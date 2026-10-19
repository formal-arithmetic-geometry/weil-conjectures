/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections
import all Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

/-! # Detecting isomorphisms on the pro-etale site

Source: Stacks Project, Tags 0991, 0993, 0GLZ and 0F6D
(blueprint: lem-cbc-proetale-stalk-conservative).

Restriction is expressed on the slice site, canonically equivalent to the small site
of the covering object. All section tests below apply to cohomology sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Exactness of restriction on the coefficient ringed site, including its additivity.
Source: Stacks, Tags 0991 and 03DA (blueprint: lem-cbc-proetale-stalk-conservative).
Proof: restrictions precompose sectionwise linear maps. Kernels and finite products
are sectionwise. Cokernels are sheafified sectionwise cokernels; covers of an object
in the slice are precisely its covers in the original site. Sheafification therefore
commutes with restriction, giving preservation of cokernels and finite sums. -/
theorem finiteCoefficientSliceRestriction_exact (U : T.ProEt) :
    (SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T Λ) U).Additive ∧
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T Λ) U) ∧
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T Λ) U) := by
  let R := finiteCoefficientRingSheaf T Λ
  let F := SheafOfModules.overFunctor.{u + 1} R U
  have hF : F.Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  have hcolim : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (SheafOfModules.pushforward.{u + 1} (𝟙 (R.over U)))
    infer_instance
  have hlim : PreservesFiniteLimits F := by
    let G := SheafOfModules.forget.{u + 1} (R.over U) ⋙
      PresheafOfModules.toPresheaf (R.over U).obj
    have h : PreservesFiniteLimits (F ⋙ G) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (Over.forget U).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves F G
  exact ⟨hF, hlim, hcolim⟩

/-- Additivity of slice restriction. Source: Stacks, Tag 03DA
(blueprint: lem-cbc-proetale-stalk-conservative). -/
noncomputable instance finiteCoefficientSliceRestriction_additive (U : T.ProEt) :
    (SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T Λ) U).Additive :=
  (finiteCoefficientSliceRestriction_exact T Λ U).1

/-- Left exactness of slice restriction. Source: Stacks, Tag 03DA
(blueprint: lem-cbc-proetale-stalk-conservative). -/
noncomputable instance finiteCoefficientSliceRestriction_limits (U : T.ProEt) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T Λ) U) :=
  (finiteCoefficientSliceRestriction_exact T Λ U).2.1

/-- Right exactness of slice restriction. Source: Stacks, Tag 03DA
(blueprint: lem-cbc-proetale-stalk-conservative). -/
noncomputable instance finiteCoefficientSliceRestriction_colimits (U : T.ProEt) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T Λ) U) :=
  (finiteCoefficientSliceRestriction_exact T Λ U).2.2

/-- The standard localization on the slice, at the same morphism universe.
Source: the blueprint size convention (blueprint: lem-cbc-proetale-stalk-conservative). -/
noncomputable instance finiteCoefficientSlice_hasDerivedCategory (U : T.ProEt) :
    HasDerivedCategory.{u + 2}
      (SheafOfModules.{u + 1} ((finiteCoefficientRingSheaf T Λ).over U)) :=
  HasDerivedCategory.standard _

private theorem finiteCoefficient_cover_iso {ι : Type v} (U : ι → T.ProEt)
    (hU : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.proetalePrecoverage T)
    {H K : FiniteCoefficientModules T Λ} (f : H ⟶ K) :
    IsIso f ↔ ∀ i, IsIso
      ((SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T Λ) (U i)).map f) := by
  let R := finiteCoefficientRingSheaf T Λ
  constructor
  · intro hf i
    infer_instance
  · intro hf
    have hs : IsIso ((SheafOfModules.toSheaf R).map f) := by
      apply isIso_of_isIso_localizationRestriction AddCommGrpCat.{u + 1} _
        (fun i ↦ (U i).hom) hU
      intro i
      rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
      rw [NatTrans.isIso_iff_isIso_app]
      intro W
      let V : Over (U i) := Over.mk
        (MorphismProperty.Over.homMk W.unop.hom rfl :
          Scheme.ProEt.mk (W.unop.hom ≫ (U i).hom) ⟶ U i)
      have := hf i
      have hi := (SheafOfModules.evaluation (R.over (U i)) (op V)).map_isIso
        ((SheafOfModules.overFunctor.{u + 1} R (U i)).map f)
      change IsIso (((SheafOfModules.overFunctor.{u + 1} R (U i)).map f).val.app
        (op V)) at hi
      exact (forget₂ (ModuleCat _) AddCommGrpCat).map_isIso
        (((SheafOfModules.overFunctor.{u + 1} R (U i)).map f).val.app (op V))
    exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

/-- Clause (1): inverse images along a single covering family detect derived
isomorphisms and vanishing of sheaves; acyclicity means vanishing of every cohomology.
The slice presentation is the usual restriction to each covering scheme.
Source: Stacks, Tag 0991 (blueprint: lem-cbc-proetale-stalk-conservative).
Proof: base change the cover to every site object V. The sheaf equalizer embeds H(V)
into the product of the restricted sections, so zero restrictions imply H=0.
This includes the empty cover of the empty scheme. Restriction is exact by the
preceding lemma and commutes with cohomology. Apply the unbounded derived
isomorphism criterion to the kernels and cokernels of every cohomology map.
A complex is acyclic exactly when its image in the derived category is zero,
equivalently all its cohomology sheaves are zero. -/
theorem finiteCoefficient_cover_detection {ι : Type v} (U : ι → T.ProEt)
    (hU : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.proetalePrecoverage T) :
    (∀ (F G : FiniteCoefficientDerivedCategory T Λ) (f : F ⟶ G),
      IsIso f ↔ ∀ i : ι,
        IsIso ((SheafOfModules.overFunctor.{u + 1}
          (finiteCoefficientRingSheaf T Λ) (U i)).mapDerivedCategory.map f)) ∧
    (∀ K : CochainComplex (FiniteCoefficientModules T Λ) ℤ,
      K.Acyclic ↔ ∀ n : ℤ, IsZero (K.homology n)) ∧
    (∀ H : FiniteCoefficientModules T Λ,
      IsZero H ↔ ∀ i : ι,
        IsZero ((SheafOfModules.overFunctor.{u + 1}
          (finiteCoefficientRingSheaf T Λ) (U i)).obj H)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F G f
    constructor
    · intro hf i
      infer_instance
    · intro hf
      rw [DerivedCategory.isIso_iff]
      intro n
      apply (finiteCoefficient_cover_iso T Λ U hU _).mpr
      intro i
      let R := SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T Λ) (U i)
      have := hf i
      have hi := (DerivedCategory.homologyFunctor _ n).map_isIso
        (R.mapDerivedCategory.map f)
      exact (NatIso.isIso_map_iff (R.mapDerivedCategoryHomologyFunctorIso n) f).mpr hi
  · intro K
    simp only [HomologicalComplex.Acyclic, HomologicalComplex.exactAt_iff_isZero_homology]
  · intro H
    constructor
    · intro h i
      exact (SheafOfModules.overFunctor.{u + 1}
        (finiteCoefficientRingSheaf T Λ) (U i)).map_isZero h
    · intro h
      have hi : IsIso (0 : H ⟶ H) := (finiteCoefficient_cover_iso T Λ U hU _).mpr (by
        intro i
        exact (h i).isIso (h i) _)
      exact IsZero.of_mono_zero H H


private theorem finiteCoefficient_iso_basis
    {H K : FiniteCoefficientModules T Λ} (f : H ⟶ K) :
    IsIso f ↔ ∀ W : T.AffineProEt,
      IsIso (f.val.app (op ((Scheme.AffineProEt.toProEt T).obj W))) := by
  let R := finiteCoefficientRingSheaf T Λ
  let E := (Scheme.AffineProEt.toProEt T).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (Scheme.AffineProEt.topology T) (Scheme.ProEt.topology T)
  constructor
  · intro hf W
    exact (SheafOfModules.evaluation R
      (op ((Scheme.AffineProEt.toProEt T).obj W))).map_isIso f
  · intro hf
    have hcomp : ∀ W : T.AffineProEtᵒᵖ,
        IsIso ((E.map ((SheafOfModules.toSheaf R).map f)).hom.app W) := by
      intro W
      have := hf W.unop
      exact (forget₂ (ModuleCat _) AddCommGrpCat).map_isIso
        (f.val.app (op ((Scheme.AffineProEt.toProEt T).obj W.unop)))
    have hiso : IsIso (E.map ((SheafOfModules.toSheaf R).map f)).hom :=
      NatIso.isIso_of_isIso_app _
    have hiso' : IsIso ((sheafToPresheaf (Scheme.AffineProEt.topology T)
        AddCommGrpCat.{u + 1}).map (E.map ((SheafOfModules.toSheaf R).map f))) := hiso
    have : IsIso (E.map ((SheafOfModules.toSheaf R).map f)) :=
      isIso_of_reflects_iso _ (sheafToPresheaf _ _)
    have : IsIso ((SheafOfModules.toSheaf R).map f) := isIso_of_reflects_iso _ E
    exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

/-- Clause (2), affine case: evaluate cohomology sheaves on the ind-etale basis.
Source: Stacks, Tag 0991 and the blueprint Step 2
(blueprint: lem-cbc-proetale-stalk-conservative).
Proof: restriction to the dense affine ind-etale subsite is an equivalence of sheaf
categories. It detects zero objects and isomorphisms; a natural transformation is
invertible exactly when each component is. Apply this to every cohomology sheaf
and use the unbounded derived isomorphism criterion. Evaluation of the original
complex is not used. -/
theorem finiteCoefficient_affine_basis_detection [IsAffine T] :
    (∀ H : FiniteCoefficientModules T Λ,
      IsZero H ↔ ∀ W : T.AffineProEt,
        Subsingleton (H.val.obj (op ((Scheme.AffineProEt.toProEt T).obj W)))) ∧
    (∀ (F G : FiniteCoefficientDerivedCategory T Λ) (f : F ⟶ G),
      IsIso f ↔ ∀ (n : ℤ) (W : T.AffineProEt),
        IsIso (((DerivedCategory.homologyFunctor (FiniteCoefficientModules T Λ) n).map f).val.app
          (op ((Scheme.AffineProEt.toProEt T).obj W)))) := by
  constructor
  · intro H
    constructor
    · intro h W
      exact ModuleCat.subsingleton_of_isZero
        ((SheafOfModules.evaluation (finiteCoefficientRingSheaf T Λ)
          (op ((Scheme.AffineProEt.toProEt T).obj W))).map_isZero h)
    · intro h
      have hi : IsIso (0 : H ⟶ H) := (finiteCoefficient_iso_basis T Λ _).mpr (by
        intro W
        have := h W
        exact (ModuleCat.isZero_of_subsingleton _).isIso
          (ModuleCat.isZero_of_subsingleton _) _)
      exact IsZero.of_mono_zero H H
  · intro F G f
    rw [DerivedCategory.isIso_iff]
    simp only [finiteCoefficient_iso_basis T Λ]


private theorem finiteCoefficient_iso_open_basis {ι : Type v}
    (V : ι → Scheme.{u}) [∀ i : ι, IsAffine (V i)] (g : ∀ i : ι, V i ⟶ T)
    [∀ i : ι, IsOpenImmersion (g i)]
    (hg : ∀ t : T, ∃ (i : ι) (x : V i), g i x = t)
    {H K : FiniteCoefficientModules T Λ} (f : H ⟶ K) :
    IsIso f ↔ ∀ (i : ι) (W : (V i).AffineProEt),
      IsIso (f.val.app (op (Scheme.ProEt.mk
        (((Scheme.AffineProEt.toProEt (V i)).obj W).hom ≫ g i)))) := by
  let R := finiteCoefficientRingSheaf T Λ
  constructor
  · intro hf i W
    exact (SheafOfModules.evaluation R _).map_isIso f
  · intro hf
    have hcover : Presieve.ofArrows V g ∈ Scheme.proetalePrecoverage T := by
      apply Scheme.zariskiPrecoverage_le_proetalePrecoverage
      exact (Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨fun t ↦ by obtain ⟨i, x, hx⟩ := hg t; exact ⟨i, x, hx⟩, fun i ↦ inferInstance⟩
    have hs : IsIso ((SheafOfModules.toSheaf R).map f) := by
      apply isIso_of_isIso_localizationRestriction AddCommGrpCat.{u + 1} _ g hcover
      intro i
      let E := (Scheme.AffineProEt.toProEt (V i)).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (Scheme.AffineProEt.topology (V i))
          (Scheme.ProEt.topology (V i))
      rw [← isIso_iff_of_reflects_iso _ E]
      rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
      rw [NatTrans.isIso_iff_isIso_app]
      intro W
      have := hf i W.unop
      exact (forget₂ (ModuleCat _) AddCommGrpCat).map_isIso
        (f.val.app (op (Scheme.ProEt.mk
          (((Scheme.AffineProEt.toProEt (V i)).obj W.unop).hom ≫ g i))))
    exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

/-- Clause (2), general case: apply the affine basis test over an affine open cover.
Source: the blueprint Step 2 (blueprint: lem-cbc-proetale-stalk-conservative).
Proof: the members of an affine open cover form a pro-etale cover. Apply clause (1),
then the affine basis criterion to each restriction. Its sections are the original
sections over the composite weakly etale object. This works for an empty cover too. -/
theorem finiteCoefficient_affine_open_basis_detection {ι : Type v}
    (V : ι → Scheme.{u}) [∀ i : ι, IsAffine (V i)] (g : ∀ i : ι, V i ⟶ T)
    [∀ i : ι, IsOpenImmersion (g i)]
    (hg : ∀ t : T, ∃ (i : ι) (x : V i), g i x = t) :
    (∀ H : FiniteCoefficientModules T Λ,
      IsZero H ↔ ∀ (i : ι) (W : (V i).AffineProEt),
        Subsingleton (H.val.obj (op (Scheme.ProEt.mk
          (((Scheme.AffineProEt.toProEt (V i)).obj W).hom ≫ g i))))) ∧
    (∀ (F G : FiniteCoefficientDerivedCategory T Λ) (f : F ⟶ G),
      IsIso f ↔ ∀ (n : ℤ) (i : ι) (W : (V i).AffineProEt),
        IsIso (((DerivedCategory.homologyFunctor (FiniteCoefficientModules T Λ) n).map f).val.app
          (op (Scheme.ProEt.mk
          (((Scheme.AffineProEt.toProEt (V i)).obj W).hom ≫ g i))))) := by
  constructor
  · intro H
    constructor
    · intro h i W
      exact ModuleCat.subsingleton_of_isZero
        ((SheafOfModules.evaluation (finiteCoefficientRingSheaf T Λ) _).map_isZero h)
    · intro h
      have hi : IsIso (0 : H ⟶ H) :=
        (finiteCoefficient_iso_open_basis T Λ V g hg _).mpr (by
          intro i W
          have := h i W
          exact (ModuleCat.isZero_of_subsingleton _).isIso
            (ModuleCat.isZero_of_subsingleton _) _)
      exact IsZero.of_mono_zero H H
  · intro F G f
    rw [DerivedCategory.isIso_iff]
    simp only [finiteCoefficient_iso_open_basis T Λ V g hg]


/-- Cohomology followed by the recorded pointed-neighbourhood colimit. Forgetting
scalars detects invertibility, also for noncommutative finite rings.
Source: Stacks, Tags 0991 and 0F6B (blueprint: lem-cbc-proetale-stalk-conservative). -/
noncomputable def finiteCoefficientCohomologyStalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (n : ℤ) :
    FiniteCoefficientDerivedCategory T Λ ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.homologyFunctor (FiniteCoefficientModules T Λ) n ⋙
    SheafOfModules.toSheaf (finiteCoefficientRingSheaf T Λ) ⋙
    sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
      AddCommGrpCat.{u + 1}).obj (Scheme.proEtaleGeometricNeighbourhoodForget t).op ⋙ colim

private noncomputable def coefficientRealizationToSheafIso :
    finiteCoefficientRealization T Λ ⋙ SheafOfModules.toSheaf
      (finiteCoefficientRingSheaf T Λ) ≅
    sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
  exact Functor.isoWhiskerLeft
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (asIso (sheafificationAdjunction (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).counit)

private noncomputable def coefficientStalkComparisonIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    finiteCoefficientComparison T Λ ⋙ SheafOfModules.toSheaf
      (finiteCoefficientRingSheaf T Λ) ⋙
      sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
        AddCommGrpCat.{u + 1}).obj (Scheme.proEtaleGeometricNeighbourhoodForget t).op ⋙
      colim ≅ (Scheme.pointSmallEtale t).sheafFiber ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} := by
  let S := sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
      AddCommGrpCat.{u + 1}).obj (Scheme.proEtaleGeometricNeighbourhoodForget t).op ⋙ colim
  let M := sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) ⋙
    (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
      (ModuleCat.{u + 1} Λ)).obj (Scheme.proEtaleGeometricNeighbourhoodForget t).op
  let Q := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let e : sheafCompose (Scheme.ProEt.topology T) Q ⋙ S ≅ M ⋙ colim ⋙ Q :=
    Functor.isoWhiskerLeft M (preservesColimitNatIso Q).symm
  let c := Classical.choose ((Scheme.proEtale_comparison_stalk T Ω t).2.2 Λ)
  exact Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
      (Functor.isoWhiskerRight (coefficientRealizationToSheafIso T Λ) S ≪≫ e) ≪≫
    Functor.isoWhiskerRight c Q

private theorem isIso_of_coefficientComparison_stalks
    {F G : FiniteCoefficientEtaleDerivedCategory T Λ} (f : F ⟶ G)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) (n : ℤ),
      IsIso ((finiteCoefficientCohomologyStalk T Λ Ω t n).map
        ((finiteCoefficientDerivedComparison T Λ).map f))) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  apply Scheme.isIso_of_isIso_sheafFiber_map
  intro x
  let t := T.algClosurePoint x
  let Q := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let S := SheafOfModules.toSheaf (finiteCoefficientRingSheaf T Λ) ⋙
    sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
      AddCommGrpCat.{u + 1}).obj (Scheme.proEtaleGeometricNeighbourhoodForget t).op ⋙ colim
  let Hn := DerivedCategory.homologyFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n
  have h1 : IsIso ((Hn ⋙ finiteCoefficientComparison T Λ ⋙ S).map f) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      ((finiteCoefficientComparison T Λ).mapDerivedCategoryHomologyFunctorIso n) S) f).mpr
        (h _ t n)
  have h2 : IsIso (((Scheme.pointSmallEtale t).sheafFiber ⋙ Q).map (Hn.map f)) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerLeft Hn
      (coefficientStalkComparisonIso T Λ _ t)) f).mp h1
  change IsIso (Q.map ((Scheme.pointSmallEtale t).sheafFiber.map (Hn.map f))) at h2
  have h3 : IsIso ((Scheme.pointSmallEtale t).sheafFiber.map (Hn.map f)) :=
    isIso_of_reflects_iso _ Q
  exact (NatIso.isIso_map_iff
    ((Scheme.pointSmallEtale t).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ))
      (Hn.map f)).mpr h3

set_option linter.unusedVariables false in
/-- Clause (3): geometric stalk detection on etale-origin bounded below complexes,
and on every morphism between bounded constructible objects of etale origin.
Source: Stacks, Tags 0991, 0993 and 0GLZ
(blueprint: lem-cbc-proetale-stalk-conservative).
Proof: exactness of comparison identifies its cohomology with the comparison of
cohomology. The canonical comparison-stalk isomorphism identifies these stalk maps
with etale stalk maps, naturally in the morphism. Etale stalks are conservative,
so every original cohomology map is invertible, hence the derived map is invertible.
The converse follows by functoriality. For arbitrary morphisms between Dbc objects,
choose their etale-origin presentations and use full faithfulness of bounded below
comparison to lift the conjugated morphism; apply the preceding criterion and
conjugate back. No geometric-stalk detection on arbitrary pro-etale sheaves is used. -/
theorem finiteCoefficient_etale_origin_stalk_detection :
    (∀ (F G : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (f : F ⟶ G),
      IsIso ((finiteCoefficientDerivedComparison T Λ).map
        ((DerivedCategory.Plus.ι).map f)) ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) (n : ℤ),
        IsIso ((finiteCoefficientCohomologyStalk T Λ Ω t n).map
          ((finiteCoefficientDerivedComparison T Λ).map ((DerivedCategory.Plus.ι).map f)))) ∧
    (∀ (F G : FiniteCoefficientDerivedCategory T Λ)
      (hF : isBoundedConstructibleFiniteCoefficient T Λ F)
      (hG : isBoundedConstructibleFiniteCoefficient T Λ G) (f : F ⟶ G),
      IsIso f ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ T) (n : ℤ),
        IsIso ((finiteCoefficientCohomologyStalk T Λ Ω t n).map f)) := by
  have hfirst : ∀ (F G : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (f : F ⟶ G),
      IsIso ((finiteCoefficientDerivedComparison T Λ).map
        ((DerivedCategory.Plus.ι).map f)) ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) (n : ℤ),
        IsIso ((finiteCoefficientCohomologyStalk T Λ Ω t n).map
          ((finiteCoefficientDerivedComparison T Λ).map ((DerivedCategory.Plus.ι).map f))) := by
    intro F G f
    constructor
    · intro hf Ω _ _ t n
      infer_instance
    · intro h
      have := isIso_of_coefficientComparison_stalks T Λ ((DerivedCategory.Plus.ι).map f) h
      exact (finiteCoefficientDerivedComparison T Λ).map_isIso _
  refine ⟨hfirst, ?_⟩
  intro F G hF hG f
  constructor
  · intro hf Ω _ _ t n
    infer_instance
  · intro h
    obtain ⟨F', hF', ⟨eF⟩⟩ := hF
    obtain ⟨G', hG', ⟨eG⟩⟩ := hG
    obtain ⟨aF, bF, _, hboundF⟩ := hF'.2
    obtain ⟨aG, bG, _, hboundG⟩ := hG'.2
    let FP : DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      ⟨F', aF, (DerivedCategory.isGE_iff F' aF).mpr (fun i hi ↦ hboundF i (.inl hi))⟩
    let GP : DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      ⟨G', aG, (DerivedCategory.isGE_iff G' aG).mpr (fun i hi ↦ hboundG i (.inl hi))⟩
    let ff := Classical.choice (siteComparison_boundedBelow T Λ).1
    have := ff.full
    have := ff.faithful
    let L := (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus ⋙
      DerivedCategory.Plus.ι
    let f' : FP ⟶ GP := L.preimage (eF.hom ≫ f ≫ eG.inv)
    have heq : L.map f' = eF.hom ≫ f ≫ eG.inv := L.map_preimage _
    have hf' : IsIso (L.map f') := (hfirst FP GP f').mpr (by
      intro Ω _ _ t n
      change IsIso ((finiteCoefficientCohomologyStalk T Λ Ω t n).map (L.map f'))
      rw [heq, Functor.map_comp, Functor.map_comp]
      have := h Ω t n
      infer_instance)
    have hfcomp : IsIso (eF.hom ≫ f ≫ eG.inv) := heq ▸ hf'
    have hfmid : IsIso (f ≫ eG.inv) := IsIso.of_isIso_comp_left eF.hom _
    exact IsIso.of_isIso_comp_right f eG.inv


end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

/-- The covering criterion also detects zero abelian sheaves on the entire pro-etale site.
Source: Stacks, Tag 0991 (blueprint: lem-cbc-proetale-stalk-conservative).
Proof: base change the cover to each object; the sheaf equalizer embeds its sections
into a product of zero groups. Conversely restriction preserves zero objects.
This is the sheaf argument of Step 1, independent of finite module coefficients. -/
theorem proEtale_abelian_cover_zero_detection (T : Scheme.{u}) {ι : Type v}
    (U : ι → T.ProEt)
    (hU : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.proetalePrecoverage T) (H : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) :
    IsZero H ↔ ∀ i : ι, IsZero
      ((AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
        (U i).hom inferInstance).obj H) := by
  constructor
  · intro h i
    let R := AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
      (U i).hom inferInstance
    have : R.Additive := by
      constructor
      intro X Y f g
      rfl
    exact R.map_isZero h
  · intro h
    have hi : IsIso (0 : H ⟶ H) := by
      apply AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction
        AddCommGrpCat.{u + 1} _ (fun i ↦ (U i).hom) hU
      intro i
      exact (h i).isIso (h i) _
    exact IsZero.of_mono_zero H H


/-- The affine basis criterion also holds for arbitrary abelian sheaves.
Source: Stacks, Tag 0991 (blueprint: lem-cbc-proetale-stalk-conservative).
Proof: restriction to the affine ind-etale basis is an equivalence of sheaf categories,
so it reflects zero objects; zero abelian sheaves have zero sections. For a general
scheme first apply the covering criterion to any affine open cover, as in Step 3. -/
theorem proEtale_abelian_affine_basis_zero_detection (T : Scheme.{u}) [IsAffine T]
    (H : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) :
    IsZero H ↔ ∀ W : T.AffineProEt,
      IsZero (H.obj.obj (op ((AffineProEt.toProEt T).obj W))) := by
  let E := (AffineProEt.toProEt T).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (AffineProEt.topology T) (ProEt.topology T)
  constructor
  · intro h W
    exact ((sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) ⋙
      (CategoryTheory.evaluation T.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op ((AffineProEt.toProEt T).obj W))).map_isZero h
  · intro h
    have hz : IsZero (E.obj H).obj := Functor.isZero _ fun W ↦ h W.unop
    have hz' : IsZero (E.obj H) :=
      IsZero.of_full_of_faithful_of_isZero
        (sheafToPresheaf (AffineProEt.topology T) AddCommGrpCat.{u + 1}) _ hz
    exact IsZero.of_full_of_faithful_of_isZero E H hz'


/-- All set maps from scheme points to A, with pointwise addition and restriction by
precomposition. Source: Stacks, Tag 0F6D (blueprint: lem-cbc-proetale-stalk-conservative). -/
noncomputable def proEtaleAllFunctionsPresheaf (T : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] : T.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := AddCommGrpCat.of (U.unop.left → A)
  map f := AddCommGrpCat.ofHom
    { toFun := fun s x ↦ s (f.unop.left x)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- Constant functions, before sheafification. Source: Stacks, Tag 0F6D
(blueprint: lem-cbc-proetale-stalk-conservative). -/
noncomputable def proEtaleConstantsToAllFunctions (T : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    (Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of A) ⟶ proEtaleAllFunctionsPresheaf T A where
  app U := AddCommGrpCat.ofHom
    { toFun := fun a _ ↦ a
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The actual sheafified quotient of all functions by the constant abelian sheaf.
Source: Stacks, Tags 0991 and 0F6D (blueprint: lem-cbc-proetale-stalk-conservative). -/
noncomputable def proEtaleFunctionsQuotient (T : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  cokernel ((presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).map
    (proEtaleConstantsToAllFunctions T A))

set_option linter.unnecessarySeqFocus false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def functionsQuotientIso (T : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A]
    (F : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1})
    (e : ∀ V : T.ProEt, F.obj.obj (op V) ≃+ (V.left → A))
    (he : ∀ (U V : T.ProEt) (f : U ⟶ V) (s : F.obj.obj (op V)) (x : U.left),
      e U (F.obj.map f.op s) x = e V s (f.left x))
    (i : (constantSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of A) ⟶ F)
    (hi : ∀ (V : T.ProEt) (a : A) (x : V.left),
      e V (i.hom.app (op V)
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app (op V) a)) x = a) :
    proEtaleFunctionsQuotient T A ≅ cokernel i := by
  let L := presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}
  let a : proEtaleAllFunctionsPresheaf T A ≅ F.obj :=
    NatIso.ofComponents (fun V ↦ (e V.unop).symm.toAddCommGrpIso) (by
      intro U V f
      ext s
      apply (e V.unop).injective
      funext y
      change e V.unop ((e V.unop).symm (fun x ↦ s (f.unop.left x))) y = _
      rw [AddEquiv.apply_symm_apply]
      convert (he V.unop U.unop f.unop ((e U.unop).symm s) y).symm using 1 <;>
        simp [AddEquiv.toAddCommGrpIso, AddCommGrpCat.Hom.hom] <;> rfl)
  let b : L.obj (proEtaleAllFunctionsPresheaf T A) ≅ F :=
    L.mapIso a ≪≫ asIso ((sheafificationAdjunction _ _).counit.app F)
  have hb : toSheafify (ProEt.topology T) (proEtaleAllFunctionsPresheaf T A) ≫
      b.hom.hom = a.hom := by
    change toSheafify _ _ ≫ (L.map a.hom).hom ≫
      ((sheafificationAdjunction _ _).counit.app F).hom = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
    simp [sheafificationAdjunction_counit_app_val]
  have h : L.map (proEtaleConstantsToAllFunctions T A) ≫ b.hom = i := by
    apply (sheafificationAdjunction _ _).homEquiv _ _ |>.injective
    simp only [Adjunction.homEquiv_unit]
    change toSheafify _ _ ≫ (L.map (proEtaleConstantsToAllFunctions T A)).hom ≫
      b.hom.hom = toSheafify _ _ ≫ i.hom
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, hb]
    ext V s
    apply (e V.unop).injective
    funext y
    convert (hi V.unop s y).symm using 1 <;>
      simp only [op_unop, Functor.const_obj_obj, NatTrans.comp_app, AddCommGrpCat.hom_comp,
        AddMonoidHom.coe_comp, Function.comp_apply] <;>
      first | rfl | exact congrFun ((e V.unop).apply_symm_apply _) y
  exact cokernel.mapIso _ i (Iso.refl _) b (by simpa using h)

private theorem field_stalk_zero (k : Type u) [Field k] [IsAlgClosed k]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of k))
    (H : Sheaf (ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (hH : IsZero (H.obj.obj (op (ProEt.mk (𝟙 (Spec (.of k))))))) :
    IsZero (proEtaleGeometricStalk t H) := by
  have : IsSepClosed (IsLocalRing.ResidueField k) := IsSepClosed.of_ringEquiv
    (RingEquiv.ofBijective (IsLocalRing.residue k)
      ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩)
  let : IsStrictlyHenselianLocalRing k :=
    (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed k).mpr
      ⟨inferInstance, inferInstance⟩
  let N : ProEtaleGeometricNeighbourhood t :=
    StructuredArrow.mk (Y := ProEt.mk (𝟙 (Spec (.of k))))
      (Over.homMk t (Category.comp_id t))
  have hN : IsInitial N := classicalStalk_initial (R := k) t (𝟙 _) t
    (Category.comp_id t) (Subsingleton.elim _ _)
  have hi : IsIso (colimit.ι (proEtaleGeometricStalkDiagram t H) (op N)) :=
    (colimit.isColimit _).isIso_ι_app_of_isTerminal _ hN.op
  exact hH.of_iso (asIso (colimit.ι (proEtaleGeometricStalkDiagram t H) (op N))).symm

/-- Clause (4): the specified quotient has zero geometric stalks and zero sections
on Spec k, but is nonzero; on affine objects its sections are all functions modulo
locally constant functions. Source: Stacks, Tags 0991 and 0F6D
(blueprint: lem-cbc-proetale-stalk-conservative).
Proof: the functions-quotient-sections lemma supplies a sheaf of all functions with
canonical constant inclusion. The section identifications give a presheaf isomorphism;
the sheafification counit and its triangle identity identify the constructed cokernel
with that lemma's cokernel. This gives the affine formula. All functions on Spec k
are constant, so its quotient sections vanish. The identity pointed neighbourhood
is initial by the proved pointed-lifting and rigidity construction of the classical
stalk lemma, applied directly to the strictly henselian field k. Its colimit leg is
an isomorphism, so all geometric stalks vanish, including points over larger fields.
For nonvanishing let E be the one-point compactification of the discrete natural
numbers and B = LocallyConstant E k. The proved weaklyEtale instance makes Spec B
a pro-etale object, and homeomorphPrimeSpectrum identifies its points with E.
A function supported at infinity with a nonzero value is not locally constant:
its zero fibre would be closed and contain the dense natural numbers, hence infinity.
Its affine quotient class is therefore nonzero. -/
theorem proEtaleFunctionsQuotient_counterexample (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [AddCommGroup A] [Nontrivial A] :
    (∀ (U : (Spec (.of k)).ProEt) [IsAffine U.left],
      Nonempty (((U.left → A) ⧸
        (LocallyConstant.coeFnAddMonoidHom : LocallyConstant U.left A →+
          (U.left → A)).range) ≃+
        (proEtaleFunctionsQuotient (Spec (.of k)) A).obj.obj (op U))) ∧
    Subsingleton ((proEtaleFunctionsQuotient (Spec (.of k)) A).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of k)),
      IsZero (proEtaleGeometricStalk t (proEtaleFunctionsQuotient (Spec (.of k)) A))) ∧
    ¬ IsZero (proEtaleFunctionsQuotient (Spec (.of k)) A) := by
  classical
  let T := Spec (.of k)
  let Q := proEtaleFunctionsQuotient T A
  obtain ⟨F, e, he, i, _, hi, _, _, hq⟩ :=
    exists_proEtale_functions_quotient_sections T A
  let c : Q ≅ cokernel i := functionsQuotientIso T A F e he i hi
  have hsep (x : T) : IsSepClosed (T.residueField x) := by
    exact IsSepClosed.of_ringEquiv
      ((Ideal.algEquivResidueFieldOfField x.asIdeal).toRingEquiv.trans
        (Spec.residueFieldIso (.of k) x).symm.commRingCatIsoToRingEquiv)
  have hq' (U : T.ProEt) [IsAffine U.left] :
      Nonempty (((U.left → A) ⧸
        (LocallyConstant.coeFnAddMonoidHom : LocallyConstant U.left A →+
          (U.left → A)).range) ≃+ Q.obj.obj (op U)) := by
    obtain ⟨q, _⟩ := hq (fun _ ↦ isClosed_singleton) hsep U inferInstance
    exact ⟨q.trans ((((sheafToPresheaf _ _) ⋙
      (CategoryTheory.evaluation _ _).obj (op U)).mapIso c.symm).addCommGroupIsoToAddEquiv)⟩
  have hz : Subsingleton (Q.obj.obj (op (ProEt.mk (𝟙 T)))) := by
    let U : T.ProEt := ProEt.mk (𝟙 T)
    have : IsAffine U.left := by change IsAffine (Spec (.of k)); infer_instance
    have : Subsingleton U.left := by change Subsingleton (Spec (.of k)); infer_instance
    have : Inhabited U.left := by change Inhabited (Spec (.of k)); infer_instance
    let q := Classical.choice (hq' U)
    suffices hsub : Subsingleton ((U.left → A) ⧸
        (LocallyConstant.coeFnAddMonoidHom : LocallyConstant U.left A →+
          (U.left → A)).range) by
      let := hsub
      exact q.symm.injective.subsingleton
    have hall (f : U.left → A) :
        f ∈ (LocallyConstant.coeFnAddMonoidHom : LocallyConstant U.left A →+
          (U.left → A)).range := by
      have hc : f = fun _ ↦ f (default : T) :=
        funext (fun x ↦ congrArg f (Subsingleton.elim x (default : T)))
      exact ⟨⟨f, by rw [hc]; exact IsLocallyConstant.const _⟩, rfl⟩
    have htriv (x : (U.left → A) ⧸
        (LocallyConstant.coeFnAddMonoidHom : LocallyConstant U.left A →+
          (U.left → A)).range) : x = 0 := by
      induction x using Quotient.inductionOn' with
      | _ f => exact (QuotientAddGroup.eq_zero_iff f).mpr (hall f)
    exact ⟨fun x y ↦ (htriv x).trans (htriv y).symm⟩
  refine ⟨hq', hz, ?_, ?_⟩
  · intro Ω _ _ t
    exact field_stalk_zero k Ω t Q (AddCommGrpCat.isZero_of_subsingleton _)
  · let : NoncompactSpace (ULift.{u} ℕ) :=
      not_compactSpace_iff.mp (fun h ↦ by
        have := h
        exact Set.infinite_univ (isCompact_univ : IsCompact
          (Set.univ : Set (ULift.{u} ℕ))).finite_of_discrete)
    let S := OnePoint (ULift.{u} ℕ)
    let B := LocallyConstant S k
    let U : T.ProEt := ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap k B)))
    have : IsAffine U.left := by
      change IsAffine (Spec (.of B))
      infer_instance
    let E : S × PrimeSpectrum k ≃ₜ U.left := LocallyConstant.homeomorphPrimeSpectrum
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    let f : U.left → A := fun x ↦ if (E.symm x).1 = OnePoint.infty then a else 0
    have hf : ¬ IsLocallyConstant f := by
      intro hf
      let g : S → A := fun s ↦ f (E (s, default))
      have hg : IsLocallyConstant g := hf.comp_continuous
        (E.continuous.comp (continuous_id.prodMk continuous_const))
      have hsub : Set.range (OnePoint.some : ULift.{u} ℕ → S) ⊆ {s | g s = 0} := by
        rintro _ ⟨n, rfl⟩
        change (if (E.symm (E (OnePoint.some n, default))).1 = OnePoint.infty then a else 0) = 0
        rw [E.symm_apply_apply]
        exact if_neg (OnePoint.coe_ne_infty n)
      have hh := closure_minimal hsub (hg.isClosed_fiber 0)
      have hinf : (OnePoint.infty : S) ∈ closure (Set.range (OnePoint.some : ULift.{u} ℕ → S)) :=
        OnePoint.denseRange_coe _
      have hzero := hh hinf
      exact ha (by simpa [g, f] using hzero)
    intro hzero
    let q := Classical.choice (hq' U)
    have hU : IsZero (Q.obj.obj (op U)) :=
      ((sheafToPresheaf _ _) ⋙ (CategoryTheory.evaluation _ _).obj (op U)).map_isZero hzero
    have : Subsingleton (Q.obj.obj (op U)) := AddCommGrpCat.subsingleton_of_isZero hU
    have heq : q (QuotientAddGroup.mk f) = q 0 := Subsingleton.elim _ _
    have hmem : f ∈ (LocallyConstant.coeFnAddMonoidHom : LocallyConstant U.left A →+
        (U.left → A)).range := (QuotientAddGroup.eq_zero_iff f).mp (q.injective heq)
    obtain ⟨g, hg⟩ := hmem
    exact hf (hg ▸ g.isLocallyConstant)

end AlgebraicGeometry.Scheme
