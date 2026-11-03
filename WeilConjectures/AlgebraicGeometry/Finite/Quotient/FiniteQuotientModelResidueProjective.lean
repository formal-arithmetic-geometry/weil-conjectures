/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive

import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelResidueComparison
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantSliceIsoReflects
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteModelDerivedScalarComparison
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # The algebraic residue of a finite-quotient constant model

Source: Stacks Project, sites-cohomology.tex, lemma-bounded (094I)
(blueprint: lem-weil-pbc-finite-quotient-model-residue-projective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem constantMap_comp (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    adicConstantMap X f ≫ adicConstantMap X g = adicConstantMap X (g.comp f) := by
  unfold adicConstantMap
  rw [← Functor.map_comp]
  rfl

private noncomputable abbrev reductionModuleRing (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

private noncomputable abbrev reductionModules (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  ringedSiteModules.{t + 1} (reductionModuleRing T R)

private noncomputable instance reductionModulesHasDerivedCategory (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    HasDerivedCategory (reductionModules T R) := HasDerivedCategory.standard _

private noncomputable abbrev reductionDerivedCategory (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  DerivedCategory (reductionModules T R)

private def reductionChangeSpec (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionModules T R ⥤ reductionModules T S) → Prop :=
  (fun {B : Type (t + 2)} {P : B → Prop} (_ : ∃ x, P x) ↦ P)
    (completedAdicChangeData T φ)

private theorem reductionChangeExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ E, reductionChangeSpec T φ E := completedAdicChangeData T φ

private noncomputable def reductionChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionModules T R ⥤ reductionModules T S := completedAdicChange T φ

private noncomputable instance reductionChangeAdditive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionChange T φ).Additive :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose

private def reductionDerivedSpec (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (LF : reductionDerivedCategory T R ⥤ reductionDerivedCategory T S) : Prop :=
    ∃ (ε : DerivedCategory.Qh ⋙ LF ⟶
        (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (reductionModules T R) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (reductionModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

private theorem reductionDerivedExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ LF, reductionDerivedSpec T φ LF :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2

private noncomputable def reductionDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionDerivedCategory T R ⥤ reductionDerivedCategory T S :=
  completedAdicDerivedChange T φ

private noncomputable def reductionDerivedCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    DerivedCategory.Qh ⋙ reductionDerivedChange T φ ⟶
      (reductionChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (reductionDerivedExistence T φ).choose_spec.choose

/-- The universal ordinary and derived scalar-extension witness on the slice.
Its object and map equations determine ordinary tensor extension, while its
counit determines the derived functor.  Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
private def completedAdicSliceChangeData (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U)))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (S.over U)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f)

/-- Ordinary scalar extension along the coefficient map restricted to the slice.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
private def completedAdicSliceChange (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (completedAdicSliceChangeData X U f).choose

/-- The chosen slice scalar-extension witness is additive.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
private instance completedAdicSliceChange_additive (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    (completedAdicSliceChange X U f).Additive :=
  (completedAdicSliceChangeData X U f).choose_spec.choose_spec.choose_spec.choose

/-- The total left derived scalar-extension functor on the slice.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
private def completedAdicSliceDerivedChange (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (completedAdicSliceChangeData X U f).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

/-- Ordinary scalar extension commutes with restriction to the pro-etale slice.
The proof is the presheaf tensor comparison followed by the sheafification
universal property.  This is the ordinary (underived) step in the derived
comparison theorem.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison-underived).
-/
private theorem completedAdic_slice_scalarComparison_underived (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty
      ((SheafOfModules.overFunctor
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U ⋙
          completedAdicSliceChange X U f) ≅
        (completedAdicChange X f ⋙ SheafOfModules.overFunctor
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U)) := by
  let O_S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
  let A := PresheafOfModules.sheafification (R := O_S) (𝟙 _)
  let AU := PresheafOfModules.sheafification (R := O_S.over U) (𝟙 _)
  let n := scalarNormalizationIso f (completedAdicChange X f)
    (globalChangeObj X f) (fun a ↦ globalChangeMap X f a)
  let nU := scalarNormalizationIso (sliceCoefficientMap X U f)
    (completedAdicSliceChange X U f)
    (sliceChangeObj X U f) (fun a ↦ sliceChangeMap X U f a)
  have hI (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
      IsIso (overSheafificationMap O_S U
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} f M)) :=
    overSheafificationMap_isIso O_S U _
  refine ⟨isoWhiskerLeft _ nU ≪≫ ?_ ≪≫
    isoWhiskerRight n.symm (SheafOfModules.overFunctor O_S U)⟩
  refine NatIso.ofComponents (fun M ↦
    AU.mapIso (scalarOverPresheafIso X U f M) ≪≫
      asIso (overSheafificationMap O_S U
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} f M))) ?_
  intro M N a
  have hp : scalarPresheafMap (sliceCoefficientMap X U f) (a.over U) ≫
        (scalarOverPresheafIso X U f N).hom =
      (scalarOverPresheafIso X U f M).hom ≫
        (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
          (scalarPresheafMap f a) := by
    ext V x
    rfl
  change AU.map (scalarPresheafMap (sliceCoefficientMap X U f) (a.over U)) ≫
      (AU.map (scalarOverPresheafIso X U f N).hom ≫ overSheafificationMap O_S U _) =
    (AU.map (scalarOverPresheafIso X U f M).hom ≫ overSheafificationMap O_S U _) ≫
      (A.map (scalarPresheafMap f a)).over U
  rw [← Category.assoc, ← AU.map_comp, hp, AU.map_comp, Category.assoc]
  calc
    _ = AU.map (scalarOverPresheafIso X U f M).hom ≫
        (overSheafificationMap O_S U _ ≫ (A.map (scalarPresheafMap f a)).over U) :=
      congrArg (fun k ↦ AU.map (scalarOverPresheafIso X U f M).hom ≫ k)
        (overSheafificationMap_naturality O_S U (scalarPresheafMap f a))
    _ = _ := (Category.assoc _ _ _).symm


-- A counit invertible on a resolving class is universal.  Compare it with
-- the existing resolving-class construction, then detect the comparison on
-- the localization images of the resolving objects.

/-- Both derived composites are left derived functors of their ordinary composites.
The composite of exact slice restriction with derived slice extension, and the
composite of derived extension with exact slice restriction, each carry a counit to
the localized ordinary composite exhibiting it as a left derived functor along the
quasi-isomorphisms.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 0D6D.
Proof: every complex of R-modules has a flat-term K-flat resolution, and slice
restriction is exact and carries K-flat complexes to K-flat complexes (pullback by
the localization morphism of ringed topoi, Tag 0G7E). The universal counits of both
derived scalar extensions are invertible on K-flat complexes and their ordinary
extensions preserve quasi-isomorphisms between K-flat complexes. Hence both ordinary
composites send quasi-isomorphisms between K-flat complexes to isomorphisms, both
derived composites are computed on K-flat representatives, and the induced counits
are isomorphisms there; a functor with this property is a left derived functor, by
the universal property of the localization restricted to K-flat complexes.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison-derived-data).
-/
private theorem completedAdic_slice_scalarComparison_derived_data (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    let O_R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let O_S := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
    let A := SheafOfModules O_R
    letI : (SheafOfModules.overFunctor O_R U).Additive := by
      exact (ringedOverFunctor_exactGeneral O_R U).1
    letI : (SheafOfModules.overFunctor O_S U).Additive := by
      exact (ringedOverFunctor_exactGeneral O_S U).1
    letI : (completedAdicChange X f).Additive := completedAdicChange_additive X f
    letI : (completedAdicSliceChange X U f).Additive :=
      completedAdicSliceChange_additive X U f
    letI : HasDerivedCategory A := HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules O_S) := HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules (O_R.over U)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules (O_S.over U)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory
        (SheafOfModules.{t + 1}
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
            ((ProEt.topology X).over U)
            (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).obj S))) :=
      HasDerivedCategory.standard _
    let Q_A := DerivedCategory.Qh (C := A)
    let F := completedAdicDerivedChange X f
    let F_U := completedAdicSliceDerivedChange X U f
    let L_U := ringedDerivedRestrictionGeneral O_R U ⋙ F_U
    let L := F ⋙ ringedDerivedRestrictionGeneral O_S U
    let G_U :=
      ((SheafOfModules.overFunctor O_R U ⋙ completedAdicSliceChange X U f).mapHomotopyCategory
        (.up ℤ)) ⋙ DerivedCategory.Qh
    let G :=
      ((completedAdicChange X f ⋙ SheafOfModules.overFunctor O_S U).mapHomotopyCategory
        (.up ℤ)) ⋙ DerivedCategory.Qh
    ∃ (α : Q_A ⋙ L_U ⟶ G_U) (α' : Q_A ⋙ L ⟶ G),
      L_U.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) ∧
      L.IsLeftDerivedFunctor α' (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  let O_R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let O_S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
  let A := SheafOfModules.{t + 1} O_R
  let B := SheafOfModules.{t + 1} O_S
  let AU := sliceModules X U R
  let BU := sliceModules X U S
  let : HasDerivedCategory A := HasDerivedCategory.standard _
  let : HasDerivedCategory B := HasDerivedCategory.standard _
  let : HasDerivedCategory AU := sliceModulesDerived X U R
  let : HasDerivedCategory BU := sliceModulesDerived X U S
  let ER := SheafOfModules.overFunctor O_R U
  let ES := SheafOfModules.overFunctor O_S U
  have : ER.Additive := (ringedOverFunctor_exactGeneral O_R U).1
  have : ES.Additive := (ringedOverFunctor_exactGeneral O_S U).1
  have : PreservesFiniteLimits ER := (ringedOverFunctor_exactGeneral O_R U).2.1
  have : PreservesFiniteColimits ER := (ringedOverFunctor_exactGeneral O_R U).2.2
  have : PreservesFiniteLimits ES := (ringedOverFunctor_exactGeneral O_S U).2.1
  have : PreservesFiniteColimits ES := (ringedOverFunctor_exactGeneral O_S U).2.2
  let E := completedAdicChange X f
  let EU := completedAdicSliceChange X U f
  have : E.Additive := completedAdicChange_additive X f
  have : EU.Additive := completedAdicSliceChange_additive X U f
  let F := completedAdicDerivedChange X f
  let FU := completedAdicSliceDerivedChange X U f
  let ε := reductionDerivedCounit X f
  let εU := sliceCounit X U f
  let P : Set (HomotopyCategory A (.up ℤ)) :=
    {K | ∃ T : CochainComplex A ℤ, T.IsKFlatIndependentCoefficients (R := R) ∧
      (HomotopyCategory.quotient A (.up ℤ)).obj T = K}
  have hres (K : HomotopyCategory A (.up ℤ)) :
      ∃ (K' : HomotopyCategory A (.up ℤ)) (s : K' ⟶ K),
        K' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨T', s, hT', _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) T
    exact ⟨_, (HomotopyCategory.quotient A (.up ℤ)).map s, ⟨T', hT', rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hε : ∀ K ∈ P, IsIso (ε.app K) := by
    intro K hK
    obtain ⟨T, hT, hK⟩ := hK
    have hi : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj T)) :=
      globalCounit_isIso X f T hT
    exact hK ▸ hi
  have hεU : ∀ K ∈ P,
      IsIso (εU.app ((ER.mapHomotopyCategory (.up ℤ)).obj K)) := by
    rintro _ ⟨T, hT, rfl⟩
    have hTU := (SheafOfModules.ringedSite_restriction_exact_kflat.{t + 1, t, t + 1}
      (ProEt.topology X) R U).2.2 T hT
    let TU : CochainComplex (sliceModules X U R) ℤ :=
      (ER.mapHomologicalComplex (.up ℤ)).obj T
    have hi := sliceCounit_isIso X U f TU hTU
    let e : (ER.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A (.up ℤ)).obj T) ≅
        (HomotopyCategory.quotient (sliceModules X U R) (.up ℤ)).obj TU :=
      ((ER.mapHomotopyCategoryFactors (.up ℤ)).app T) ≪≫ eqToIso (by rfl)
    exact (NatTrans.isIso_app_iff_of_iso εU e).2 hi
  have h := scalarDerived_composites E EU ER ES F FU ε εU P hres hε hεU
  exact h

/-- Exact slice restriction commutes with unbounded derived scalar extension.
This is a comparison of the two functors, for an arbitrary coefficient map; it
contains no adic quotient, constant model, or local-isomorphism hypothesis.

Source: Stacks Project, sites-cohomology.tex, lemma-derived-base-change (06YY),
lemma-pullback-K-flat (0G7E), and lemma-derived-pullback-composition (0D6D).
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).

Proof: choose a flat-term K-flat resolution of the input. Restriction to the slice
is the inverse image of the localization morphism of topoi and is exact. It carries
this resolution to a flat-term K-flat resolution, by pullback-K-flat. Ordinary scalar
extension commutes with slice restriction: on an object V -> U the two presheaf
tensors are the same tensor over R(V), and module sheafification commutes with
localization of the site. Consequently these identifications commute with all
restriction maps and differentials. The universal derived counits identify the two
localized complexes with the displayed composite functors. The representative
comparison is natural on K-flat complexes; localization of their homotopy category
extends it uniquely to a natural isomorphism on the entire derived category.
This also applies when U is empty or one of the coefficient rings is zero. -/
private theorem completedAdic_slice_scalarComparison (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty
      (ringedDerivedRestrictionGeneral
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U ⋙
          completedAdicSliceDerivedChange X U f ≅
        completedAdicDerivedChange X f ⋙
          ringedDerivedRestrictionGeneral
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U) := by
  let O_R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let O_S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
  let A := SheafOfModules O_R
  let : (SheafOfModules.overFunctor O_R U).Additive := by
    exact (ringedOverFunctor_exactGeneral O_R U).1
  let : (SheafOfModules.overFunctor O_S U).Additive := by
    exact (ringedOverFunctor_exactGeneral O_S U).1
  let : (completedAdicChange X f).Additive := completedAdicChange_additive X f
  let : (completedAdicSliceChange X U f).Additive :=
    completedAdicSliceChange_additive X U f
  let : HasDerivedCategory A := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules O_S) := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules (O_R.over U)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules (O_S.over U)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (SheafOfModules.{t + 1}
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
          ((ProEt.topology X).over U)
          (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).obj S))) :=
    HasDerivedCategory.standard _
  let Q_A := DerivedCategory.Qh (C := A)
  let F := completedAdicDerivedChange X f
  let F_U := completedAdicSliceDerivedChange X U f
  let L_U := ringedDerivedRestrictionGeneral O_R U ⋙ F_U
  let L := F ⋙ ringedDerivedRestrictionGeneral O_S U
  let G_U :=
    ((SheafOfModules.overFunctor O_R U ⋙ completedAdicSliceChange X U f).mapHomotopyCategory
      (.up ℤ)) ⋙ DerivedCategory.Qh
  let G :=
    ((completedAdicChange X f ⋙ SheafOfModules.overFunctor O_S U).mapHomotopyCategory
      (.up ℤ)) ⋙ DerivedCategory.Qh
  obtain ⟨e₀⟩ := completedAdic_slice_scalarComparison_underived X U f
  let e : G_U ≅ G := Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory e₀.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory e₀.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] } DerivedCategory.Qh
  obtain ⟨α, α', hα, hα'⟩ := completedAdic_slice_scalarComparison_derived_data X U f
  let := hα
  let := hα'
  exact ⟨Functor.leftDerivedNatIso L_U L α α'
    (HomotopyCategory.quasiIso A (.up ℤ)) e⟩

private theorem residueOverMap_exact (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V) :
    (SheafOfModules.overMap.{t + 1} R f).Additive ∧
      PreservesFiniteLimits (SheafOfModules.overMap.{t + 1} R f) ∧
      PreservesFiniteColimits (SheafOfModules.overMap.{t + 1} R f) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let H := (ProEt.topology X).overMapPullback AddCommGrpCat.{t + 1} f
  have hAdd : F.Additive := ⟨fun {_ _} a b ↦ by ext V x; rfl⟩
  let e : F ⋙ SheafOfModules.toSheaf.{t + 1} (R.over U) ≅
      SheafOfModules.toSheaf.{t + 1} (R.over V) ⋙ H := Iso.refl _
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesColimitsOfSize.{t + 1, t + 1} H :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{t + 1}
      ((ProEt.topology X).over U) ((ProEt.topology X).over V)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits H :=
    PreservesColimitsOfSize.preservesFiniteColimits H
  have h (S : ShortComplex (SheafOfModules.{t + 1} (R.over V))) (hS : S.ShortExact) :
      (S.map F).ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SheafOfModules.toSheaf.{t + 1} (R.over U))
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e.symm)
      ((hS.map_of_exact (SheafOfModules.toSheaf.{t + 1} (R.over V))).map_of_exact H)
  exact ⟨hAdd, (Functor.exact_tfae F).out 0 3 |>.mp h⟩

/-- The exact derived restriction agrees with the chosen representative formula.
Source: Stacks Tags 03DJ and 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
private def residueRestrictionComparison (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (M : DerivedCategory (SheafOfModules.{t + 1} R)) :
    (ringedDerivedRestrictionGeneral R U).obj M ≅
      ringedSiteDerivedRestrictionOfUniverses R U M := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)

/-- A local isomorphism persists on every smaller chart.
Source: Stacks Tag 03DJ
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
private theorem residueRestrictIso_further (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V)
    (M N : DerivedCategory (SheafOfModules.{t + 1} R))
    (e : ringedSiteDerivedRestrictionOfUniverses R V M ≅
      ringedSiteDerivedRestrictionOfUniverses R V N) :
    Nonempty (ringedSiteDerivedRestrictionOfUniverses R U M ≅
      ringedSiteDerivedRestrictionOfUniverses R U N) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let FV := SheafOfModules.overFunctor.{t + 1} R V
  let FU := SheafOfModules.overFunctor.{t + 1} R U
  have := (residueOverMap_exact X R f).1
  have := (residueOverMap_exact X R f).2.1
  have := (residueOverMap_exact X R f).2.2
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  have := (ringedOverFunctor_exactGeneral R V).1
  have := (ringedOverFunctor_exactGeneral R V).2.1
  have := (ringedOverFunctor_exactGeneral R V).2.2
  have c (K : DerivedCategory (SheafOfModules.{t + 1} R)) :
      F.mapDerivedCategory.obj (ringedSiteDerivedRestrictionOfUniverses R V K) ≅
        ringedSiteDerivedRestrictionOfUniverses R U K :=
    F.mapDerivedCategory.mapIso (residueRestrictionComparison X R V K).symm ≪≫
      (Functor.mapDerivedCategoryCompIso FV F).symm.app K ≪≫
      (Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap R f)).app K ≪≫
      residueRestrictionComparison X R U K
  exact ⟨(c M).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫ c N⟩

/-- On a nonempty chart, the algebraic derived residue of a constant quotient model
has a projective representative in the residue interval. This asserts a model only
AFTER reduction modulo the image of the coefficient ideal, not a Tor bound before reduction.

Source: Stacks Project, sites-cohomology.tex, Tags 094I (lemma-bounded, part (2))
and 094G (lemma-locally-constant); proetale.tex, Tag 09C2.
(blueprint: lem-weil-pbc-finite-quotient-model-residue-projective).

Proof: let B = A/I^(n+1), J be the image of I in B, and identify B/J with A/I.
Scalar extension along B -> B/J has a total left derived functor: take flat K-flat
resolutions and extend scalars termwise, which preserves their quasi-isomorphisms.
Choose a geometric point of the nonempty chart W. Pull the covering sieve in the
residue-model hypothesis back along W -> V and choose a member through that point.
At the chosen geometric stalk, the constant realization of P has algebraic value P,
with the stated universe lift. Exactness of stalks and derived tensor pullback identify
its derived B/J-extension with the stalk of the residue reduction of M: iterate the
quotient compatibility square and use the scalar compatibility square to identify the
coefficient actions. On the chosen covering member, the hypothesis identifies that
residue with a complex of finite projective A/I-modules in [a,b]. Taking its stalk
recovers that algebraic complex. Transport it along B/J = A/I and remove the universe
lift by the module equivalence. The resulting complex E has zero terms outside [a,b],
projective terms, and its localization is the derived residue of Q(P). No nilpotent
lifting, Tor bound for Q(P), or finiteness assumption on P is used in this step. -/
theorem finiteQuotient_model_residueProjective
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) (a b : ℤ)
    (hresidue : FinitePerfectModelsOn X d φ M 0 V a b)
    (n : ℕ) (W : X.Etale) (g : W ⟶ V)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ)
    (hchart : Nonempty W.left)
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    let B := A ⧸ d.ideal ^ (n + 1)
    let J := d.ideal.map (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    ∃ (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} (B ⧸ J)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        @Functor.mapHomotopyCategory _ _ _ _ _ _ _
          (ModuleCat.extendScalars (Ideal.Quotient.mk J))
          (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk J)).left_adjoint_additive
          (.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) ∧
      ∃ E : CochainComplex (ModuleCat.{t} (B ⧸ J)) ℤ,
        E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Projective (B ⧸ J) (E.X i)) ∧
        Nonempty (L.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj E) := by
  classical
  let B := A ⧸ d.ideal ^ (n + 1)
  let J := d.ideal.map (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let B₀ := A ⧸ d.ideal ^ (0 + 1)
  let : Algebra B (B ⧸ J) := (Ideal.Quotient.mk J).toAlgebra
  let : (ModuleCat.extendScalars (Ideal.Quotient.mk J)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk J)).left_adjoint_additive
  obtain ⟨L, ε, hL, _⟩ := ModuleCat.exists_baseDerivedExtension_resolution.{t, t, t} B
    (B ⧸ J)
  refine ⟨L, ε, hL, ?_⟩
  let ρ : (B ⧸ J) ≃+* B₀ :=
    (DoubleQuot.quotQuotEquivQuotOfLE
      (Ideal.pow_le_self (Nat.succ_ne_zero n))).trans
      (Ideal.quotEquivOfEq (by simp))
  have hρ : ρ.toRingHom.comp (Ideal.Quotient.mk J) =
      adicQuotientMap d.ideal (n + 1) (0 + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    change (Ideal.quotEquivOfEq (show d.ideal = d.ideal ^ (0 + 1) by simp))
      ((DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (Nat.succ_ne_zero n)))
      (DoubleQuot.quotQuotMk (d.ideal ^ (n + 1)) d.ideal x)) = _
    rw [DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk, Ideal.quotEquivOfEq_mk]
    rfl
  let : RingHomInvPair ρ.toRingHom ρ.symm.toRingHom := RingHomInvPair.of_ringEquiv ρ
  let : RingHomInvPair ρ.symm.toRingHom ρ.toRingHom := RingHomInvPair.of_ringEquiv_symm ρ
  let K := DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P))
  let F := ModuleCat.restrictScalars.{t} ρ.symm.toRingHom
  let G := ModuleCat.restrictScalars.{t} ρ.toRingHom
  let C := (F.mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨T, hT, hlocal⟩ := hresidue
  obtain ⟨w⟩ := hchart
  obtain ⟨Z, f, hf, z, _⟩ := (mem_smallEtaleTopology_iff (T.pullback g)).1
    (X.smallEtaleTopology.pullback_stable g hT) w
  obtain ⟨E₀, ha, hb, hproj, ⟨e₀⟩⟩ := hlocal Z (f ≫ g) hf
  obtain ⟨en⟩ := residueRestrictIso_further X (completedAdicFiniteRing X d n)
    ((toProEt X).map f) _ _ e.some
  obtain ⟨ec⟩ := finiteQuotient_model_residueComparison X d φ hφ hcompat M n Z P
    ⟨en⟩ L ε hL ρ hρ
  obtain ⟨ealg⟩ := finiteConstantSlice_iso_reflects X B₀
    (completedAdicFiniteCommRing X d 0) (φ 0) (hφ 0) Z ⟨z⟩ C E₀
    ⟨ec.symm ≪≫ e₀⟩
  let E := (G.mapHomologicalComplex (.up ℤ)).obj E₀
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff] at ha ⊢
    intro i hi
    exact G.map_isZero (ha i hi)
  · rw [CochainComplex.isStrictlyLE_iff] at hb ⊢
    intro i hi
    exact G.map_isZero (hb i hi)
  · intro i
    let := (hproj i).1
    let e₁ : E₀.X i ≃ₛₗ[ρ.symm.toRingHom] E.X i :=
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change r • x = ρ (ρ.symm r) • x
          rw [ρ.apply_symm_apply] }
    exact Module.Projective.of_equiv (σ' := ρ.toRingHom) e₁
  · let eqv := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t} ρ
    let ret : F ⋙ G ≅ 𝟭 (ModuleCat.{t} (B ⧸ J)) := eqv.counitIso
    let eret : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
        𝟭 (DerivedCategory (ModuleCat.{t} (B ⧸ J))) :=
      (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
        Functor.mapDerivedCategoryNatIso ret ≪≫ Functor.mapDerivedCategoryIdIso _
    exact ⟨(DerivedCategory.Q.objObjPreimageIso _).symm ≪≫
      (eret.app (DerivedCategory.Q.obj K)).symm ≪≫
      G.mapDerivedCategory.mapIso
        (F.mapDerivedCategoryFactors.app K ≪≫ ealg) ≪≫
      G.mapDerivedCategoryFactors.app E₀⟩

end AlgebraicGeometry.Scheme
