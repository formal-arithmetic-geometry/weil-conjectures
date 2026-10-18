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
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.SiteRestrictionInjectives
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The affine basis criterion also holds for arbitrary abelian sheaves.
Source: Stacks, Tag 0991 (blueprint: lem-cbc-proetale-stalk-conservative).
Proof: restriction to the affine ind-etale basis is an equivalence of sheaf categories,
so it reflects zero objects; zero abelian sheaves have zero sections. For a general
scheme first apply the covering criterion to any affine open cover, as in Step 3. -/
theorem proEtale_abelian_affine_basis_zero_detection (T : Scheme.{u}) [IsAffine T]
    (H : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) :
    IsZero H ↔ ∀ W : T.AffineProEt,
      IsZero (H.obj.obj (op ((AffineProEt.toProEt T).obj W))) := by
  sorry

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

/-- Clause (4): the specified quotient has zero geometric stalks and zero sections
on Spec k, but is nonzero; on affine objects its sections are all functions modulo
locally constant functions. Source: Stacks, Tags 0991 and 0F6D
(blueprint: lem-cbc-proetale-stalk-conservative).
Proof: the functions-quotient-sections lemma supplies the affine formula; the canonical
constant-function map and the sheafification adjunction identify its cokernel with
our constructed quotient. On Spec k all functions are constant. The strict localization
at any geometric point is Spec k itself: every pointed etale neighbourhood has its
unique k-valued section, including geometric points with a larger algebraically closed
field. The classical stalk formula therefore gives zero stalks. For nonvanishing take
the one-point compactification E of N and B=colim Map(E_n,k), with E_n the finite
truncations. This is ind-Zariski, hence ind-etale, and Spec B is a pro-etale object
with point space E. A function zero on N and nonzero at infinity is not locally
constant. Its class in the displayed affine quotient is nonzero. Thus 0→Q is a
non-isomorphism whose geometric stalk maps are isomorphisms. -/
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
  sorry

end AlgebraicGeometry.Scheme
