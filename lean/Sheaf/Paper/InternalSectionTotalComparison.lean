/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical internal-to-sectionwise total-complex comparison

Source: Stacks Project, Tags 08J9, 08JA and 08JB; blueprint module objects and
derived tensor--Hom (blueprint: def-sfb-internal-section-total-comparison).

## Main definitions

* `totalComparison`: the fixed comparison of the concrete sum-total complexes.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- The reconstructed section-ring sheaf of the pulled-back coefficient ring.
Source: Stacks 03CV (blueprint: def-sfb-internal-section-total-comparison). -/
abbrev ring : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (condensedRingObj Λ X)

/-- Internal module objects, with the relative coequalizer tensor.
Source: blueprint module objects
(blueprint: def-sfb-internal-section-total-comparison). -/
abbrev Internal := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
  (condensedRingObj Λ X)

/-- Sectionwise module sheaves over the reconstructed ring.
Source: Stacks 03CV (blueprint: def-sfb-internal-section-total-comparison). -/
abbrev Modules := SheafOfModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X))

/-- The fixed equivalence, unchanged on underlying sheaves and maps.
Source: Stacks 00YV (blueprint: def-sfb-internal-section-total-comparison). -/
abbrev equivalence : Internal Λ X ≌ Modules Λ X :=
  sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)

/-- Grothendieck abelianness supplies the small ordinary derived-category universe.
Source: Stacks 07A5 (blueprint: def-sfb-internal-section-total-comparison).
Proof: apply Grothendieck abelianness of module sheaves on a site small in
the coefficient universe. Restriction of scalars from the commutative ring
sheaf to its underlying ring sheaf does not change this category. -/
@[instance] theorem sectionModulesGrothendieck {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u + 1}) :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) := by
  classical
  let S : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  have : HasFilteredColimitsOfSize.{u + 1, u + 1} (SheafOfModules.{u + 1} S) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{u + 1, u + 1} (SheafOfModules.{u + 1} S) :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (SheafOfModules.toSheaf S)⟩
  let T (U : C) := (PresheafOfModules.sheafification.{u + 1} (𝟙 S.obj)).obj
    ((PresheafOfModules.free S.obj).obj (uliftYoneda.{u + 1}.obj U))
  have hs : ObjectProperty.IsSeparating (.ofObj T) := by
    intro M N f g h
    apply (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj).map_injective
    ext ⟨U⟩ x
    let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 S.obj)
    let e (M : SheafOfModules.{u + 1} S) :=
      (adj.homEquiv
        ((PresheafOfModules.free S.obj).obj (uliftYoneda.{u + 1}.obj U)) M).trans
        (PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv)
    have hn (a : T U ⟶ M) (k : M ⟶ N) :
        (e N) (a ≫ k) = k.val.app (.op U) ((e M) a) := by
      dsimp only [e, Equiv.trans_apply]
      rw [adj.homEquiv_naturality_right]
      let a' := (adj.homEquiv _ _) a
      let k' := (SheafOfModules.forget S ⋙
        PresheafOfModules.restrictScalars (𝟙 S.obj)).map k
      change uliftYonedaEquiv (PresheafOfModules.freeHomEquiv (a' ≫ k')) = _
      have hh := (PresheafOfModules.freeAdjunction S.obj).homEquiv_naturality_right a' k'
      rw [PresheafOfModules.freeAdjunction_homEquiv,
        PresheafOfModules.freeAdjunction_homEquiv] at hh
      erw [hh, uliftYonedaEquiv_comp]
    have hh := congrArg (e N) (h _ (ObjectProperty.ofObj_apply T U) ((e M).symm x))
    rw [hn, hn, Equiv.apply_symm_apply] at hh
    exact hh
  have : HasSeparator (SheafOfModules.{u + 1} S) :=
    ⟨_, hs.isSeparator_coproduct⟩
  exact {}

/-- Fix the dependency's existing totalization instance for this internal category.
Source: Stacks 012Z; lem-pe-internal-section-tensor-comparison
(blueprint: def-sfb-internal-section-total-comparison). -/
instance internalTotalExists (P Q : CochainComplex (Internal Λ X) ℤ) :
    P.HasMapBifunctor Q (curriedTensor (Internal Λ X)) :=
  comparison_internalTotalExists (Scheme.ProEt.topology X) (condensedRingObj Λ X) P Q

/-- The native total tensor on internal complexes.
Source: Stacks 06YL (blueprint: def-sfb-internal-section-total-comparison). -/
instance internalComplexMonoidal : MonoidalCategory (CochainComplex (Internal Λ X) ℤ) :=
  CategoryTheory.Mod.monoidalCategoryCochainComplex

/-- The native total tensor, with its instance fixed explicitly.
Source: Stacks 06YL (blueprint: def-sfb-internal-section-total-comparison). -/
def internalTotalTensor (P Q : CochainComplex (Internal Λ X) ℤ) :
    CochainComplex (Internal Λ X) ℤ :=
  (internalComplexMonoidal Λ X).tensorObj P Q

/-- The ordinary lax localization comparison, for the same total tensor.
Source: Stacks 06YS (blueprint: def-sfb-internal-section-total-comparison). -/
def localizationTensorMap (P Q : CochainComplex (Internal Λ X) ℤ) :
    ((CondensedRing.derivedTensor Λ X).obj ((DerivedCategory.Q (C := Internal Λ X)).obj P)).obj
      ((DerivedCategory.Q (C := Internal Λ X)).obj Q) ⟶
      (DerivedCategory.Q (C := Internal Λ X)).obj (internalTotalTensor Λ X P Q) := by
  letI := internalComplexMonoidal Λ X
  exact Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Internal Λ X)) P Q

/-- Its termwise extension to ordinary unbounded derived categories.
Source: Stacks 05RU (blueprint: def-sfb-internal-section-total-comparison). -/
def forward : DerivedCategory (Internal Λ X) ⥤ DerivedCategory (Modules Λ X) :=
  (equivalence Λ X).functor.mapDerivedCategory

/-- The functorial K-injective sheaf-Hom model, retaining both site universes.
Source: Stacks 08J7 (blueprint: def-sfb-internal-section-total-comparison). -/
def hom : (DerivedCategory (Modules Λ X))ᵒᵖ × DerivedCategory (Modules Λ X) ⥤
    DerivedCategory (Modules Λ X) :=
  derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X)

/-- The exact equivalence applied termwise to cochain complexes.
Source: Stacks 05RU (blueprint: def-sfb-internal-section-total-comparison). -/
def complexForward :
    CochainComplex (Internal Λ X) ℤ ⥤ CochainComplex (Modules Λ X) ℤ :=
  (equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)

/-- The actual localization comparison for the termwise equivalence.
Source: Stacks 05RU (blueprint: def-sfb-internal-section-total-comparison). -/
def localizationIso : DerivedCategory.Q ⋙ forward Λ X ≅
    complexForward Λ X ⋙ DerivedCategory.Q :=
  (equivalence Λ X).functor.mapDerivedCategoryFactors

/-- The ordinary sectionwise tensor bifunctor, with its coefficient ring fixed.
Source: Stacks 03EK (blueprint: def-sfb-internal-section-total-comparison). -/
abbrev sectionTensor : Modules Λ X ⥤ Modules Λ X ⥤ Modules Λ X :=
  @curriedTensor (Modules Λ X) _ (SheafOfModules.monoidalCategory (ring Λ X))

/-- The dependency's ordinary tensor comparison, fixed by its pure-tensor formula.
Source: Stacks 03EK; lem-pe-internal-section-tensor-comparison
(blueprint: def-sfb-internal-section-total-comparison). -/
def ordinaryTensorIso (M N : Internal Λ X) :
    (equivalence Λ X).functor.obj (M ⊗ N) ≅
      ((sectionTensor Λ X).obj ((equivalence Λ X).functor.obj M)).obj
        ((equivalence Λ X).functor.obj N) :=
  (internal_section_tensor_comparison (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)).2.choose M N

attribute [local irreducible] ordinaryTensorIso

/-- The canonical total-complex comparison, characterized on every total summand.
The ordinary comparison on the right is the dependency's pure-tensor-normalized
witness; total coproduct inclusions determine the comparison uniquely.
Source: Stacks 03EK, 06YL; lem-pe-internal-section-tensor-comparison
(blueprint: def-sfb-internal-section-total-comparison).
Proof: take the total-complex witness in the last part of the dependency's
internal_section_tensor_comparison. Its displayed summand equations are exactly
these equations. The chosen ordinary tensor witness is the preceding existential
witness in that same theorem, so the pure-tensor characterization is retained.
Two such isomorphisms agree after every total summand inclusion, hence in each
degree by the coproduct universal property, and then as complex morphisms. -/
theorem canonicalComplexTensorComparison (P Q : CochainComplex (Internal Λ X) ℤ) :
    ∃ t : (complexForward Λ X).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor (Internal Λ X))) ≅
      CochainComplex.mapBifunctor ((complexForward Λ X).obj P)
        ((complexForward Λ X).obj Q) (sectionTensor Λ X),
      ∀ (p q n : ℤ) (h : p + q = n),
        (equivalence Λ X).functor.map
            (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫ t.hom.f n =
          (ordinaryTensorIso Λ X (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor ((complexForward Λ X).obj P)
            ((complexForward Λ X).obj Q) (sectionTensor Λ X) p q n h := by
  obtain ⟨t, ht⟩ := (internal_section_tensor_comparison (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)).2.choose_spec.choose_spec.2.2.2.2.2.2.2.1 P Q
  refine ⟨t, ?_⟩
  intro p q n h
  have he : ordinaryTensorIso Λ X (P.X p) (Q.X q) =
      (internal_section_tensor_comparison (Scheme.ProEt.topology X)
        (condensedRingObj Λ X)).2.choose (P.X p) (Q.X q) := by
    delta ordinaryTensorIso
    rfl
  rw [he]
  exact ht p q n h

/-- The existing total-complex comparison, pinned on every summand by the
ordinary tensor comparison and hence on every local pure tensor.
Source: Stacks 03EK, 06YL and lem-pe-internal-section-tensor-comparison
(blueprint: def-sfb-internal-section-total-comparison). -/
def complexTensorIso (P Q : CochainComplex (Internal Λ X) ℤ) :
    (complexForward Λ X).obj
      (CochainComplex.mapBifunctor P Q (curriedTensor (Internal Λ X))) ≅
    CochainComplex.mapBifunctor ((complexForward Λ X).obj P)
      ((complexForward Λ X).obj Q) (sectionTensor Λ X) :=
  (canonicalComplexTensorComparison Λ X P Q).choose

/-- The native source tensor and the explicit sum total have the same complex.
Source: Stacks 06YL (blueprint: def-sfb-internal-section-total-comparison).
Proof: unfold the native cochain monoidal instance. Its tensor object is exactly
HomologicalComplex.mapBifunctor for the relative tensor and the up shape. -/
theorem internalTotalTensor_eq (P Q : CochainComplex (Internal Λ X) ℤ) :
    internalTotalTensor Λ X P Q = CochainComplex.mapBifunctor P Q (curriedTensor _) := by
  rfl

/-- The representative-model tensor and the explicit sectionwise sum total agree.
Source: Stacks 06YL (blueprint: def-sfb-internal-section-total-comparison).
Proof: unfold coefficientTotalTensor and the cochain mapBifunctor abbreviation.
Both are the same uncurrying of map₂HomologicalComplex on the sheaf tensor. -/
theorem sectionTotalTensor_eq (P Q : CochainComplex (Modules Λ X) ℤ) :
    CochainComplex.mapBifunctor P Q (sectionTensor Λ X) =
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
        (P, Q) := by
  rfl

/-- The canonical summand comparison has the concrete native tensor endpoints.
Heterogeneous equality records only the equality of the two implementations of
these endpoints; it retains the entire fixed comparison, not merely existence.
Source: Stacks 03EK, 06YL
(blueprint: def-sfb-internal-section-total-comparison).
Proof: internalTotalTensor_eq identifies the source total. The definition of
complexForward is the termwise section equivalence, and sectionTotalTensor_eq
identifies the target total. Transport complexTensorIso along these object
identifications. Equality after this transport is precisely the displayed HEq;
heterogeneous equality with that fixed isomorphism gives uniqueness. -/
theorem totalComparison_existsUnique (P Q : CochainComplex (Internal Λ X) ℤ) :
    ∃! c : (complexForward Λ X).obj (internalTotalTensor Λ X P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
        ((complexForward Λ X).obj P, (complexForward Λ X).obj Q),
      HEq c (complexTensorIso Λ X P Q) := by
  rw [internalTotalTensor_eq, ← sectionTotalTensor_eq]
  refine ⟨complexTensorIso Λ X P Q, HEq.rfl, ?_⟩
  intro c hc
  exact eq_of_heq hc

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
