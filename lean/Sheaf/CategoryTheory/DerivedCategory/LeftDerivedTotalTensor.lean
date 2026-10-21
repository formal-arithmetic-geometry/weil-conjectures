/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Left derived functors computed on K-flat complexes

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-def-sfb-derived-categories`, `def-sfb-left-derived-functor`
(blueprint: def-sfb-left-derived-functor).

The functor and its counit are Mathlib's canonical total left derived functor and
counit. This interface uses the binary total-tensor K-flatness recorded by the
statement dependency, without requiring a chosen monoidal structure on complexes.

## Main definitions

* `CategoryTheory.Functor.leftDerivedFunctorFromTotalTensor`: the total left derived functor.
* `CategoryTheory.Functor.leftDerivedFunctorFromTotalTensorCounit`: its canonical counit.
-/

@[expose] public section

universe uC vC uD vD wC wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem preservesCountableCoproducts_of_preservesInt
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasCountableCoproducts C] [HasColimitsOfShape ℤ C]
    (G : C ⥤ C) [G.Additive] [PreservesColimitsOfShape ℤ G]
    (I : Type) [Countable I] : PreservesColimitsOfShape (Discrete I) G := by
  classical
  have hm : Monotone Int.toNat := fun _ _ h ↦ Int.toNat_le_toNat h
  let t : ℤ ⥤ ℕ := hm.functor
  have ht : t.Final := (hm.final_functor_iff).2
    (fun n ↦ ⟨n, by simp⟩)
  have : HasColimitsOfShape ℕ C := Functor.Final.hasColimitsOfShape_of_final t
  have : PreservesColimitsOfShape ℕ G :=
    Functor.Final.preservesColimitsOfShape_of_final t G
  let q := IsFiltered.sequentialFunctor (Finset (Discrete I))
  have : HasColimitsOfShape (Finset (Discrete I)) C :=
    Functor.Final.hasColimitsOfShape_of_final q
  have : PreservesColimitsOfShape (Finset (Discrete I)) G :=
    Functor.Final.preservesColimitsOfShape_of_final q G
  refine ⟨?_⟩
  intro K
  let f : I → C := fun i ↦ K.obj ⟨i⟩
  let u : CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor (fun i ↦ G.obj (f i))) ⟶
      CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor f) ⋙ G :=
    { app S := sigmaComparison G (fun x : S ↦ f x.1.as)
      naturality S T a := by
        dsimp only [CoproductsFromFiniteFiltered.liftToFinsetObj, Functor.comp_map]
        ext x
        simp }
  have : IsIso u := NatIso.isIso_of_isIso_app u
  let c := G.mapCocone (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone f)
  let hc := isColimitOfPreserves G
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone f)
  let hc' := (IsColimit.precomposeHomEquiv (asIso u) c).symm hc
  let a : CoproductsFromFiniteFiltered.finiteSubcoproductsCocone (fun i ↦ G.obj (f i)) ⟶
      (Cocone.precompose u).obj c :=
    { hom := sigmaComparison G f
      w S := by
        dsimp [c, CoproductsFromFiniteFiltered.finiteSubcoproductsCocone]
        ext x
        simp [u] }
  have : IsIso a :=
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone (fun i ↦ G.obj (f i))).hom_isIso
      hc' a
  have : IsIso (sigmaComparison G f) := (Cocone.forget _).map_isIso a
  have : PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk)) G :=
    PreservesCoproduct.of_iso_comparison G f
  exact preservesColimit_of_iso_diagram G (Discrete.natIsoFunctor (F := K)).symm

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [hCountable : HasCountableCoproducts C] [hIntColimits : HasColimitsOfShape ℤ C]
  [hExactIntColimits : HasExactColimitsOfShape ℤ C]
  [hTensorLeft : ∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [hTensorRight : ∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [hFlatResolution : Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [hF : F.PreservesTotalTensorKFlatQuasiIso]

omit hExactIntColimits hTensorRight hFlatResolution [HasDerivedCategory C] in
private theorem preservesCountableTensorLeft (X : C) (I : Type) [Countable I] :
    PreservesColimitsOfShape (Discrete I) ((curriedTensor C).obj X) :=
  preservesCountableCoproducts_of_preservesInt _ I

omit hExactIntColimits hTensorLeft hFlatResolution [HasDerivedCategory C] in
private theorem preservesCountableTensorRight (X : C) (I : Type) [Countable I] :
    PreservesColimitsOfShape (Discrete I) ((curriedTensor C).flip.obj X) :=
  preservesCountableCoproducts_of_preservesInt _ I

attribute [local instance] preservesCountableTensorLeft preservesCountableTensorRight

omit hExactIntColimits hTensorRight hFlatResolution [HasDerivedCategory C] in
private theorem hasTensorFour (X₁ X₂ X₃ X₄ : GradedObject ℤ C) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by
  intro i j
  infer_instance

omit hExactIntColimits hTensorLeft hFlatResolution [HasDerivedCategory C] in
private theorem hasGoodTensorLeft (X₁ X₂ X₃ : GradedObject ℤ C) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by
  intro i j
  infer_instance

omit hExactIntColimits hTensorRight hFlatResolution [HasDerivedCategory C] in
private theorem hasGoodTensorRight (X₁ X₂ X₃ : GradedObject ℤ C) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by
  intro i j
  infer_instance

attribute [local instance] hasTensorFour hasGoodTensorLeft hasGoodTensorRight

omit hExactIntColimits hFlatResolution [HasDerivedCategory C] [HasDerivedCategory D] in
private theorem preservesKFlatQuasiIso : F.PreservesKFlatQuasiIso where
  quasiIso_map hP hP' s :=
    PreservesTotalTensorKFlatQuasiIso.quasiIso_map (F := F) hP hP' s

attribute [local instance] preservesKFlatQuasiIso

set_option linter.unusedSectionVars false in
include hCountable hIntColimits hExactIntColimits hTensorLeft hTensorRight hFlatResolution hF in
/-- Existence of the total left derived functor under the stated flat-resolution hypotheses.
Source: blueprint main-20261015, `def-sfb-left-derived-functor`, proof
(blueprint: def-sfb-left-derived-functor).

Proof: resolve the terms of each complex functorially by flat objects, and totalize
using countable coproducts. Exact integer-indexed colimits and their preservation
by both tensor functors make the resulting resolution K-flat and a quasi-isomorphism.
Compare two resolutions through a third. The recorded preservation property of `F`
inverts the quasi-isomorphisms between these resolutions after localization in `D`.
Thus K-flat complexes form a left derivability structure for this functor, whose
localization gives the asserted right Kan extension along the quasi-isomorphisms. -/
theorem hasLeftDerivedFunctor_of_preservesTotalTensorKFlatQuasiIso :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  exact F.derives_kFlat.hasLeftDerivedFunctor

/-- The total left derived functor of `F`, computed on K-flat resolutions.
Source: blueprint main-20261015, `def-sfb-left-derived-functor`, definition
(blueprint: def-sfb-left-derived-functor).
This is Mathlib's right Kan extension along localization, so the existence theorem
only supplies a proof that this universally characterized object exists. -/
noncomputable def leftDerivedFunctorFromTotalTensor : DerivedCategory C ⥤ DerivedCategory D :=
  letI := F.hasLeftDerivedFunctor_of_preservesTotalTensorKFlatQuasiIso
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The canonical counit of the total left derived functor.
Source: blueprint main-20261015, `def-sfb-left-derived-functor`, counit clause
(blueprint: def-sfb-left-derived-functor). -/
noncomputable def leftDerivedFunctorFromTotalTensorCounit :
    DerivedCategory.Qh ⋙ F.leftDerivedFunctorFromTotalTensor ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  letI := F.hasLeftDerivedFunctor_of_preservesTotalTensorKFlatQuasiIso
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerivedCounit
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The functor with its counit satisfies the total left derived universal property.
Source: blueprint main-20261015, `def-sfb-left-derived-functor`, definition
(blueprint: def-sfb-left-derived-functor).
Proof: the definitions are Mathlib's canonical right Kan extension and its counit;
their universal property is the defining property of `totalLeftDerived`. -/
theorem isLeftDerivedFunctor_leftDerivedFunctorFromTotalTensor :
    F.leftDerivedFunctorFromTotalTensor.IsLeftDerivedFunctor
      F.leftDerivedFunctorFromTotalTensorCounit
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  let := F.hasLeftDerivedFunctor_of_preservesTotalTensorKFlatQuasiIso
  dsimp only [leftDerivedFunctorFromTotalTensor, leftDerivedFunctorFromTotalTensorCounit]
  infer_instance

/-- The counit is invertible on every K-flat complex.
Source: blueprint main-20261015, `def-sfb-left-derived-functor`, counit clause
(blueprint: def-sfb-left-derived-functor).
Proof: K-flat complexes form the left derivability structure described in the
existence proof. The counit of a total left derived functor is invertible on its
resolving subcategory, hence on the image of each such complex in the homotopy category. -/
theorem isIso_leftDerivedFunctorFromTotalTensorCounit_app (P : CochainComplex C ℤ)
    (hP : P.IsKFlatForTotalTensor) :
    IsIso (F.leftDerivedFunctorFromTotalTensorCounit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) := by
  let := F.isLeftDerivedFunctor_leftDerivedFunctorFromTotalTensor
  exact F.derives_kFlat.isIso_of_isLeftDerivedFunctor
    F.leftDerivedFunctorFromTotalTensorCounit
    ⟨_, (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP⟩

/-- Applying `F` to any K-flat resolution computes its left derived functor.
Source: blueprint main-20261015, `def-sfb-left-derived-functor`, resolution formula
(blueprint: def-sfb-left-derived-functor).
Proof: localization makes the resolution quasi-isomorphism invertible. Apply the
derived functor to its inverse, and compose with the invertible counit at the
K-flat resolving complex. The quotient-localization comparison identifies the
resulting objects with the displayed complex localizations. -/
theorem leftDerivedFunctorFromTotalTensor_obj_resolution
    {P K : CochainComplex C ℤ} (s : P ⟶ K) [QuasiIso s]
    (hP : P.IsKFlatForTotalTensor) :
    Nonempty ((F.leftDerivedFunctorFromTotalTensor.obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  have := F.isIso_leftDerivedFunctorFromTotalTensorCounit_app P hP
  exact ⟨(F.leftDerivedFunctorFromTotalTensor.mapIso (asIso (DerivedCategory.Q.map s))).symm ≪≫
    (F.leftDerivedFunctorFromTotalTensor.mapIso
      ((DerivedCategory.quotientCompQhIso C).app P)).symm ≪≫
    asIso (F.leftDerivedFunctorFromTotalTensorCounit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) ≪≫
    (DerivedCategory.quotientCompQhIso D).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)⟩

include hCountable hIntColimits hExactIntColimits hTensorLeft hTensorRight hFlatResolution hF in
/-- A functor with counit is left derived exactly when its counit is invertible on K-flats.
Source: blueprint main-20261015, `def-sfb-left-derived-functor`, final sentence
(blueprint: def-sfb-left-derived-functor).
Proof: the K-flat left derivability structure identifies the universal property of
a right Kan extension along localization with invertibility of the counit on its
resolving objects. Every homotopy-category object has a complex representative;
K-flatness of that representative gives precisely the test written here. -/
theorem isLeftDerivedFunctor_iff_isIso_app_of_totalTensorKFlat
    {LF : DerivedCategory C ⥤ DerivedCategory D}
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ↔
      ∀ (P : CochainComplex C ℤ), P.IsKFlatForTotalTensor →
        IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) := by
  exact F.isLeftDerivedFunctor_iff_isIso_app_of_kFlat α

end CategoryTheory.Functor
