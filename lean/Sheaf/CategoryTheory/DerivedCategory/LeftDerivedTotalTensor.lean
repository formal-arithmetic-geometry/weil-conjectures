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

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [hCountable : HasCountableCoproducts C] [hIntColimits : HasColimitsOfShape ℤ C]
  [hExactIntColimits : HasExactColimitsOfShape ℤ C]
  [hTensorLeft : ∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [hTensorRight : ∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [hFlatResolution : Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [hF : F.PreservesTotalTensorKFlatQuasiIso]

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end CategoryTheory.Functor
