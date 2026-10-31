/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-! # The cohomological interval of a strict Roos complex

Source: Bhatt--Scholze, Proposition 3.1.11, proof.
(blueprint: lem-sp-roos-cohomological-amplitude).
-/

@[expose] public section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem product_homology_isZero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [HasExactLimitsOfShape (Discrete ℕ) A]
    (K : ℕ → CochainComplex A ℤ) (i : ℤ)
    (hK : ∀ n, IsZero ((HomologicalComplex.homologyFunctor A (.up ℤ) i).obj (K n))) :
    IsZero ((HomologicalComplex.homologyFunctor A (.up ℤ) i).obj (∏ᶜ K)) := by
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : CountableAB4Star A := CountableAB4Star.of_hasExactLimitsOfShape_nat A
  obtain ⟨hP, hQ, hH⟩ := derivedCategory_countableProducts_core A
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor A i) :=
    hH ℕ i
  have hc := isLimitOfPreserves (DerivedCategory.homologyFunctor A i) (hQ ℕ K).some
  have hz : IsZero ((DerivedCategory.homologyFunctor A i).obj
      (DerivedCategory.Q.obj (∏ᶜ K))) := by
    apply hc.isZero_pt
    rw [Functor.isZero_iff]
    intro n
    exact (hK n.as).of_iso ((DerivedCategory.homologyFunctorFactors A i).app (K n.as))
  exact hz.of_iso ((DerivedCategory.homologyFunctorFactors A i).app (∏ᶜ K)).symm

/-- Exact countable products enlarge a uniform cohomology interval by at most one
when passing to the strict Roos complex. No condition on the transition maps is needed.

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 3.1.11,
proof (blueprint: lem-sp-roos-cohomological-amplitude).

Proof: Homology commutes with exact countable products, so the product of the tower
has zero homology in every degree outside the given interval. In the distinguished
mapping-cocone triangle Roos(P) → product(P) → product(P), exactness at H^i(Roos(P))
places it between H^(i-1)(product(P)) and H^i(product(P)). Both are zero below a
and above b+1, and exactness therefore makes the middle object zero. -/
theorem roosCohomologicalAmplitude
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [HasExactLimitsOfShape (Discrete ℕ) A]
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a b : ℤ)
    (hP : ∀ n i, i < a ∨ b < i →
      IsZero ((HomologicalComplex.homologyFunctor A (.up ℤ) i).obj
        (P.asFunctor.obj (op n))))
    (i : ℤ) (hi : i < a ∨ b + 1 < i) :
    IsZero ((HomologicalComplex.homologyFunctor A (.up ℤ) i).obj (roosF.obj P)) := by
  have hz (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((DerivedCategory.homologyFunctor A j).obj
        (DerivedCategory.Q.obj (roosP P))) :=
    (product_homology_isZero (fun n ↦ P.asFunctor.obj (op n)) j
      (fun n ↦ hP n j hj)).of_iso
        ((DerivedCategory.homologyFunctorFactors A j).app (roosP P))
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle (roosU P))
  have hT : T ∈ distTriang _ :=
    DerivedCategory.mappingCocone_triangle_distinguished (roosU P)
  have he := DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega)
  have hzero := he.isZero_of_both_isZero (hz (i - 1) (by omega)) (hz i (by omega))
  exact hzero.of_iso ((DerivedCategory.homologyFunctorFactors A i).app (roosF.obj P)).symm

end CategoryTheory
