/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.ContinuousConstructibleModule
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.RationalModuleRealizationFunctor
public import Sheaf.Paper.IntegralTStructure
public import Sheaf.Paper.LocalizedTStructure
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits

/-!
# Degree reflection for rational module realization

Source: Bhatt--Scholze, Propositions 6.8.11(3) and 6.8.14(2), pp. 61--62;
BBD, Proposition 1.3.3 and Theorem 1.3.6
(blueprint: lem-per-rational-realization-degree-reflection).

The raw rational category carries its localized standard t-structure. Full faithfulness
of the specified module realization is assumed. No torsion-freeness or compatibility
between finite-level reduction and truncation is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The localized standard t-structure already specified by the dependency theorem.
Its two halves are the strictly full images of the integral standard halves; these
uniquely determine the t-structure, so this selects no unspecified mathematical data.
Source: Bhatt--Scholze, Propositions 6.8.11(3) and 6.8.14(2), and BBD 1.3.3
(blueprint: lem-per-rational-realization-degree-reflection). -/
abbrev rationalRealizationTStructure := (pbc_localized_tstructure X l E).choose

/-- The realization's specified shift comparison, exposed for the connecting-map equation.
Source: Bhatt--Scholze, Proposition 6.8.14(2), and BBD 1.3.3
(blueprint: lem-per-rational-realization-degree-reflection). -/
instance rationalRealizationCommShift (R : RationalModuleRealization l E X) :
    R.J.CommShift ℤ := R.shift

/-- A fully faithful rational module realization reflects both degree bounds,
commutes naturally with the normalized truncation triangles, realizes heart-valued
cohomology by ordinary localized sheaves, and identifies its heart with the
objects of its essential image concentrated in degree zero.
Source: Bhatt--Scholze, Propositions 6.8.11(3) and 6.8.14(2), pp. 61--62;
BBD, Proposition 1.3.3 and Theorem 1.3.6
(blueprint: lem-per-rational-realization-degree-reflection).

Proof, following the node's seven steps:
1. The cohomology formula of lem-per-rational-module-realization-functor preserves
both integral degree bounds. The strictly full image descriptions in
prop-weil-localized-tstructure, shifted by m, therefore show that J preserves both
localized bounds, using def-sbc-standard-tstructure-derived-category.
2. Apply the triangulated J to the canonical localized truncation triangle. Its
end terms have the ambient bounds. Uniqueness of truncation triangles in
lem-weil-heart-short-exact-triangles gives the two comparison isomorphisms, with
identity on the middle term and compatibility with the connecting arrow and shift.
3. The truncation adjunctions make these comparisons natural for every rational
morphism: the lower maps have the same composite with the counit, and the upper
maps have the same precomposition with the unit. This includes all fractions.
4. If JZ has upper bound m, the ambient lower counit is invertible. Its comparison
makes J of the localized counit invertible. Fullness lifts its inverse; faithfulness
reflects the two inverse equations. Thus Z is isomorphic to its lower truncation.
5. Dually, an ambient lower bound makes the upper unit invertible. Lift its inverse
by fullness and verify the inverse equations by faithfulness. Isomorphism closure
then gives the localized lower bound.
6. Heart-valued cohomology is truncGE 0 of truncLE 0 of the r-shift. The localized
comparisons identify it with Q of integral heart-valued cohomology. The ambient
good truncations of def-kun-truncations identify the latter with the ordinary
sheaf H^r(K) in degree zero, by the kernel/image quotient calculation in
def-weil-derived-cohomology-sheaves. Apply the exact scalar extension and its
natural cohomology comparison; the result is E_X tensor H^r(K) in degree zero.
7. Intersect the reflected bounds at zero. This identifies heart membership with
vanishing in all nonzero degrees. Transport this condition along isomorphisms in
the essential image; full faithfulness restricts to the resulting full categories.
None of these steps uses torsion-freeness or a finite-level truncation formula. -/
theorem rationalRealizationDegreeReflection (R : RationalModuleRealization l E X)
    (_hJ : R.J.FullyFaithful) :
    (∀ (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) (m : ℤ),
      ((rationalRealizationTStructure l E X).le m
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ↔
        ∀ r : ℤ, m < r → IsZero ((DerivedCategory.homologyFunctor _ r).obj
          (R.J.obj ((pbcRationalization X (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K)))) ∧
      ((rationalRealizationTStructure l E X).ge m
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ↔
        ∀ r : ℤ, r < m → IsZero ((DerivedCategory.homologyFunctor _ r).obj
          (R.J.obj ((pbcRationalization X (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K))))) ∧
    (∃ (α : ∀ m : ℤ, (rationalRealizationTStructure l E X).truncLE m ⋙ R.J ≅
          R.J ⋙ DerivedCategory.TStructure.t.truncLE m)
      (β : ∀ m : ℤ, (rationalRealizationTStructure l E X).truncGE m ⋙ R.J ≅
          R.J ⋙ DerivedCategory.TStructure.t.truncGE m),
      ∀ (m : ℤ) (Z : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E)),
        (α m).hom.app Z ≫ (DerivedCategory.TStructure.t.truncLEι m).app (R.J.obj Z) =
          R.J.map (((rationalRealizationTStructure l E X).truncLEι m).app Z) ∧
        R.J.map (((rationalRealizationTStructure l E X).truncGEπ m).app Z) ≫
            (β m).hom.app Z =
          (DerivedCategory.TStructure.t.truncGEπ m).app (R.J.obj Z) ∧
        R.J.map (((rationalRealizationTStructure l E X).truncGEδLE m (m + 1) rfl).app Z) ≫
            (R.J.commShiftIso (1 : ℤ)).hom.app
              (((rationalRealizationTStructure l E X).truncLE m).obj Z) ≫
            (shiftFunctor _ (1 : ℤ)).map ((α m).hom.app Z) =
          (β (m + 1)).hom.app Z ≫
            (DerivedCategory.TStructure.t.truncGEδLE m (m + 1) rfl).app (R.J.obj Z)) ∧
    (∀ r : ℤ, Nonempty (
      pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
          shiftFunctor _ r ⋙ (rationalRealizationTStructure l E X).truncLE 0 ⋙
          (rationalRealizationTStructure l E X).truncGE 0 ⋙ R.J ≅
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
          DerivedCategory.homologyFunctor _ r ⋙ pbcExtend (R.integralIso.hom ≫ R.inclusion) ⋙
          DerivedCategory.singleFunctor _ 0)) ∧
    (∀ Z : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E),
      (rationalRealizationTStructure l E X).heart Z ↔
        ∀ r : ℤ, r ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ r).obj (R.J.obj Z))) ∧
    (∀ M : DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)),
      (∃ Z : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E),
        (rationalRealizationTStructure l E X).heart Z ∧ Nonempty (R.J.obj Z ≅ M)) ↔
      R.J.essImage M ∧
        ∀ r : ℤ, r ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ r).obj M)) := by
  sorry

end AlgebraicGeometry.Scheme
