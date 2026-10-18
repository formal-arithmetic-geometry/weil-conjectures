/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.TorsionAssembly
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.ThreeStepAdjunctionComparison
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.Paper.CondensedAmbientExchange

/-!
# Proper base change on classical pro-etale complexes

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/_section.md, order 1062
(blueprint: sk-thm-properbasechange).

The exchange below is the published ambient ringed exchange specialized to arbitrary
constant coefficients and their constant-section identifications. The conclusion records
both endpoints in the bounded-below classical full subcategory and invertibility of the
specified ambient morphism; fullness then places its inverse in that subcategory.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical uncompleted constant-coefficient exchange: the published ambient ringed
exchange `proEtaleAmbientRingedExchange` (def-weil-pbc-ambient-ringed-exchange) on the four
constant ring sheaves with their constant-section identifications. It is the
unit--square--counit mate of the canonical composition comparisons. The two composite
coefficient identifications agree because both are the constant comparison for the same
composite arrow (`proEtaleConstantRingCompositeCoefficients_eq` and the square equation).
Source: blueprint proper-base-change theorem, displayed exchange, and Stacks Tag 07A7
(blueprint: sk-thm-properbasechange). No torsion or classicality enters this construction. -/
abbrev classicalProEtaleExchange (Λ : Type u) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y Λ) (proEtaleConstantRing X Λ)
        (proEtaleConstantRingComparison f Λ) ⋙ proEtaleConstantRingDerivedPullback Λ g ⟶
      proEtaleConstantRingDerivedPullback Λ g' ⋙
        proEtaleRingDerivedDirectImage f' (proEtaleConstantRing Y' Λ)
          (proEtaleConstantRing X' Λ) (proEtaleConstantRingComparison f' Λ) :=
  proEtaleAmbientRingedExchange sq
    (proEtaleConstantRing X Λ) (proEtaleConstantRing Y Λ)
    (proEtaleConstantRing X' Λ) (proEtaleConstantRing Y' Λ)
    (proEtaleConstantRingComparison f Λ) (proEtaleConstantRingComparison g Λ)
    (proEtaleConstantRingComparison g' Λ) (proEtaleConstantRingComparison f' Λ)
    ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f Λ)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q Λ) sq.w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g Λ)).symm))

/-- Proper base change for bounded-below classical complexes with locally torsion
underlying abelian cohomology, for arbitrary constant commutative coefficients.
Source: blueprint main-20261015, sk-thm-properbasechange, order 1062
(blueprint: sk-thm-properbasechange).

Proof plan, following the nine DAG steps:
1. Use sk-prop-sf-comparison and det-pe-classical-derived-equivalence to write K as
   nu_X^* L by its counit; exactness identifies their cohomology sheaves.
2. Descend local torsion to L: the exact fully faithful left adjoint nu_X^* preserves
   the integer-torsion kernels and their sheaf colimit and reflects its invertibility.
   Use det-pe-classical-sheaves-modules, the left-adjoint colimit theorem and
   lem-weil-pbc-module-sheaves-colimits-forgetful; no uniform annihilator is chosen.
3. Apply lemma-weil-pbc-torsion-assembly to torsion abelian sheaves in degree zero.
4. Starting below a lower cohomological bound, induct through finite truncation
   triangles. The derived exchange commutes with shifts, and the triangulated
   two-out-of-three lemma transfers invertibility from adjacent truncations and
   the shifted cohomology sheaf. The zero truncation is the induction base.
5. For each degree m, the map from the upper truncation at m induces isomorphisms
   in that degree after both composites, by the derived-functor-truncation-iso
   lemma and exact inverse image. Naturality and cohomology conservativity finish
   the bounded-below abelian case; no infinite Postnikov limit is taken.
6. Apply lem-weil-pbc-exchange-forget-coefficients: exact conservative forgetting
   commutes with the two derived direct images by acyclicity, and identifies the
   actual module mate with the abelian mate, so reflects its invertibility.
7. Properness of f and its base change gives qcqs vertical edges. Apply
   sk-thm-pe-direct-image-comparison for arbitrary discrete coefficients, including
   its inverse-image, unit, counit and composition compatibility clauses.
8. Write each exchange as unit, square comparison, counit. The three-step
   adjunction-comparison lemma gives commuting comparison squares; composing them
   conjugates the pro-etale exchange to nu_Y'^* of the etale exchange.
9. Transport along the counit isomorphism to K using naturality. The comparisons
   identify both endpoints with nu_Y'^* of bounded-below etale complexes, hence
   they are bounded below and classical. Fullness retains the inverse morphism.
-/
theorem isIso_classicalProEtaleExchange_of_isProper (Λ : Type u) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g) (K : proEtaleDerivedCategory X Λ)
    (hbounded : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (hclassical : ProEtale.IsClassicalModuleComplex K)
    (htorsion : ∀ q : ℤ,
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X Λ)) q).obj K)).IsTorsion) :
    (∃ n : ℤ, DerivedCategory.IsGE
      ((proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y Λ)
        (proEtaleConstantRing X Λ) (proEtaleConstantRingComparison f Λ) ⋙
      proEtaleConstantRingDerivedPullback Λ g).obj K) n) ∧
    ProEtale.IsClassicalModuleComplex ((proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y Λ)
        (proEtaleConstantRing X Λ) (proEtaleConstantRingComparison f Λ) ⋙
      proEtaleConstantRingDerivedPullback Λ g).obj K) ∧
    (∃ n : ℤ, DerivedCategory.IsGE
      ((proEtaleConstantRingDerivedPullback Λ g' ⋙
      proEtaleRingDerivedDirectImage f' (proEtaleConstantRing Y' Λ)
        (proEtaleConstantRing X' Λ) (proEtaleConstantRingComparison f' Λ)).obj K) n) ∧
    ProEtale.IsClassicalModuleComplex ((proEtaleConstantRingDerivedPullback Λ g' ⋙
      proEtaleRingDerivedDirectImage f' (proEtaleConstantRing Y' Λ)
        (proEtaleConstantRing X' Λ) (proEtaleConstantRingComparison f' Λ)).obj K) ∧
    IsIso ((classicalProEtaleExchange Λ sq).app K) := by
  sorry

end AlgebraicGeometry.Scheme
