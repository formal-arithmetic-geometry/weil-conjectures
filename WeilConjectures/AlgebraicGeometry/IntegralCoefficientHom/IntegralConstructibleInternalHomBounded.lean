/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientHom.IntegralConstructibleInternalHomData
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Admissible integral Hom residue test

The helper refines the corresponding step of `cor-coef-integral-internal-hom`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientHom
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]


/-- Canonical principal reductions and the residue test for integral internal Hom.
Source: latest blueprint `cor-coef-integral-internal-hom.proof.md`, sentence 1 and
its concluding integral-output test; `lem-coef-integral-hom-reduction.proof.md`.
(blueprint: lem-coef-admissible-integral-hom-residue-test).

Proof: use the specified admissible condensed coefficient isomorphism to identify R
with an integral p-adic coefficient ring, taking the bottom finite subextension in
its Z_l alternative. This identifies powers of the irreducible pi with powers of a
standard uniformizer up to units. The corresponding quotient and scalar-extension
squares commute with their units, tensorators and evaluation transposes. Noetherianity
identifies stratified finite presentation with finite constant local models. The
forward integral residue criterion makes the second input complete. The two-term
free principal quotient resolution and exact R-linear internal Hom identify every
restricted comparison with scalar extension
of evaluation; conservative restriction gives invertibility of the specified map.
Hom into the complete object L preserves the product/Roos completion triangle, so
H is complete. If its first reduction is bounded constructible, the reverse integral
residue criterion makes H bounded constructible. Transport these predicates back
through the coefficient equivalence. This does not assert constructibility of H's
first reduction, any finite-level Hom bound, or any uniform Tor interval. -/
theorem admissible_integral_hom_residue_test
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hR :
      Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
        Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
          Mon.mk (Profinite.padicIntegersRingObj ℓ E)))
    (X : Scheme.{u}) [IsNoetherian X] (π : R) (hπ : Irreducible π)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) K)
    (hL : boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) L) :
    (∀ (n : ℕ), 1 ≤ n → IsIso (comparison R X π n K L)) ∧
      (boundedConstructible
          (condensedRingObj
            (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ 1} : Set R))) X)
          ((reduction R X π 1).obj
            (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
              (op K)).obj L)) →
        boundedConstructible (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)
          (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
            (op K)).obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralCoefficientHom
