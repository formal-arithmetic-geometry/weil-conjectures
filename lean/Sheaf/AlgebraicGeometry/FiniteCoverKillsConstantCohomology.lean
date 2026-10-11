/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Finite covers kill classes with finite constant coefficients

Source: Stacks Project, Lemma 59.80.9 (Tag 09ZD), part (2)
(blueprint: lem-weil-pbc-integral-cover-kills-constant-cohomology).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Stacks Project, Lemma 59.80.9 (Tag 09ZD), part (2)
(blueprint: lem-weil-pbc-integral-cover-kills-constant-cohomology).
A positive-degree class with finite constant abelian coefficients on a closed subscheme
of an affine scheme dies after base change to a finite surjective cover of finite presentation.
The constant-sheaf comparison identifies the inverse-image coefficients with the constant
sheaf on the fibre product.

Proof:
1. Apply `lem-weil-pbc-integral-cover-trivial-cohomology` (09ZD (1)) to obtain an integral
   surjective cover whose every closed subscheme has zero positive constant cohomology.
2. The base change of the closed immersion is closed
   (`lem-weil-pbc-closed-immersion-base-change`), so the class dies there. Identify the
   coefficients using `lemma-constructible-pullback-constant`; cohomology respects this
   identification by `lem-weil-pbc-cohomology-pullback-functorial`.
3. Write the integral cover as a nonempty directed limit of finite finitely presented covers
   by `lem-weil-pbc-integral-morphism-limit-of-finite` (09YZ). They are affine by
   `lem-weil-pbc-finite-morphism-permanence`; use `lem-weil-pbc-qcqs-over-affine` and
   `lem-weil-pbc-spec-colimit-limit` to identify the cover with the spectrum of the colimit
   of their rings (`def-weil-pbc-category-colimit`, `def-weil-affine-spectrum`).
4. Write the closed subscheme as Spec B for a quotient A → B. Base change is tensor product
   (`lem-weil-pbc-fibre-product-affine-spectra`), and the base-changed rings have the correct
   colimit by `lem-weil-pbc-filtered-colimit-tensor-varying-rings`.
5. Apply `lem-weil-pbc-etale-cohomology-limit-of-schemes` (03Q6/09YQ) to this ring system.
   Pullback functoriality makes the finite-stage classes compatible with the limit class.
6. The limit class is zero, hence a finite-stage class is zero by
   `def-weil-directed-colimit-abelian-groups`. Transport it back to the fibre product using
   `lem-weil-pbc-cohomology-pullback-functorial`.
7. That stage is finite and finitely presented; it is surjective because the integral
   surjective cover factors through it. It is the required cover. -/
theorem exists_isFinite_surjective_constant_cohomology_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AddCommGrpCat.{u + 1}) [Finite M] (q : ℕ) (hq : 1 ≤ q)
    (ξ : Sheaf.H ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsFinite f ∧ Surjective f ∧ LocallyOfFinitePresentation f ∧
        Sheaf.H.map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
            (pullback.snd f i)).hom.app M) q
          (cohomologyMap (pullback.snd f i)
            ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q ξ) = 0 := by
  sorry

end AlgebraicGeometry.Etale
