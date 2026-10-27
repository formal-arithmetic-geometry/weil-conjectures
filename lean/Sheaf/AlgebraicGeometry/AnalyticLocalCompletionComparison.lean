/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.SmoothAnalytificationCotangent
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.AlgebraicGeometry.EtaleChartRationalPointTaylorIso
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Algebraic and analytic local completion comparison

Source: Serre, GAGA, no. 6, Proposition 3, pp. 9--10, and the exactness input to
no. 9, Proposition 10; analytic Noetherianity by Weierstrass division
(blueprint: lem-sfb-analytic-local-completion-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.SmoothAnalytic

/-- Algebraic and holomorphic stalks at a smooth complex point are Noetherian local
rings. The regular-to-holomorphic stalk map is local and induces an isomorphism
of their maximal-ideal-adic completions. The isomorphism is specified on every
positive quotient level by the quotient map induced by that very stalk map,
and commutes with the two canonical maps from the algebraic local ring.
The algebraic stalk's local-ring instance is the existing scheme-stalk instance.

Source: Serre, GAGA, no. 6, Proposition 3, pp. 9--10; Bruhat, Cartan seminar
1951--52, exp. 11, section 2, Theorem 2; Stacks Tags 00FN, 054L, 039M
(blueprint: lem-sfb-analytic-local-completion-comparison).

Proof plan (the node's eight steps):
1. Use lem-trf-affine-chart-stalk-differentials to identify the algebraic stalk
   with a localization of a finitely presented complex algebra. Apply
   lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-localization-noetherian.
   The complex point gives residue field C and the stalk is local by
   def-weil-pbc-localization-at-prime.
2. Choose an etale chart by sbc-thm-etale-local-normal-form and
   lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension. Use
   lem-weil-pbc-etale-ring-map-iff-etale-affine,
   lem-trf-formally-etale-differentials-base-change and
   lem-weil-pbc-polynomial-ring-kahler-basis to obtain the coordinate differential frame.
3. The cotangent comparison lem-sfb-smooth-analytification-cotangent identifies
   that frame analytically. Apply lem-sfb-complex-analytic-inverse-toolkit and
   lem-sfb-complex-analytic-function-operations to identify the analytic stalk
   with holomorphic germs at the origin, taking centered coordinates to coordinate germs.
4. Induct on dimension using lem-sfb-holomorphic-weierstrass-division. A nonzero
   element of an ideal becomes regular in the last variable after a linear change.
   Remainders in that ideal form a submodule of a finite free module over the
   lower-dimensional germ ring. By lem-weil-pbc-noetherian-submodule-finite they
   have finitely many generators; division shows these together with the selected
   element generate the ideal. Dimension zero is C; order-zero division has no remainder.
5. Evaluation identifies the analytic maximal ideal with germs vanishing at the point:
   a germ with nonzero value has holomorphic reciprocal. Evaluation commutes with
   the regular-germ map, proving the maximal-ideal preimage equality and all its powers.
6. By lem-sfb-holomorphic-germ-taylor-jets, the analytic quotients are polynomial
   Taylor jets. Taking compatible truncations identifies the analytic completion
   with the multivariate formal power series ring of
   def-weil-pbc-multivariate-power-series. Coefficients recover the inverse map.
7. Apply lem-trf-etale-chart-rational-point-taylor-iso to the same etale chart and
   residue field C. It identifies the algebraic completion with the same series ring,
   with each quotient component given by evaluation in the actual centered coordinates.
8. Compare those two Taylor expansions at every positive exponent. Applying the
   stalk map to the algebraic truncation gives exactly the analytic truncation,
   hence the induced completion map is the composite of the two Taylor isomorphisms.
   Constant compatible sequences give the final square. No variables are needed
   in dimension zero, and an empty analytification has no point to check. -/
theorem exists_analyticLocalCompletionComparison {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ)))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f]
    (D : Data f) (a : D.space) :
    IsNoetherianRing (X.presheaf.stalk (D.pi.hom.base a)) ∧
    IsNoetherianRing (D.space.presheaf.stalk a) ∧
    ∃ hB : IsLocalRing (D.space.presheaf.stalk a),
      ∃ hlocal : Ideal.comap (D.pi.hom.stalkMap a).hom
          (@IsLocalRing.maximalIdeal (D.space.presheaf.stalk a) _ hB) =
            IsLocalRing.maximalIdeal (X.presheaf.stalk (D.pi.hom.base a)),
        ∃ e : AdicCompletion
            (IsLocalRing.maximalIdeal (X.presheaf.stalk (D.pi.hom.base a)))
            (X.presheaf.stalk (D.pi.hom.base a)) ≃+*
          AdicCompletion (@IsLocalRing.maximalIdeal (D.space.presheaf.stalk a) _ hB)
            (D.space.presheaf.stalk a),
          (∀ (r : ℕ), 1 ≤ r → ∀ z : AdicCompletion
              (IsLocalRing.maximalIdeal (X.presheaf.stalk (D.pi.hom.base a)))
              (X.presheaf.stalk (D.pi.hom.base a)),
            AdicCompletion.evalₐ
                (@IsLocalRing.maximalIdeal (D.space.presheaf.stalk a) _ hB) r (e z) =
              Ideal.quotientMap
                (@IsLocalRing.maximalIdeal (D.space.presheaf.stalk a) _ hB ^ r)
                (D.pi.hom.stalkMap a).hom
                ((pow_le_pow_left' hlocal.ge r).trans
                  (Ideal.le_comap_pow (D.pi.hom.stalkMap a).hom r))
                (AdicCompletion.evalₐ
                  (IsLocalRing.maximalIdeal (X.presheaf.stalk (D.pi.hom.base a))) r z)) ∧
          (∀ b : X.presheaf.stalk (D.pi.hom.base a),
            e (algebraMap _ _ b) = algebraMap _ _ ((D.pi.hom.stalkMap a).hom b)) := by
  sorry

end AlgebraicGeometry.SmoothAnalytic
