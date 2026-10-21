/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Paper.AlgebraicNumberRealization
public import Sheaf.Paper.GeometricHypotheses
public import Sheaf.Paper.WeilNumbers
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import WeilConjectures.ZetaFunction.CohomologicalFamily
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.CharP.CharAndCard

import Sheaf.Algebra.Polynomial.ReciprocalPolynomial
import Sheaf.Paper.EmbeddingExtension
import WeilConjectures.ZetaFunction.Weights
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Sheaf.ZetaWeil.WeightPurityRoots
import Sheaf.Paper.SmoothProperPurityHypotheses
import Sheaf.Paper.WeilCohomologyScalarExtensionQlbar

/-!
# Arithmetic roots of the integral Frobenius factors

Source: Weil conjectures blueprint, `sec-zeta-weil/sk-thm-rh/prop-arithmetic-roots.md`,
statement and proof, main-20261015 (blueprint: prop-arithmetic-roots).

The recorded cohomological family is realized over `PadicAlgCl l`. For another chosen
closure `C.Qbar`, a coefficient isomorphism `e` expresses the same ordinary cohomology
by tensor extension, and its Frobenius is the image of the recorded Frobenius under
`ModuleCat.extendScalars e.toRingHom`. The assertion quantifies over every such `e`,
so no identification of closures is imposed as an extra hypothesis. The integral-factor
predicate uses the recorded coefficientwise equality for every prime simultaneously.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The finite-field datum gives characteristic `D.p`, by the existing cardinality criterion.
Source: blueprint `prop-arithmetic-roots.md`, finite-field setting
(blueprint: prop-arithmetic-roots). -/
instance arithmeticRootsBaseCharP (D : FiniteFieldDatum.{u}) : CharP D.k₀ D.p :=
  letI := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))

/-- The coefficient-prime instance required by the recorded cohomological family, obtained
from `C.different` and the finite-field cardinality, without any additional assumption.
Source: blueprint `prop-arithmetic-roots.md`, primes distinct from `p`
(blueprint: prop-arithmetic-roots). -/
instance arithmeticRootsCoefficientChar (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum) :
    Fact (ringChar D.k₀ ≠ C.l) :=
  ⟨fun h ↦ C.different (h.symm.trans (ringChar.eq D.k₀ D.p))⟩

/-- The reverse integral factor is monic; its roots are algebraic integers and Weil numbers
of weight `i`, and every adic realization is a reciprocal root and a Frobenius eigenvalue
on ordinary cohomology after scalar extension. Ordinary roots have weight `-i`.
Source: blueprint `sec-zeta-weil/sk-thm-rh/prop-arithmetic-roots.md`, main-20261015
(blueprint: prop-arithmetic-roots).

Proof (the seven steps of the DAG node):
1. Apply `lem-weil-reciprocal-polynomial` to `P` with constant coefficient one.
   Its reverse is precisely `U^(deg P) P(U⁻¹)`, is monic, and has nonzero constant
   coefficient. Its roots are nonzero and their inverses are the ordinary roots.
2. A reciprocal root satisfies the resulting monic integral polynomial, hence is integral
   over `ℤ`, as in `def-weil-numbers`.
3. Map this root equation through the chosen realization (`lem-weil-polynomial-root-ring-hom`).
   The integral-factor identity and the reciprocal-polynomial identity show that its image
   is a reciprocal root of the corresponding cohomological determinant factor.
4. Apply `prop-weil-reciprocal-roots-eigenvalues` to the Frobenius automorphism.
   The comparison `lem-weil-cohomology-scalar-extension-qlbar` identifies the resulting
   space with ordinary cohomology after scalar extension and intertwines Frobenius.
   Tensor extension along the coefficient isomorphism `e` gives the displayed operator.
5. `lem-weil-smooth-proper-purity-hypotheses` supplies the hypotheses of `prop-weight-purity`.
   Apply `prop-weight-purity-roots` to obtain the norm `q^(i/2)` for every realization
   and every complex isomorphism of its coefficient closure.
6. Choose a prime different from `p` and apply `lem-embedding-extension` to extend every
   embedding of `ℚ(α)` to such a complex isomorphism. This proves the intrinsic norm
   assertion and, with nonzeroness from step 1, `IsWeilNumber D α i`.
7. An ordinary root is the inverse of a reciprocal root and generates the same simple
   field. Every embedding respects inversion, so its norm is `q^(-i/2)`.
-/
theorem arithmetic_roots (D : FiniteFieldDatum.{u})
    (X₀ : Scheme.{u}) [X₀.Over (Spec (.of D.k₀))]
    [IsProper (X₀ ↘ Spec (.of D.k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (.of D.k₀))]
    (d : ℕ) (hsmooth : @FiniteFieldDatum.IsSmoothOfPureDimension D
      (Over.mk (X₀ ↘ Spec (.of D.k₀)))
      (inferInstanceAs (LocallyOfFiniteType (X₀ ↘ Spec (.of D.k₀))))
      (inferInstanceAs (QuasiCompact (X₀ ↘ Spec (.of D.k₀)))) d)
    (i : ℤ) (hi₀ : 0 ≤ i) (hi : i ≤ 2 * (d : ℤ))
    (P : Polynomial ℤ) (hP₀ : P.coeff 0 = 1)
    (hP : Scheme.IsIntegralFrobeniusFactor D.k₀ X₀ i P)
    (Qbar : Type v) [Field Qbar] [Algebra ℚ Qbar] [IsAlgClosure ℚ Qbar] :
    P.reverse.Monic ∧
      (∀ α : Qbar, (P.reverse.map (Int.castRingHom Qbar)).IsRoot α →
        IsIntegral ℤ α ∧ IsWeilNumber D α (i : ℝ) ∧
          ∀ (C : D.CoefficientDatum)
            (e : PadicAlgCl C.l ≃ₐ[Padic C.l] C.Qbar)
            (j : C.AlgebraicNumberRealization D Qbar),
            ((AlgEquiv.toEquiv j) α : C.Qbar) ≠ 0 ∧
              ((Scheme.frobeniusCharpolyRev D.k₀ C.l X₀ i).map e.toRingHom).IsRoot
                ((AlgEquiv.toEquiv j) α : C.Qbar)⁻¹ ∧
              Module.End.HasEigenvalue
                (((ModuleCat.extendScalars e.toRingHom).map
                  (ModuleCat.ofHom
                    (WeilSheaf.ordinaryCompactWeilSheafCohomology
                      (WeilSheaf.adicConstant D.k₀ C.l X₀) i).1.frobeniusEnd)).hom)
                ((AlgEquiv.toEquiv j) α : C.Qbar)) ∧
      ∀ β : Qbar, (P.map (Int.castRingHom Qbar)).IsRoot β →
        ∀ τ : IntermediateField.adjoin ℚ ({β} : Set Qbar) →+* ℂ,
          ‖τ (IntermediateField.AdjoinSimple.gen ℚ β)‖ =
            (D.q : ℝ) ^ (-(i : ℝ) / 2) := by
  sorry

end WeilConjectures
