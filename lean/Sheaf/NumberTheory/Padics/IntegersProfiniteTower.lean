/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# The profinite tower of the integers in a finite p-adic extension

Source: blueprint main-20261015, `sk-prop-sfb-qlbar-colimit-x-integral-limit`, clause 1;
Stacks Project, Tags 08ZU, 0ET8, 08ZY and 08ZZ
(blueprint: lem-sfb-integers-profinite-tower).

## Main definitions and statements

* `Padic.coefficientExtensionPositiveLimit`: compatible families at exponents `n + 1`.
* `Padic.coefficientExtensionIntegersTopology`: the absolute-value subspace topology.
* `Padic.coefficientExtensionPositiveLimitTopology`: the discrete-product subspace topology.
* `Padic.coefficientExtension_integers_profinite_tower`: the canonical ring and topological
  identification, profiniteness, and eventual unique factorization through finite levels.
-/

@[expose] public section

universe u v

namespace Padic

/-- The compatible-family subring of the positive coefficient levels. Coordinate `n` is
the quotient at exponent `n + 1`; equalizers impose precisely the successive reductions.
Ring operations are inherited coordinatewise from the product.

Source: blueprint main-20261015, integral-limit clause 1; Stacks Tag 08ZY
(blueprint: lem-sfb-integers-profinite-tower). -/
noncomputable def coefficientExtensionPositiveLimit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Subring (∀ n : ℕ, coefficientExtensionRing l E (n + 1)) :=
  ⨅ n : ℕ, RingHom.eqLocus
    ((coefficientExtensionTransition l E (n + 1)).comp
      (Pi.evalRingHom (fun k : ℕ ↦ coefficientExtensionRing l E (k + 1)) (n + 1)))
    (Pi.evalRingHom (fun k : ℕ ↦ coefficientExtensionRing l E (k + 1)) n)

/-- The topology on the integers induced from the spectral absolute value on `E`.
This is the extending absolute value recorded by the coefficient-extension dependency.

Source: blueprint main-20261015, integral-limit clause 1
(blueprint: lem-sfb-integers-profinite-tower). -/
@[instance_reducible]
noncomputable def coefficientExtensionIntegersTopology (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    TopologicalSpace (coefficientExtensionIntegers l E) :=
  letI := spectralNorm.normedField (Padic l) E
  TopologicalSpace.induced (fun x : coefficientExtensionIntegers l E ↦ (x : E))
    inferInstance

/-- The subspace topology from the product of the discrete positive coefficient rings.

Source: blueprint main-20261015, integral-limit clause 1; Stacks Tag 08ZY
(blueprint: lem-sfb-integers-profinite-tower). -/
@[instance_reducible]
noncomputable def coefficientExtensionPositiveLimitTopology (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    TopologicalSpace (coefficientExtensionPositiveLimit l E) :=
  TopologicalSpace.induced
    (fun b : coefficientExtensionPositiveLimit l E ↦ b.val)
    (@Pi.topologicalSpace ℕ (fun n ↦ coefficientExtensionRing l E (n + 1)) (fun _ ↦ ⊥))

/-- The reductions identify the integers with their profinite tower as rings and spaces.
They are compact, Hausdorff and totally disconnected. Every continuous surjection to
a finite discrete set factors uniquely through every sufficiently high positive level.

Source: blueprint main-20261015, `sk-prop-sfb-qlbar-colimit-x-integral-limit`, clause 1;
Stacks Tags 08ZU, 0ET8, 08ZY and 08ZZ
(blueprint: lem-sfb-integers-profinite-tower).

Proof: (1) By lem-weil-l-adic-extension-integers-dvr the uniformizer has absolute value
`r` with `0 < r < 1`, and units have value one. Nonarchimedeanness from
lem-weil-l-adic-extension-absolute-value gives membership in its nth ideal power exactly
when the absolute value is at most `r ^ n`. These cosets are clopen and form a neighbourhood
basis. Lem-weil-valued-dvr-finite-quotients supplies finite quotients and surjective
transitions. (2) Compatible reductions define a ring homomorphism. If two elements have
the same reductions, their difference has value at most every `r ^ n`, hence is zero.
(3) Representatives of a compatible family are Cauchy by the same estimate. Completeness
from lem-weil-l-adic-extension-complete gives a limit in the closed unit ball. Each of
its reductions is the specified coordinate. This proves surjectivity and hence the ring
isomorphism. (4) Coordinate cylinders form a basis on the inverse limit: dominate the
finitely many restricted coordinates by their maximum. Their inverse images are exactly
the coset basis, proving continuity in both directions. (5) Properness from
lem-weil-l-adic-extension-proper makes the closed unit ball compact. (6) The metric is
Hausdorff; distinct points have distinct reductions, so a clopen coset separates them.
Thus every connected subset has at most one point. (7) The open fibres of the finite discrete
map contain coset neighbourhoods. Compactness gives finitely many of them covering the
integers. Their maximum exponent ensures that the map is constant on every coset at
that level, defining its factorization. The cover is nonempty since it covers zero.
(8) Surjectivity of reduction makes the factor unique. Composing with reduction from
any higher level gives its factorization there, again unique by surjectivity.
-/
theorem coefficientExtension_integers_profinite_tower (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∃ e : coefficientExtensionIntegers l E ≃+* coefficientExtensionPositiveLimit l E,
      (∀ (x : coefficientExtensionIntegers l E) (n : ℕ),
        (e x).val n = Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) x) ∧
      @IsHomeomorph _ _ (coefficientExtensionIntegersTopology l E)
        (coefficientExtensionPositiveLimitTopology l E) e) ∧
    @CompactSpace _ (coefficientExtensionIntegersTopology l E) ∧
    @T2Space _ (coefficientExtensionIntegersTopology l E) ∧
    @TotallyDisconnectedSpace _ (coefficientExtensionIntegersTopology l E) ∧
    (∀ (Q : Type v) [Finite Q] (g : coefficientExtensionIntegers l E → Q),
      @Continuous _ _ (coefficientExtensionIntegersTopology l E) ⊥ g →
      Function.Surjective g →
      ∃ n : ℕ, 1 ≤ n ∧ ∀ m : ℕ, n ≤ m →
        ∃! h : coefficientExtensionRing l E m → Q,
          g = h ∘ Ideal.Quotient.mk (coefficientExtensionIdeal l E m)) := by
  sorry

end Padic
