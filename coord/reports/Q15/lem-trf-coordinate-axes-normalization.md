## Worker report

The module `Sheaf.RingTheory.CoordinateAxesNormalization` states
`AlgebraicGeometry.coordinate_axes_normalization`, with exactly one postponed theorem.
Its eight auxiliary definitions construct the specific maps, ideal, subalgebra and
parameter used in the node; every definition has real data. No new independent notion,
new definition node, dependency repair or statement correction is needed.

Hypothesis and clause correspondence, reading the node and source alongside the file:

- The field is `(k : Type u) [Field k]`, for arbitrary explicit universe `u`.
  The integer number of branches is `(b : ℕ) (hb : 1 ≤ b)`.
- `D` is `Fin b → PowerSeries k`, using the dependency's approved univariate
  specialization. `A` is `MvPowerSeries (Fin b) k`.
- `rho` is `coordinateAxesConstants k b`, the product of the constant-coefficient
  ring homomorphisms, bundled as a k-algebra homomorphism. The diagonal k is
  `(⊥ : Subalgebra k (Fin b → k))`, the image of the scalar map. `P` is its
  `Subalgebra.comap`, namely `coordinateAxesSubalgebra k b`; its algebra structure
  and its inclusion in D are inherited from that subalgebra, with no chosen structure.
- Evaluation on the separate axes is `coordinateAxesEvaluation k b`, built with
  `MvPowerSeries.killCompl` for the embedding `Unit ↪ Fin b` selecting each axis,
  then `AlgHom.pi`. Thus the coordinate series has coefficient `a_(n e_i)`.
  The first conclusion gives its `AlgHom.range = P`, and the second gives its
  `RingHom.ker = coordinateAxesMixedIdeal k b`, the actual algebraic `Ideal.span`
  of the finitely indexed generators `X i * X j` with `i < j`, not a closed ideal.
- `R_b` reuses `AlgebraicGeometry.ordinaryMultiplePointRing k b`, whose definition
  is exactly the quotient by all unequal-pair mixed monomials. The conclusion
  `∃ e : ordinaryMultiplePointRing k b ≃ₐ[k] P` includes its value on every quotient
  representative, so this is precisely the isomorphism induced by evaluation.
  The already-landed node `def-trf-ordinary-multiple-point` is added to `stmt_deps`
  solely to cite this existing definition. No second copy of this quotient is made.
- Reduced and Noetherian are `_root_.IsReduced P` and `IsNoetherianRing P`.
  Locality is an existential `hlocal : IsLocalRing P`, allowing the same conclusion
  to identify `@IsLocalRing.maximalIdeal P _ hlocal` with the kernel of rho
  restricted to P. The common-constant map `coordinateAxesResidue k b hb` reads
  the first coordinate; its kernel is asserted equal to that same kernel. The
  displayed k-algebra equivalence of its quotient with k is characterized by
  `e [p] = coordinateAxesResidue k b hb p`. This expresses the specified residue
  field together with the canonical map, rather than an arbitrary field isomorphism.
- The coordinate idempotent `e_i` is `Pi.single i 1`. For every d the conclusion
  supplies `p : Fin b → P` with `d = ∑ i, (p i).val * Pi.single i 1`.
  `Module.Finite P D` separately records the stated finiteness as a P-module.
- The tuple s is the actual element `coordinateAxesParameter k b`, with every
  coordinate `PowerSeries.X`; membership in P is verified using zero constants.
  Its membership in `nonZeroDivisors P` states regularity. The next universal
  clause is exactly `s.val * d ∈ P`, expressing `sD ⊆ P`.
- Write F for `Fin b → FractionRing (PowerSeries k)`. The concrete map
  `coordinateAxesFractionMap` embeds D coordinatewise using the canonical
  fraction maps, and `coordinateAxesSubalgebraFractionMap` composes with P's
  inclusion. The three conclusions `IsFractionRing P F`,
  `IsLocalization.Away s F` over P, and `IsLocalization.Away s.val F` over D
  each explicitly supply the algebra structure induced by the appropriate map.
  By the definition of these Mathlib predicates this states exactly that the
  SAME canonically embedded F is Q(P), P[1/s], and D[1/s]. In particular,
  `IsFractionRing` localizes at all non-zero-divisors and does not require P to
  be a domain. This avoids false literal type equalities between localization
  constructions while retaining the canonical identifications and scalar actions.
- `(@integralClosure P F ... canonicalAlgebra).carrier = Set.range
  (coordinateAxesFractionMap k b)` identifies the integral closure inside this
  very fraction ring with the canonical image of D, not an arbitrary equivalent
  ring. Here the `integralClosure` is the exact recorded Mathlib declaration.
- The displayed `LinearEquiv` is between `D ⧸ P.toSubmodule` and
  `k^b ⧸ diagonal.toSubmodule`. Its values on every class `[d]` are asserted
  equal to `[rho d]`. The following universal clause expresses compatibility
  with multiplication by every p in P as scalar multiplication by its common
  residue `coordinateAxesResidue ... p`. Thus the P-action through k is
  specified without inventing an extra arbitrary module structure.
- The next conclusion is exactly `Module.finrank k (D ⧸ P.toSubmodule) = b - 1`.
  The final clause says that every p in the residue kernel kills every class [d],
  using `[p.val * d] = 0`. Since quotient classes have representatives, this is
  the stated annihilation by the maximal ideal, already identified above.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic`, and the recorded `PowerSeries`
  specialization, `Mathlib.RingTheory.PowerSeries.Basic`.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (carrier is `IsIntegral`).
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom`,
  `Mathlib.Algebra.Algebra.Hom`; the quotient algebra and quotient map from
  `Mathlib.RingTheory.Ideal.Quotient.Operations`.
- Added landed dependency `def-trf-ordinary-multiple-point`:
  `AlgebraicGeometry.ordinaryMultiplePointRing`,
  `Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint`. The full definition and
  docstring were read before using it.
- Proof dependency imports: `Mathlib.RingTheory.MvPowerSeries.Equiv`
  (`MvPowerSeries.isNoetherianRing`), `Mathlib.RingTheory.MvPowerSeries.Inverse`
  (`MvPowerSeries.isUnit_iff_constantCoeff`, local-ring instance), and
  `WeilConjectures.RingTheory.PowerSeriesNormalDomain`
  (`PowerSeries.noetherian_normal_domain`). The power-series domain instances
  are already public through the statement imports. The normal-domain notion
  uses the recorded Mathlib `IsDomain` and `IsIntegrallyClosed` conventions.

Edge cases checked mathematically: b=1 has no mixed generators, P=D=k[[t]],
all three fraction-ring identifications are k((t)), and both quotient vector
spaces are zero of dimension 0. b=2 gives the usual equal-constant nodal ring
and one-dimensional residue quotient. b=0 is excluded by the actual hypothesis;
only the residue definition needs that bound. Arbitrary field characteristic,
finite fields and non-algebraically-closed fields require no extra assumption.
The tuple s is regular despite P having zero divisors when b>1. Integral closure
is in the total ring, not a nonexistent field of fractions of a reducible ring.
The mixed ideal is the ordinary finitely generated ideal, including infinite
input series; the docstring carries the coefficientwise grouping proof.

Searches (2026-10-24):

- `msearch.py ... leansearch "coordinate axes formal power series ring normalization
  equal constant coefficients"`: 8 hits, including `PowerSeries.ext`,
  `MvPowerSeries.coeff_zero_eq_constantCoeff`, `PowerSeries.ker_coeff_eq_max_ideal`;
  none states the node.
- `msearch.py ... leanfinder "The coordinate axes power series quotient is the equal
  constant subring of a product, its normalization and total quotient ring"`:
  8 hits, including `PowerSeries.idealX`, Weierstrass quotient equivalences,
  `PowerSeries.span_X_isPrime`, `LaurentSeries.powerSeries_ext_subring`;
  none covers this finite-product equal-constant statement.
- `msearch.py ... loogle "MvPowerSeries, PowerSeries, constantCoeff"`: 0 hits;
  service says `constantCoeff` is an unknown unqualified identifier. Direct source
  inspection instead found the qualified maps and `MvPowerSeries.killCompl`.
- `msearch.py ... grep "(multicross|coordinate.?axes|equal.?constant)" RingTheory`:
  0 hits in Mathlib. Direct rg of `MvPowerSeries` and `PowerSeries` found
  `killCompl` in Rename.lean and the basic constant-coefficient maps.
- `rg -n "(coordinateAxes|coordinate.axes|multicross|equalConstant|equal.constant)"`
  over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing complete statement. Existing nodal modules discuss the two-axis
  case in proofs; `OrdinaryMultiplePoint.lean` owns exactly the quotient ring and
  is reused. `OrdinaryPointDeltaBranches.lean` mentions the calculation in its
  proof but its theorem concerns geometric delta invariants, not this ring result.
- `grep -rn "lem-trf-coordinate-axes-normalization" lean/WeilConjectures`:
  no attached upstream declaration.
- Direct rg for every proposed full-name suffix in Mathlib, WeilConjectures,
  Sheaf and the upstream-name index: no declaration clashes.

Source read: `literature/stacks-project/curves.tex`, equation-multicross and
its following paragraph before lemma-multicross-algebra (Tags 0C1U/0C1V).
No statement fault or `STATEMENT-DISPUTED` issue was found.

Validation: prescribed scompile.py compiles both the sandbox and final module
cleanly (5.9 s and 4.6 s). All variables and universes are explicit; no diagnostic
commands or local notation remain. The only theorem proof is `sorry`, and its
source docstring contains the node's complete ten-step natural-language proof.

## Second reading by Q15

This is a second self-reading, not a claim of an independent worker review:
the dispatcher's explicit instruction prohibits starting other agents. The
maintainer's independent review is still required. I reopened the node, the
source equation and the compiled module, and matched every clause as above.

The second reading checked in particular that the existing quotient uses all
unequal pairs while the kernel uses increasing pairs; the evaluation compatibility
uses the existing quotient and is mathematically identical by commutativity.
It checked that the residue isomorphism is characterized on representatives,
that the integral closure uses the explicitly embedded P-algebra structure,
and that all three fraction-ring statements use the same concrete ambient ring.
It also checked the actual scalar action in the quotient compatibility and that
annihilation concerns every quotient representative. No hypothesis or clause
was lost. Early elaboration errors were repaired by making the PowerSeries import
public, qualifying ring `IsReduced`, and using the explicit integral-closure
carrier rather than allowing Lean to infer a different algebra structure.
