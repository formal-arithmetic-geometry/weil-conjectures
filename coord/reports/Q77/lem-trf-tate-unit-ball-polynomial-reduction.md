## Worker report

The module `Sheaf.RingTheory.TateUnitBallPolynomialReduction` states
`RestrictedSeries.tateUnitBallPolynomialReduction`, with its only proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
All original node fields other than `lean` are unchanged.

Source read: Bosch, Lectures on Formal and Rigid Geometry (April 2008), Section 1.2,
printed p.9 / PDF p.10, the coefficient-reduction paragraph before Proposition 3:
https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf .
It identifies the reduction of the integral restricted-series ring with residue polynomials
and characterizes zero reduction by Gauss norm less than one. The node's proof supplies the
finite-coefficient argument in the stated generality without completeness or nontriviality.

Hypothesis and clause correspondence:

- The arbitrary field with its real multiplicative nonarchimedean absolute value is
  `(K : Type u) [NormedField K] [IsUltrametricDist K]`. This is the same mathematical data:
  Mathlib's `AbsoluteValue.toNormedField` equips any real absolute value with its induced
  metric, whose norm is that absolute value. `NormedField` does not require a nontrivial norm
  or completeness. The ultrametric class expresses the required maximum triangle inequality.
- `r ≥ 0` is `(r : ℕ)`, including zero.
- `V = {a : |a| ≤ 1}` is `∃ V : Subring K, (∀ a : K, a ∈ V ↔ ‖a‖ ≤ 1)`.
  A `Subring` supplies the unital subring structure, without adding a construction assumption.
- Locality is the conclusion `IsLocalRing V`.
- The ideal of elements of norm less than one is `∃ m : Ideal V,
  (∀ a : V, a ∈ m ↔ ‖(a : K)‖ < 1)`. It is maximal by `m.IsMaximal`.
  In conjunction with locality, this is the unique maximal ideal asserted in the node.
- The residue field is the actual ideal quotient `V ⧸ m`, with `IsField (V ⧸ m)`.
  `IsField` asserts field properties of the quotient's existing ring operations, rather than
  existentially selecting an unrelated field structure. The residue map is
  `Ideal.Quotient.mk m : V →+* V ⧸ m`.
- `T_r` is exactly the recorded dependency's Mathlib subring
  `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))`.
  Restrictedness at polyradius one means coefficient norms tend to zero along the cofinite
  filter. The node's Gauss supremum is Mathlib's
  `MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)`.
- `U_r` and its unital subring structure are expressed by `∃ U : Subring T_r` and the exact
  carrier equivalence `f ∈ U ↔ gaussNorm ... f.val ≤ 1`.
- The well-defined unital reduction homomorphism is `∃ red : U →+* MvPolynomial (Fin r) (V ⧸ m)`.
  It is not an unconstrained map: for EVERY `f : U` and `ν : Fin r →₀ ℕ`, the statement
  requires `∃ a : V, (a : K) = MvPowerSeries.coeff ν f.val.val ∧
  MvPolynomial.coeff ν (red f) = Ideal.Quotient.mk m a`.
  Thus each coefficient belongs to V and reduces to exactly its residue class. Since
  polynomial coefficients determine polynomials and V is a subtype, this specifies the
  intended coefficient map uniquely. The polynomial target itself enforces finite support.
- Surjectivity is `Function.Surjective red`.
- The exact kernel is the equivalence, for every `f : U`,
  `f ∈ RingHom.ker red ↔ gaussNorm ... f.val.val < 1`.
- Constants are covered for every `a : V` by `∃ f : U,
  f.val = constants K r (a : K) ∧ red f = MvPolynomial.C (Ideal.Quotient.mk m a)`.
  The equality with the dependency's constant series fixes f, so this states both its
  membership in the Gauss unit ball and its specified reduction.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, inherited by `NormedField`.
- `def-trf-restricted-series-presentation`:
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, `RestrictedSeries.constants`; its full
  source and all four recorded declarations were read. The actual restricted ring is its
  imported `MvPowerSeries.IsRestricted.subring`, Mathlib.RingTheory.MvPowerSeries.Restricted;
  Gauss norm is `MvPowerSeries.gaussNorm`, Mathlib.RingTheory.MvPowerSeries.GaussNorm.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  Mathlib.Algebra.MvPolynomial.Basic. Also read the recorded `MvPolynomial.aeval`
  (Mathlib.Algebra.MvPolynomial.Eval) and `MvPolynomial.algHom_ext` signatures/docstrings;
  this theorem uses the ring and coefficients and needs no evaluation map.
- `def-weil-pbc-algebra-hom-quotient`: Mathlib's `Ideal.Quotient.mk`, quotient ring structure,
  and ideals. Read the recorded `AlgHom`, `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`
  and ideal operations; no algebra structure beyond the underlying quotient ring is needed.
- Standard predicates `IsLocalRing`, `Ideal.IsMaximal`, and `IsField` are Mathlib's existing
  notions. No copies of these, of the closed ball, or of the reduction map are defined.

Edge cases checked before writing:

- For `r = 0`, `Fin 0 →₀ ℕ` has the single zero multi-index, and restrictedness is automatic
  on this finite index set. The statement becomes the residue homomorphism of V.
- For a trivial norm, restrictedness at threshold one forces finite support, V is K and m
  is zero. The claimed map reduces to the coefficient quotient map on polynomials and its
  kernel is zero. No `NontriviallyNormedField` constraint appears.
- The zero series and zero polynomial are included. The empty polynomial support has the
  zero lift; a coefficient of norm exactly one may have nonzero residue.
- Fields whose norm is not complete are allowed. Every coefficient product is a finite
  Cauchy sum; the uniform strict bound for the kernel uses the finite set of coefficient
  norms at least one half, not an unjustified strict supremum argument.
- Arbitrary field characteristic and universe u are retained.

Searches (2026-10-24; msearch results also logged in searches.jsonl):

- LeanFinder: "Reduction of the unit ball of restricted power series modulo coefficients
  of absolute value less than one is a polynomial ring over the residue field". Eight
  results were Weierstrass constructions and the residue field of ordinary power series;
  none is the asserted restricted-series reduction theorem.
- LeanSearch: "The reduction map of the Gauss unit ball of restricted multivariate series
  is surjective onto residue polynomials with kernel the open unit ball". Eight results
  included `IsLocalRing.residue_surjective` and `MvPolynomial.map_surjective_iff`, neither
  supplies the restricted-series map or its Gauss-kernel characterization.
- Loogle: `"AbsoluteValue", "IsNonarchimedean"`: zero hits.
- msearch grep `reduction|residue|unitBall` in Mathlib/RingTheory/MvPowerSeries: zero hits.
  Read Restricted.lean and GaussNorm.lean: they provide exactly the underlying ring/norm.
- rg `gaussNorm|IsRestricted|tateUnitBallPolynomialReduction` in `lean/WeilConjectures`
  and `lean/Sheaf`: existing presentation, comparison, and power-bounded modules use
  these notions but do not state this reduction theorem. rg of unitBall/polynomialReduction
  likewise found only unrelated coefficient/polynomial or condensed-coefficient material.
- grep of this node id in `lean/WeilConjectures`: no hits. rg of the declaration name in
  `dag/lean_names_upstream.json`: no hits.

No STATEMENT-DISPUTED issue found. The theorem has no unbound implicit variables or helper
proofs; `autoImplicit` and `relaxedAutoImplicit` are explicitly disabled. Every proof is sorry.
The full ten-step natural-language proof is in its docstring.

Validation: prescribed scompile.py compiled the module in sandbox and library modes on the
live server, exit 0, no errors or warnings (7.4 s and 1.3 s respectively).

## Second reading by Q77

Author's self-check, not an independent review; this worker was instructed not to start
another agent and the maintainer independently reviews the delivery. Re-read the full node
and the final Lean file together. V and m have exact carriers; locality plus maximality is
present; the residue field uses the actual quotient. The twice-nested `.val.val` in coefficient
and Gauss expressions correctly reaches the formal power series, whereas `f.val` in the
constant clause is the restricted series. Each coefficient clause both proves membership in
V and specifies its residue, so the existential map cannot be an unrelated surjection.
The target is `MvPolynomial (Fin r)` and all monomials are quantified. Surjectivity, the open
Gauss-ball kernel, and constants are separate conjuncts. No completeness or nontrivial-norm
assumption slipped in, and r = 0 is allowed. No mismatch or correction was found.
