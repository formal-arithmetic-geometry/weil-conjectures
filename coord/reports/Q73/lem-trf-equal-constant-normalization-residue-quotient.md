## Worker report

The module `Sheaf.RingTheory.EqualConstantNormalizationResidueQuotient` states
`RingTheory.equalConstant_normalization_residue_quotient`, with its single proof `sorry`.
It gives all clauses of the equal-constant normalization and residue-quotient lemma.
There are no definitions with postponed data, new nodes, dependency repairs, or statement changes.

Source read: `literature/stacks-project/curves.tex`, lemma-2-branches-delta-1
(Stacks Tag 0C4A), Case I and the subsequent by-hand delta calculation.
The node expands that by-hand calculation over an arbitrary field, rather than
assuming the field algebraically closed or the equal-constant ring a domain.

Hypotheses and clauses, matched individually:

- Field k: `(k : Type u) [Field k]`, with the universe explicitly bound.
- P is `PowerSeries k × PowerSeries k`; `PowerSeries` is definitionally
  `MvPowerSeries Unit k`, the recorded one-variable convention of the power-series dependency.
- L is `LaurentSeries k × LaurentSeries k`. The embedding of P in L is
  `RingHom.prodMap (HahnSeries.ofPowerSeries ℤ k) (HahnSeries.ofPowerSeries ℤ k)`.
  The embedding of S is its composite with `S.subtype`.
- S is named by `(S : Subring P)` and `hS`, its exact membership equivalence
  `p ∈ S ↔ constantCoeff p.1 = constantCoeff p.2`. This merely names the
  subring in the node, with no further assumption. It always exists, as the existing
  `RingHom.eqLocus` of constant-coefficient evaluation composed with the two projections.
- The integral closure equals P: for every `z : L`, the composite embedding's
  `RingHom.IsIntegralElem z` is equivalent to membership in the image of the top
  subring of P under the coordinatewise Laurent embedding. `IsIntegralElem` is
  exactly existence of a monic polynomial with zero `Polynomial.eval₂`; the recorded
  `IsIntegral` is its algebra-map specialization and `integralClosure` has this carrier.
  This elementwise assertion is equality of the two subrings, without requiring an
  extra algebra structure as an assumption or conflating a ring with its image in L.
- Epsilon is `(1, 0) : P`. The displayed square equation is epsilon squared equals epsilon.
- `P = S + S epsilon`: the clause `∀ p : P, ∃ s t : S, p = s.val + t.val * (1,0)`.
- `P = S[epsilon]`: `Algebra.adjoin S ({(1,0)} : Set P) = ⊤`, for the
  inherited subring algebra action.
- Locality: `IsLocalRing S` is a conclusion, not a hypothesis.
- The specified maximal ideal: the existential `m : Ideal S` is characterized by
  membership iff BOTH constant coefficients vanish. `m.IsMaximal` and the clause
  `∀ I : Ideal S, I.IsMaximal → I = m` give existence and uniqueness of the maximal ideal.
- The residue map: `c : S →+* k` has both formulas `c s = constantCoeff s.val.1`
  and `c s = constantCoeff s.val.2`, is surjective, and has kernel m. The quotient
  ring equivalence `ρ : (S ⧸ m) ≃+* k` is specified by `ρ (mk m s) = c s`.
- The S-module structure on k: an existential `Module S k` is required to have
  exactly `s • a = c s * a`. It is provided in the conclusion, never hypothesized.
- The difference map: the existential linear map `d : P →ₗ[S] k` satisfies
  `d p = constantCoeff p.1 - constantCoeff p.2` for EVERY pair, and is surjective.
- Kernel S: `LinearMap.ker d = Submodule.span S (S : Set P)`. This span is
  precisely S as a set: S is additive and closed under its own multiplication,
  and the inherited scalar multiplication is coordinatewise multiplication by S.
  Thus this is the exact kernel, not an uncharacterized auxiliary submodule.
- Induced S-linear quotient isomorphism: `e : (P ⧸ Submodule.span S (S : Set P)) ≃ₗ[S] k`
  with `e (Submodule.Quotient.mk p) = d p` on EVERY representative.
- Annihilation: for every `s ∈ m` and every quotient element q, `s • q = 0`.
- The action over S/m: an existential module structure on the SAME quotient is
  specified by `(Ideal.Quotient.mk m s) • q = s • q`, so it is the induced action.
- Freeness, rank one, and the named basis: the `Module.Basis (Fin 1) (S ⧸ m)`
  of that quotient satisfies `b 0 = Submodule.Quotient.mk (1,0)`. A one-element
  basis is exactly the asserted free rank-one statement, including its generator.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (direct public import).
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic` (direct public import), through its
  one-variable abbreviation `PowerSeries`, `Mathlib.RingTheory.PowerSeries.Basic`.
- `def-weil-pbc-laurent-series`: `LaurentSeries`, `Mathlib.RingTheory.LaurentSeries`;
  `HahnSeries.ofPowerSeries`, `HahnSeries.ofPowerSeries_injective`, and
  `HahnSeries.order` were read in HahnSeries/PowerSeries and HahnSeries/Basic.
- `def-weil-pbc-integral-closure`: `integralClosure` and `IsIntegral` were read
  in the recorded modules; `RingHom.IsIntegralElem` is the underlying defining
  predicate and is used along the actual inclusion. The recorded
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` is directly publicly imported.
- Proof-only dependency `lem-weil-pbc-power-series-local-ring`:
  `MvPowerSeries.isUnit_iff_constantCoeff` and the local-ring instance in
  `Mathlib.RingTheory.MvPowerSeries.Inverse`, imported with plain `import`.
- Other standard interfaces are Mathlib's `Algebra.adjoin`, `Ideal`, `IsLocalRing`,
  `LinearMap`, `Submodule.span`, quotient modules, and `Module.Basis`.

Edge cases checked before writing: characteristic two (difference still has kernel
exactly equality, and d(epsilon)=1); the zero pair; pairs with one coordinate zero;
equal nonzero common constant (both inverses have equal inverse constants);
zero common constant (cannot be a unit); Laurent elements of negative order,
including order -1 and degree-one monic equations; arbitrarily large fields.
The zero ring is excluded by exactly the field assumption of the node. No
separability, algebraic closure, Noetherian, or domain hypothesis is imposed on S.
The annihilation and basis clauses concern the additive module quotient, not an
invalid ring quotient by the subring S.

Searches for an existing statement:

- `msearch.py ... leanfinder "integral closure of pairs of power series with equal
  constant coefficients is their product and quotient is the residue field"`:
  eight hits about Weierstrass preparation and `PowerSeries.residueFieldOfPowerSeries`;
  none gives the equal-constant product normalization and quotient statement.
- `msearch.py ... loogle "PowerSeries, integralClosure"`: no hits.
- `msearch.py ... grep "equal.constant|constantCoeff.*quotient|integralClosure.*PowerSeries"`:
  no hits in Mathlib.
- `msearch.py ... leansearch "integral closure equal constant pairs power series
  normalization residue quotient"`: generic integralClosure/completeIntegralClosure
  and the residue field of one power-series ring; none is this statement.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for equal-constant names,
  the item ID, and constant-coefficient pair predicates, plus the prescribed
  `grep -rn` for the item ID in WeilConjectures: no exact statement. Related
  `NodalNormalizationQuotient`, `RelativeNodalPointPinching`, `NodalIdealScalarGluing`,
  `MarkedNodalInfinitesimalFields` and `NodalCompletedResidueDenominators` were read.
  They mention the calculation in proofs or state results about curves; the last
  module has only a rational-field counterexample containing a related subring,
  not this arbitrary-field statement. The upstream name index likewise has no match.

Validation: the prescribed `scompile.py Q73 ... <module>` succeeds against current
server sources. An earlier elaboration exposed two different inherited product
module instances for a bottom-subalgebra quotient; using the ordinary span of S
in the existing product module removed that ambiguity without changing objects or
hypotheses. The final integral-closure clause uses the ring-map predicate, avoiding
an unnecessary separately inferred algebra structure. All variables are explicitly
bound, no diagnostic commands remain, and the only proof is the expected `sorry`.

## Second reading by Q73

This is an author's second pass, not a claim of independent review; the dispatcher
explicitly prohibits starting another agent, and the maintainer supplies the
independent review. On rereading the complete node and module, I checked the
ambient Laurent embedding, both equal-constant and zero-constant conditions, both
generation statements, existence and uniqueness of the maximal ideal, the two
residue formulas, the specified S-action on k, the difference map on all P,
the quotient representative equation, and the descended S/m action with the
one-element basis. No clause is omitted and no statement correction is needed.
The span is exactly the original S, not a different quotient. Both existential
module structures are pinned down by action formulas, and both equivalences are
pinned down on all representatives; they are not arbitrary replacement maps.
