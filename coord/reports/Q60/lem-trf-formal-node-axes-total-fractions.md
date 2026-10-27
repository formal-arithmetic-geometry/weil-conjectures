## Worker report

The module `Sheaf.RingTheory.FormalNodeAxesTotalFractions` states
`MvPowerSeries.formalNode_axes_totalFractions`, with its proof postponed by `sorry`.
Its five auxiliary declarations construct the objects and canonical maps of this node;
no data is postponed. No statement correction, dependency repair, or new DAG node is needed.
The only changed field of the existing node is `lean`.

Source read: `literature/stacks-project/curves.tex`, Tag 0C4A,
`lemma-2-branches-delta-1`, proof of (1) implies (2), Case I, q = xy.
This is the explicit algebra expanded in the accepted five-step proof of the item.
The source calls the branch-product normalization a calculation; the delivered theorem
states the axis and fraction calculation rather than adding the geometric hypotheses
of the surrounding lemma.

Hypotheses and clauses, in the order of the node:

- The arbitrary field k is `(k : Type u) [Field k]`, with `universe u` explicit.
  There is no characteristic or cardinality restriction.
- T = k[[u,v]] is `MvPowerSeries (Fin 2) k`; u and v are `X 0` and `X 1`.
  `formalNodeIdeal k` is literally `Ideal.span {X 0 * X 1}`.
  `FormalNodeRing k` is the Mathlib ideal quotient by that ideal, with its inherited
  k-algebra structure. This is an abbreviation, not a replacement quotient construction.
- P is `PowerSeries k × PowerSeries k`. Mathlib's `PowerSeries k` is exactly
  `MvPowerSeries Unit k`, with the standard coefficientwise and Cauchy operations.
- S is `formalNodeAxesSubalgebra k`. It is `AlgHom.equalizer` of the two constant
  coefficient maps composed with the two projections. Its carrier is exactly the
  pairs whose constant coefficients are equal. All ring and algebra operations
  come from Mathlib's subalgebra equalizer, so the ring structure is the induced one.
  The constant coefficient maps use `PowerSeries.constantCoeff` and the existing
  proof `PowerSeries.constantCoeff_C` of their compatibility with constants.
- The canonical axis map is the real definition `formalNodeAxisMap k`:
  `MvPowerSeries.killCompl` for the embedding of Unit onto 0, paired with the
  analogous map onto 1. The first map preserves precisely the u-axis coefficients
  and kills all terms containing v; the second does the opposite. The coefficient
  formula is Mathlib's `coeff_killCompl`, not a choice of an unspecified map.
- The first conjunction asserts `RingHom.ker ... = formalNodeIdeal k`.
  The second asserts `Set.range ... = (formalNodeAxesSubalgebra k : Set P)`.
- `∃ e : FormalNodeRing k ≃ₐ[k] formalNodeAxesSubalgebra k` gives the claimed
  k-algebra isomorphism. Its next clause fixes it on every quotient representative
  by `↑(e (Ideal.Quotient.mk ... h)) = formalNodeAxisMap k h`.
  Thus the existential is canonically characterized, not an arbitrary isomorphism.
- For EVERY r in R, `Function.Injective (fun x : R ↦ r * x)` is equivalent to
  `(e r).val.1 ≠ 0 ∧ (e r).val.2 ≠ 0`. This is the exact definition of
  non-zero-divisor in the node; no domain assumption is imposed on R or S.
- `∃ s : S, ↑s = (PowerSeries.X, PowerSeries.X) ∧ Function.Injective (s * ·)`
  asserts both that the specified s = (u,v) belongs to S and that it is regular.
  Equality to this fixed pair uniquely determines s.
- Q(R) is `FractionRing (FormalNodeRing k)`. Mathlib defines this abbreviation as
  `Localization (nonZeroDivisors R)` even for rings with zero divisors. This is
  the localization clause of `def-weil-pbc-essentially-finite-type-algebra`;
  the theorem does not impose essential finite type on the formal node.
- The existential `Φ : FractionRing R ≃ₐ[k] LaurentSeries k × LaurentSeries k`
  is the claimed extension isomorphism. The next clause fixes its value on the
  canonical `algebraMap R (FractionRing R)`, using the axis identification e and
  `formalNodeBranchesToLaurent k`.
- The real definition `formalNodeBranchesToLaurent k` is the product of the two
  `HahnSeries.ofPowerSeries ℤ k` maps, the exact coefficientwise inclusions named
  by the Laurent-series dependency. The factors are Mathlib's `LaurentSeries k`.
- `∃ ι : P →ₐ[k] FractionRing R, Function.Injective ι ∧ ...` gives the inclusion
  of P. Its two compatibility clauses say `Φ (ι p) = formalNodeBranchesToLaurent k p`
  for every p, and `ι (e r).val = algebraMap R (FractionRing R) r` for every r.
  Together with the preceding Φ clause these render both inclusions in the node.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, extending `CommRing`
  and `DivisionRing`.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic`; its recorded signature and the
  `PowerSeries` specialization were read. The canonical restrictions use
  `MvPowerSeries.killCompl`, `Mathlib.RingTheory.MvPowerSeries.Rename`.
- `def-weil-pbc-laurent-series`: `LaurentSeries`,
  `Mathlib.RingTheory.LaurentSeries`, and `HahnSeries.ofPowerSeries`,
  `HahnSeries.ofPowerSeries_injective`, `Mathlib.RingTheory.HahnSeries.PowerSeries`;
  `HahnSeries.order`, `Mathlib.RingTheory.HahnSeries.Basic`, was also inspected.
  Hahn support in Z is bounded below, as the dependency's match explains.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom`,
  `Mathlib.Algebra.Algebra.Hom`, and `Ideal.Quotient.mkₐ`/the quotient algebra
  in `Mathlib.RingTheory.Ideal.Quotient.Operations`. The theorem uses the same
  quotient map at the ring level as `Ideal.Quotient.mk`.
- `def-weil-pbc-essentially-finite-type-algebra`: its localization construction is
  Mathlib `Localization`; the specialization to all regular denominators is
  `FractionRing`, `Mathlib.RingTheory.Localization.FractionRing`.
  The recorded `Algebra.EssFiniteType`, `Mathlib.RingTheory.EssentialFiniteness`,
  and its signature were read; the finiteness predicate itself is irrelevant here.
- Proof-only imports: `Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors`
  (`lem-weil-pbc-power-series-domain`), `Mathlib.RingTheory.HahnSeries.Summable`
  (`HahnSeries.instField`, `lem-weil-pbc-laurent-series-field`), and
  `Mathlib.RingTheory.Localization.Defs` (`IsLocalization.lift`,
  `IsLocalization.ringHom_ext`, `lem-weil-pbc-ring-localization-universal-property`).
  Their recorded source signatures and docstrings were inspected. All theorem
  proof steps appear in the theorem docstring. The proof-only imports remain plain
  imports even when another statement import already imports them transitively.

Edge cases checked before writing:

- Arbitrary characteristic, including 2: the inverse uses subtraction of the common
  constant, with no division by 2. Both the ideal and the maps have the same formulas.
- Zero r, and pairs with just one zero component: the iff correctly fails injectivity,
  using (u,0) or (0,v) as a nonzero annihilator. R is not assumed to be a domain.
- The unit pair has both components nonzero. The pair (u,v) has common constant zero.
- Zero Laurent series have a lower support bound as well. If only one component is
  nonzero, multiplying by a large common power still gives a numerator in S.
  For example (u^(-3),0) = (u,0)/(u,v)^4.
- Equal-constant branch pairs include arbitrary common constants; P includes pairs
  with unequal constants. For example (1,0) lies in P but not S and is represented
  in Q(R) by (u,0)/(u,v). Thus the final P compatibility has not been restricted to S.
- `s` and `e` are existentially specified by their exact canonical formulas, so
  there is no extra choice or added hypothesis. All universes and variables are
  explicit, and `set_option autoImplicit false` enforces this.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder "The total quotient ring of k[[u,v]]/(uv) is the product
  of two Laurent series fields via the axis restrictions"`: 8 hits, including
  `LaurentSeries.instIsFractionRingPowerSeries` and Laurent/adic completion
  equivalences. These concern one branch and give neither the two-axis kernel and
  image nor the product total-fraction result.
- `msearch.py ... loogle "MvPowerSeries, IsFractionRing"`: 0 hits.
- `msearch.py ... grep "(MvPowerSeries|PowerSeries).*(axis|node|fiber[Pp]roduct)|LaurentSeries.*Prod"`:
  0 hits in Mathlib.
- `msearch.py ... leansearch "The total quotient ring of the formal split node
  k[[u,v]]/(uv) is k((u)) times k((v))"`: 8 hits. The closest is again
  `LaurentSeries.instIsFractionRingPowerSeries`; the others concern localization
  subalgebras, polynomial fraction rings, or Dedekind quotients. No exact statement.
- `rg -n` for the item id, `formalNode`, `formalSplitNode`, and axis/fraction patterns
  in `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration of this result.
  One prose hit in `Sheaf/AlgebraicGeometry/OrdinaryPointDeltaBranches.lean` mentions
  an axes quotient in a later normalization argument, not this statement.
- `grep -rn "lem-trf-formal-node-axes-total-fractions" lean/WeilConjectures`:
  no hits. Searches for every proposed declaration name across Mathlib and both
  project source roots also found none.

Validation: the complete module compiled separately in sandbox and library mode through
`scompile.py Q60 lem-trf-formal-node-axes-total-fractions`, with no errors or warnings.
The final module also enables `autoImplicit false`; delivery preflight recompiles it.
There are no node faults or disputed statements.

## Second reading by Q60

This is the worker's own second pass, not an independent worker review. The dispatcher
explicitly forbids spawning another agent and assigns independent review to the maintainer.
I reread the original node and the delivered module together. The matching above includes
both the kernel and image, the induced k-algebra quotient isomorphism, the iff for every
r including zero, the specified regular pair, and the Laurent isomorphism. In particular,
I checked the final two commuting formulas for all of P and its restriction to R: omitting
the P-to-Q embedding would have left the last phrase of the node unstated. No mathematical
statement changed during this pass. The five helpers are explicit constructions owned
by this node, not independent notions or replacements of dependency definitions.
