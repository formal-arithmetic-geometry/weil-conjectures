## Worker report

The module `Sheaf.RingTheory.IntegralLocalizationFractionComparison` states
`IsLocalization.integral_localization_fraction_comparison`, with one `sorry` and
no new definition. The node's statement, dependencies and proof are unchanged.
The inherited NS merge was the stage-1 split, not a stage-2 delivery: the current
node had no Lean record and the N9 sandbox had no node files or modules.
No interrupted delivery was repeated.

Hypotheses and conclusions, clause by clause:

- The rings A and B are `CommRing A`, `IsDomain A`, `CommRing B`, `IsDomain B`.
  Their universes u and v are independent. The given unital map φ is
  `algebraMap A B`, and `hφ` is its injectivity. For commutative rings any unital
  ring homomorphism gives exactly this algebra structure; this encoding imposes
  no additional condition on the map.
- Integrality is `hIntegral : ∀ b : B, IsIntegral A b`. The definition of
  `IsIntegral` is existence of a monic polynomial with zero `eval₂`; it does not
  assert module finiteness.
- C has only `CommRing C` and `Algebra B C`, with its independent universe w.
  Its given map ι is `algebraMap B C`. The assumption
  `IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) C`
  expresses precisely localization at φ(A minus zero): in a domain the
  nonzero-divisors submonoid consists exactly of the nonzero elements.
  `Algebra.algebraMapSubmonoid` is its image under φ. `IsLocalization` includes
  invertibility of denominators, fraction representation and the multiplied
  cross-product equality criterion. No field structure on C is assumed.
- The first conjunct quantifies over every `b ≠ 0` and every polynomial p with
  `p.Monic` and `p.eval₂ (algebraMap A B) b = 0`. Every monic equation in the
  node corresponds to exactly such a polynomial. Its degree n is `p.natDegree`;
  monicity says its coefficient at n is 1. The index i is Mathlib's existing
  `p.natTrailingDegree`, the smallest exponent with nonzero coefficient.
  Monicity over the nontrivial domain excludes the zero polynomial, so the
  zero-polynomial convention for this index never applies.
- The inequality `p.natTrailingDegree < p.natDegree` states i < n.
  The sum `∑ j ∈ Finset.Ioc p.natTrailingDegree p.natDegree,
  algebraMap A B (p.coeff j) * b ^ (j - p.natTrailingDegree - 1)` is d,
  including the leading coefficient. The open-closed interval is precisely
  j = i+1 through n. The next conjunct is φ(a_i) + b*d = 0.
- The final part of the certificate is `algebraMap B C b *
  (-algebraMap B C d * Ring.inverse (algebraMap B C (algebraMap A B a_i))) = 1`,
  with d and a_i expanded in the actual signature. `Ring.inverse` is the existing
  unit inverse in a ring without a field structure. Its argument is a unit
  because a_i is nonzero and is among the denominators. Thus it is exactly the
  inverse used in the node, without an arbitrary inverse parameter or choice.
- The second outer conjunct says every nonzero b has unit image:
  `∀ b : B, b ≠ 0 → IsUnit (algebraMap B C b)`.
- The third outer conjunct quantifies over every `L : Type z`, `Field L`,
  `Algebra B L`, with z independent of the three ring universes. The specified
  injective map j is `algebraMap B L`; its injectivity is an explicit premise.
  The other premise is exactly `∀ ℓ, ∃ b b', b' ≠ 0 ∧ ℓ = j(b)*j(b')⁻¹`.
  This uses the node's explicit fraction-field condition, not a finite-extension
  assumption or an arbitrary field containing B.
- It produces `q : C →+* L` with `q.comp (algebraMap B C) = algebraMap B L`.
  The following conjunct quantifies over ALL ring maps q' with that same
  composite and gives q' = q: uniqueness is among all extending maps, not just
  bijective maps. `Function.Bijective q` is the comparison conclusion.
- For every b in B and nonzero a in A the final conjunct states
  `q (ι(b) * Ring.inverse (ι(φ(a)))) = j(b) * (j(φ(a)))⁻¹`.
  This is the displayed formula, including every allowed denominator.
- There are no finite-generation, module-finiteness, separability or Noetherian
  binders. The first two conjuncts do not require specifying a fraction field.

Dependencies read and used:

- `def-weil-polynomial-ring`: its recorded declaration `Polynomial` in
  `Mathlib.Algebra.Polynomial.Basic`, including its docstring and full structure
  signature. `Mathlib.Algebra.Polynomial.Degree.TrailingDegree` publicly imports
  this interface and gives the existing least-coefficient index; its definition,
  `coeff_natTrailingDegree_ne_zero`, and `coeff_eq_zero_of_lt_natTrailingDegree`
  were read. No private polynomial or least-index construction was introduced.
- `lem-weil-pbc-ring-localization-universal-property`: the node is a Mathlib
  match, `IsLocalization.lift` and `IsLocalization.ringHom_ext` in
  `Mathlib.RingTheory.Localization.Defs`. Read their full signatures and the lift
  docstring, together with `lift_eq`, `lift_comp`, `lift_mk'` and the
  `IsLocalization` definition. That module is a public import. The conclusion
  characterizes the canonical map by its universal property; no helper map or
  postponed map construction is needed.
- `def-weil-field`: Mathlib match `Field`, read in
  `Mathlib.Algebra.Field.Defs` and publicly imported. It is a nontrivial
  commutative ring with inverses for nonzero elements.

Sources read: `literature/stacks-project/algebra.tex`,
`lemma-integral-over-field` (Tag 00GS, part 2) and
`proposition-universal-property-localization` (Tag 00CP), including their proofs.
As the node already specifies, the precise coefficient certificate is its
agent expansion, not a formula asserted to be verbatim from 00GS. The theorem's
proof docstring carries all five steps of the node's accepted proof.

Edge cases checked before writing:

- n = 0: the only monic degree-zero polynomial is 1, so the equation would say
  1 = 0 in B; no nonzero-root case is excluded by an added degree assumption.
- The equation X^n = 0 has no nonzero solution in a domain. This is exactly why
  i = n cannot occur, rather than an additional restriction on the equation.
- A polynomial with zero constant coefficient is allowed: natTrailingDegree
  can be positive. For example X*(X-1) at b = 1 has i = 1 and n = 2, with
  coefficient -1, d = 1 and -1 + 1*d = 0. No a_0 ≠ 0 assumption appears.
- For a linear equation X-a at b = φ(a) ≠ 0, i = 0, d = 1; the inverse
  certificate is the usual inverse of φ(a), with the sign as stated.
- The endpoint j = i+1 gives exponent zero, while j = n contributes the
  monic leading term. Natural subtraction does not truncate a negative
  exponent because the index interval requires j > i.
- Zero numerator b in the fraction comparison is included. Only denominators
  are required nonzero. A = B, base already a field, arbitrary characteristic,
  and infinite integral extensions all remain allowed. No zero-ring domain
  is inadvertently included because IsDomain supplies nontriviality.

Searches for an existing complete statement (msearch.py with group N9 and this
item, plus source rg):

- LeanFinder: "Integral extension of domains localization at nonzero base
  elements explicit inverse least nonzero coefficient monic equation comparison
  fraction field". OK, 8 hits, including
  `RingHom.isIntegralElem_localization_at_leadingCoeff`,
  `is_integral_localization_at_leadingCoeff`, `isIntegral_localization`,
  `IsIntegralClosure.isLocalization`. These concern preservation of integrality
  or an integral-closure specialization, not every monic equation's specified
  least-coefficient inverse together with the comparison.
- Loogle: `"IsIntegral", "IsLocalization"`. OK, 11 hits; localization of integral
  elements, integral closures and related statements, no complete match.
- Mathlib grep: `trailingCoeff.*(eval|root)|eval.*trailingCoeff|root.*trailingCoeff`.
  OK, 4 hits, in Polynomial.Div and Polynomial.RingDivision. These concern
  polynomial division/root multiplicity and do not assert this statement.
- LeanSearch: "Localizing an injective integral extension of domains at the
  nonzero base elements gives explicit inverses from every monic equation and
  a bijective comparison to its fraction field". OK, 8 hits, including
  `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors`,
  `IsField.localization_map_bijective`, and `IsIntegralClosure.isLocalization`.
  The first is a related localization instance; the second localizes a field
  as source; the third assumes an integral closure. None includes the explicit
  coefficient certificates. Related source signatures and docstrings were read.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for integral localization,
  fraction comparison, least-coefficient and trailing-coefficient patterns:
  no complete statement; the trailingCoeff upstream hits concern other results.
- Exact proposed declaration searches in Mathlib, both project source trees
  and `dag/lean_names_upstream.json`: no existing declaration. The prescribed
  node-id grep in `lean/WeilConjectures` also had no hit.

Validation: scompile.py compiled the delivered module both as a sandbox module
and under its final library module name, in 0.9 s and 1.0 s respectively, with
exit code 0 and no errors or unexpected warnings. All variables and universes
are explicit, with `set_option autoImplicit false`. No node faults or
STATEMENT-DISPUTED issue found. No new nodes or dependency repairs were needed.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
