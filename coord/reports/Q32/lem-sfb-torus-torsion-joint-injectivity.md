## Worker report

Q32 states `lem-sfb-torus-torsion-joint-injectivity` in
`Sheaf.RingTheory.TorusTorsionJointInjectivity`. There is one real helper construction,
`AddMonoidAlgebra.torusTorsionIdeal`, and one postponed theorem,
`AddMonoidAlgebra.torus_torsion_joint_injectivity`. The helper names the very ideal introduced
in this node, rather than an additional independent notion. Its data is Mathlib's ideal span.
Only the item's `lean` field changes; the mathematical statement and dependency lists stay intact.

Read the full item and its statement dependency `def-weil-pbc-algebra-hom-quotient`, including
that dependency's `mathlib_match`. Read the signatures and docstrings of `AlgHom` in
`Mathlib.Algebra.Algebra.Hom`, and `Ideal.Quotient.algebra` and `Ideal.Quotient.mkₐ` in
`Mathlib.RingTheory.Ideal.Quotient.Operations` (lines 353–395). The dependency is a Mathlib
node, so it correctly has no project `lean` record. Its recorded canonical quotient declaration
is used directly; no dependency repair is needed.

Read the local Milne PDF as extracted text: Theorem 12.33 and its proof on printed p.243,
and Theorem 12.36 and its proof on printed pp.243–244. The former identifies the torsion
quotients by the relations `t_i^n - 1`; the latter uses joint injectivity after adjoining the
parameter algebra. The node's five-step proof supplies the finite-support argument over an
arbitrary coefficient ring. The module docstring reproduces all five steps, including the
residue sums, their vanishing on all generator multiples, support separation, and the
quotient-kernel equivalence.

Hypotheses and clauses, matched individually:

- Any commutative ring `B`: `(B : Type u) [CommRing B]`, with an explicitly declared universe
  `u`. There is no domain, field, reducedness, characteristic, or nontriviality assumption.
- Integer rank `r ≥ 0`: `(r : ℕ)` and the coordinate type `Fin r`. Every finite rank is allowed.
- The Laurent ring of finite formal sums on integer exponent vectors:
  `AddMonoidAlgebra B (Fin r → ℤ)`. Mathlib defines it as a wrapper of finitely supported
  coefficient functions with coefficientwise addition and convolution multiplication. Its
  `single_mul_single` adds exponent vectors, giving exactly `t^u * t^v = t^(u+v)`.
- The ideal `J_n = (t_1^n - 1, ..., t_r^n - 1)`:
  `torusTorsionIdeal B r n` is `Ideal.span` of the range of
  `fun i : Fin r ↦ AddMonoidAlgebra.single (Pi.single i (n : ℤ)) (1 : B) - 1`.
  The vector `Pi.single i (n : ℤ)` is `n e_i`; its monomial is exactly `t_i^n`.
  The helper accepts all natural `n`, while every theorem quantifier selects `0 < n`.
- The quotient homomorphism `q_n`: exactly
  `Ideal.Quotient.mkₐ B (torusTorsionIdeal B r n)`. This is the canonical surjective
  `B`-algebra homomorphism from the recorded dependency, with kernel `J_n`.
- Intersection over every `n ≥ 1` is zero: the first conjunct is
  `(⨅ (n : ℕ) (_ : 0 < n), torusTorsionIdeal B r n) = ⊥`.
  In the complete lattice of ideals, `⨅` is intersection and `⊥` is the zero ideal.
- Equivalently, equal images of `f,g` in every such quotient imply equality:
  the second conjunct quantifies `∀ f g : AddMonoidAlgebra B (Fin r → ℤ)` and then
  assumes `∀ (n : ℕ) (_ : 0 < n), Ideal.Quotient.mkₐ ... f = Ideal.Quotient.mkₐ ... g`,
  concluding `f = g`. Both equivalent assertions are stated, without requiring a
  separate equivalence theorem as a stronger premise.
- When `r = 0`, the Laurent ring is `B`: the exponent type `Fin 0 → ℤ` has one element.
  The existing canonical declaration `AddMonoidAlgebra.uniqueAlgEquiv B (Fin 0 → ℤ)`
  in `Mathlib.Algebra.MonoidAlgebra.Basic` identifies the rank-zero ring with `B`, as
  a `B`-algebra. Its underlying ring equivalence is
  `AddMonoidAlgebra.uniqueRingEquiv (Fin 0 → ℤ)` in
  `Mathlib.Algebra.MonoidAlgebra.Defs`. These existing declarations are not copied.
- Every `J_n` is zero in rank zero: the third conjunct is
  `∀ (n : ℕ) (_ : 0 < n), torusTorsionIdeal B 0 n = ⊥`.
  It specializes the rank to zero explicitly and uses exactly the original positive indices.

Dependency imports and declarations:

- `Mathlib.Algebra.MonoidAlgebra.Basic`: the canonical `B`-algebra structure on the
  Laurent ring, and `AddMonoidAlgebra.uniqueAlgEquiv` for its rank-zero interpretation;
  publicly imports `Mathlib.Algebra.MonoidAlgebra.Defs` with `AddMonoidAlgebra`,
  `AddMonoidAlgebra.single`, and its convolution ring structure.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.mkₐ` and
  `Ideal.Quotient.algebra`, as recorded on `def-weil-pbc-algebra-hom-quotient`;
  also exposes ideal spans, the zero ideal, and the complete lattice of ideals.
  The only proof dependency is that same already imported Mathlib node.

Edge cases checked mathematically before writing:

- Rank zero: `Fin 0` is empty; the generating range is empty, so its ideal span is zero.
  There is exactly one exponent vector and the existing trivial-monoid equivalence gives `B`.
- Zero coefficient ring: every Laurent polynomial is zero; the statement remains valid.
- Positive characteristic and nilpotent coefficients: no cancellation in `B` is used.
  Residue separation is a calculation with integer exponents only; it works over arbitrary `B`.
- `n = 1` is included. For positive rank its ideal need not be zero; only the intersection
  is asserted zero. The theorem does not falsely assert that any single quotient is injective.
- `n = 0` is excluded throughout the conclusions, as in the node.
- Empty polynomial support gives zero directly. Negative exponent coordinates are allowed
  and the bound on their absolute values handles them symmetrically.

Searches actually run, using the prescribed `msearch.py` with this group and item:

- LeanFinder: "The intersection of ideals generated by t_i^n minus one in the Laurent
  polynomial ring over any commutative ring is zero". Eight hits, including
  `LaurentPolynomial.invertibleT`, `exists_T_pow`, `isUnit_T`, `isLocalization`, and
  `reduce_to_polynomial_of_mul_T`; none states the multivariable torsion intersection.
- Loogle: `AddMonoidAlgebra, "injective"`. Eight hits, including `coeff_injective`,
  `single_right_injective`, `ofCoeff_injective`, and `mapDomain_injective`. These give
  coefficient extensionality or individual map injectivity, not joint torsion detection.
- Mathlib grep: `torsionIdeal|torsion.*joint|Laurent.*quotient|iInf.*span`.
  Twelve hits; the ideal hits include `Ideal.iInf_span_singleton` and its nat-cast form,
  which concern products of pairwise coprime generators, not these Laurent ideals.
- LeanSearch: "Laurent polynomials over a commutative ring are jointly detected modulo
  the ideals generated by t_i^n minus one for all positive n". Eight hits, including
  `LaurentPolynomial`, `LaurentPolynomial.ext`, `LaurentPolynomial.isLocalization`, and
  `Polynomial.toLaurent_eq_zero`; no exact statement.
- Direct `rg` of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `torusTorsionIdeal`,
  `torus_torsion_joint_injectivity`, `Laurent.*(joint|quotient)`, and `torsion.*joint`
  found no matching declaration. Earlier broader Laurent searches found the existing
  univariate Laurent complements and projective-chart Laurent sections; those do not
  state this theorem. Direct `grep -rn` of the item ID in `lean/WeilConjectures` found none.
- Read `AddMonoidAlgebra` and the `single_mul_single` signature in Defs, and the generated
  additive versions of `uniqueRingEquiv` and `uniqueAlgEquiv` in Defs/Basic. Thus the
  underlying finite-formal-sum ring and its rank-zero identification are reused.

No statement correction, new definition node, dependency module, or disputed assertion is needed.
The main module compiled cleanly with the prescribed `scompile.py`, in both its sandbox
and library module modes; no errors or unexpected warnings were printed.

## Second reading by Q32

Author's second reading, with the unchanged node and finished Lean module open; the dispatcher
forbids starting other agents, so this is not represented as an independent worker review.

I checked the ring hypothesis against `[CommRing B]`, the nonnegative rank against `r : ℕ`,
the finite integer-vector sums against `AddMonoidAlgebra B (Fin r → ℤ)`, and each ideal
generator against `single (Pi.single i (n : ℤ)) 1 - 1`. In particular the exponent is `n e_i`,
not a constant vector and not a natural-exponent polynomial ring. The quotient maps are
precisely the dependency's `Ideal.Quotient.mkₐ`, with `B` as coefficient ring. Both index
binders range over all positive naturals, not merely primes or integers invertible in `B`.
I compared the first conjunct with the intersection clause, the second with equality
detection for arbitrary `f,g`, and the third with the explicit rank-zero ideal clause.
The rank-zero identification uses the already existing canonical algebra equivalence;
it is documented without duplicating the construction or adding it as a hypothesis.
No mismatch was found and no mathematical statement was changed. The helper has real data,
the one theorem has only `sorry` as its proof, and its docstring includes all five proof steps.
