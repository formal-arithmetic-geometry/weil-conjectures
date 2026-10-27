## Worker report

The module `Sheaf.Algebra.Lie.LocallyNilpotentDerivationExponential` states
`Module.End.exists_lieEquiv_of_locallyNilpotent_derivation`, with proof `sorry`.
No definitions, helper theorems, new nodes, dependency repairs, or statement
corrections are needed. Only the item's `lean` field changes.

Source read: Milne, Algebraic Groups (2017), Theorem 23.63, first proof,
printed pp. 503–504, and the characteristic-zero discussion on p. 508.
As the node expressly says, Milne does not state this exponential lemma;
it is the agent-supplied Lie-theoretic prerequisite for the Serre reflection
construction. The four proof steps in the node are retained in the theorem's
docstring. The module does not assert any additional attribution to Milne.

Hypotheses and clauses, matched individually:

- A Lie algebra over Q: `{L : Type u} [LieRing L] [LieAlgebra ℚ L]`.
  The universe `u` is explicitly declared. There is no dimension, finiteness,
  or nontriviality assumption.
- A Q-linear endomorphism: `(D : Module.End ℚ L)`. This is Mathlib's bundled
  linear endomorphism, not a new derivation definition.
- The displayed Leibniz identity is exactly
  `hder : ∀ x y : L, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆`.
- Local nilpotence is exactly
  `hnil : ∀ x : L, ∃ N : ℕ, 1 ≤ N ∧ (D ^ N) x = 0`.
  In particular the bound is inside the quantifier over vectors.
- The convention on powers is Mathlib's multiplication on `Module.End`:
  `mul_eq_comp`, `one_apply`, and `pow_apply` identify multiplication with
  composition, the unit with the identity, and powers with function iterates.
- A Q-linear Lie algebra automorphism is the witness `e : L ≃ₗ⁅ℚ⁆ L`.
  Mathlib's `LieEquiv` extends `LieHom`, hence a Q-linear bracket-preserving
  map, and supplies left and right inverse laws. This includes exactly
  linearity, preservation of the bracket, and bijectivity.
- The finite-sum formula is the first conjunct, for every `x : L` and every
  `N : ℕ` with `1 ≤ N` and `(D ^ N) x = 0`:
  `e x = ∑ n ∈ Finset.range N, ((n.factorial : ℚ)⁻¹) • ((D ^ n) x)`.
  `Finset.range N` is precisely the integers from zero through N-1, and the
  coefficient is the rational inverse factorial.
- Independence of N is included by the quantifier over every valid cutoff,
  all giving the value of the same witness `e`. Conversely, the node's
  cutoff-independent automorphism supplies exactly this witness. No choice
  of an arbitrary map or extra assumption replaces the finite-sum construction.
- The inverse clause is the second conjunct with the same coefficient and
  summation range, `e.symm x`, and `(-D)` in both the annihilation hypothesis
  and summands. It applies to every positive cutoff killing x under -D,
  exactly the pointwise formula defining Exp_{-D}. Existence of such cutoffs
  follows from `hnil` and `(-D)^n x = (-1)^n • D^n x`, as in proof step 1.
  Using `e.symm` gives both inverse identities by the existing `LieEquiv`
  structure, without adding a separate unnamed postponed theorem.

Dependency declarations read and used:

- `def-wf-lie-algebra` has no `lean` record; its `mathlib_match` provides
  `LieRing` and `LieAlgebra` in `Mathlib.Algebra.Lie.Basic` (lines 61–80).
  Their full signatures and docstrings were read. These are the exact
  additive, alternating, bilinear Lie bracket with Jacobi required here.
  The same module defines `LieEquiv` (lines 500–517), also read, which
  packages the conclusion. The other notions in this broad definition node
  (ideals, representations, etc.) are not needed by the item.
- Proof prerequisite `lem-sfb-lie-derivation-iterate-binomial` is recorded as
  `LieDerivation.iterate_apply_lie'` in `Mathlib.Algebra.Lie.Derivation.Basic`,
  lines 145–148. Its signature, docstring, and the `LieDerivation` signature
  at lines 43–48 were read. The latter uses subtraction with the reversed
  bracket, equivalent to `hder` by skew symmetry. Its module is a plain
  proof import; the statement keeps the explicit Leibniz hypothesis.
- Proof prerequisite `lem-pur-commutative-ring-binomial-expansion` is
  `add_pow` in `Mathlib.Data.Nat.Choose.Sum`, lines 75–79, read together
  with its signature and docstring. Its module is a plain proof import.
- `Mathlib.Algebra.Module.LinearMap.End` publicly supplies the composition
  ring and powers of linear endomorphisms; its `mul_eq_comp`, `one_apply`,
  and `pow_apply` signatures were read. `Mathlib.Data.Nat.Factorial.Basic`
  publicly supplies the factorial in the statement.

Edge cases checked before writing:

- The zero Lie algebra is allowed, with its unique automorphism. There is
  no `Nontrivial` or finite-dimensional instance.
- For D = 0, cutoff N = 1 gives the identity, and all larger positive
  cutoffs give the same value, for both D and -D.
- For x = 0 every summand vanishes and any positive cutoff is allowed.
- The n = 0 term is x, because D^0 is the identity and 0! = 1. A cutoff
  N = 0 is excluded exactly as in the node; no zero factorial is inverted.
- Taking the abelian Lie algebra on Q[X] and D = d/dX shows why local
  nilpotence cannot be replaced by global nilpotence: every polynomial is
  killed by some derivative, but D^n(X^n) = n! is nonzero for every n.
  This arbitrary-dimensional case is included in the delivered signature.
- Negative D has the same annihilating cutoffs because its n-th power is
  (-1)^n times D^n. Thus the inverse specification is nonvacuous.
- The base is exactly Q, so all factorial denominators are invertible;
  no positive-characteristic case is silently introduced or discarded.

Searches actually run with the prescribed `msearch.py Q40 <item>` wrapper:

- LeanFinder query: "The exponential of a locally nilpotent derivation of an
  arbitrary dimensional rational Lie algebra is an automorphism with inverse
  the exponential of its negative". Eight hits: `LieDerivation.exp`, its
  apply lemmas, `Module.End.exp_mul_of_derivation`, and globally nilpotent
  exponential lemmas. None gives the pointwise local hypothesis.
- Loogle query: `LieDerivation.exp`. Three hits: `LieDerivation.exp`,
  `LieDerivation.exp_apply`, `LieDerivation.exp_map_apply`; all require
  `IsNilpotent D.toLinearMap`.
- Mathlib grep query: `locallyNilpotent|LocallyNilpotent|def exp|iterate_apply_lie`,
  restricted to `Algebra/Lie`. Four hits, all in Derivation/Basic.lean:
  the iterate lemmas and the global exponential definition.
- LeanSearch query: "A locally nilpotent Lie derivation over the rationals
  exponentiates pointwise to a Lie algebra automorphism". Eight hits:
  the same globally nilpotent exponentials and related derivation/Engel
  declarations; no exact match.
- Read the candidate's source in Mathlib/Algebra/Lie/Derivation/Basic.lean,
  lines 399–426. Its `IsNilpotent D.toLinearMap` is a uniform bound and
  cannot specialize to the pointwise bound on arbitrary-dimensional L.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `locallyNilpotent|LocallyNilpotent|nilpotent.*[Ee]xp|[Ee]xp.*[Nn]ilpotent`
  and the node id found no exact declaration. The Chevalley Weyl-sign
  module uses the global nilpotent exponential only. The node-id search
  of `lean/WeilConjectures` found nothing.
- Searches for `locally_nilpotent|locallyNilpotent|exp_of_locally|locallyNilpotentExp`
  in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`
  found only an unrelated factorization statement. A final search for the
  chosen full declaration name in Mathlib, the upstream-name index, and
  both Lean trees found no collision.

Validation: prescribed `scompile.py` compiled both its sandbox and library
module views cleanly (2.6 s and 1.4 s), without errors or warnings.
No statement dispute or source correction was found.

## Second reading by Q40

The dispatcher expressly prohibits starting another agent; this section records
my separate rereading of the completed node and module, not an independent
worker's review. The maintainer supplies the independent delivery review.

The binder `{L : Type u}` includes arbitrary dimension and the zero algebra;
`[LieRing L] [LieAlgebra ℚ L]` uses the definition dependency's Mathlib match.
`Module.End ℚ L` and `hder` reproduce the two assumptions about D separately.
The position of `∀ x` before `∃ N` in `hnil` preserves local nilpotence.
The first conjunct quantifies every positive annihilating N and fixes all
such sums to `e x`, so the independence clause is present. The second
conjunct uses the same formula for -D with its own valid cutoffs and the
inverse of that same e. `LieEquiv` supplies linearity, bracket preservation,
and both inverse laws, so no conclusion is missing. The two finite sums
start at zero, stop at N-1, and have coefficients in Q, not in the
endomorphism ring. No mismatch was found and no statement change was made.
All four natural-language proof steps are in the declaration docstring.
