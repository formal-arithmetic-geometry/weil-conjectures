## Worker report

The module states the Buchsbaum--Eisenbud implication for a commutative Noetherian
local ring. `R`, its Noetherian and local instances, `e ≥ 1`, and the ranks `n` are
bound explicitly. The maps `φ i` are linear maps between the finite free modules
`(Fin (n (i+1)) → R)` and `(Fin (n i) → R)`. `hcomplex` renders consecutive
compositions equal to zero; `hexact` renders exactness at each intermediate term as
range equal to kernel; `hinjective` renders exactness at the last term. `A` and `hA`
identify the last map's matrix in the standard bases. `I` is the ideal span of
 determinants of all injectively selected row submatrices (including the empty
minor convention through `Matrix.det`). The conclusion is `I = ⊤` or a list of
length `e` contained in `I` which is regular on `R` via
`RingTheory.Sequence.IsRegular R rs`.

The only declarations used are Mathlib's `IsNoetherianRing`, `LinearMap.range`,
`LinearMap.ker`, `LinearMap.toMatrix`, `Matrix.submatrix`, `Matrix.det`, and
`RingTheory.Sequence.IsRegular`; dependency nodes record these as Mathlib leaves.
Edge cases checked include `e = 1` (the intermediate `Fin (e-1)` is empty),
`n e = 0` (the determinant is the empty determinant), and `n (e-1) < n e`
(no injective row selection, hence the span is bottom).

Searches: the target and all dependencies were read from `dag/nodes`; Mathlib
searches in the node report `Matrix.det`, `Matrix.submatrix`, `Module.Free`,
`IsNoetherianRing`, and `RingTheory.Sequence.IsRegular` as matches. `rg` over
`WeilConjectures` and `lean/Sheaf` found no existing Buchsbaum--Eisenbud statement.

## Earlier second reading (a previous round; superseded)

The theorem signature was checked against every clause of the node statement.
The finite free modules are explicit coordinate free modules, the complex and
exactness hypotheses are present, the matrix and maximal-minor ideal use all row
injections, and both alternatives of the conclusion are retained. No statement
correction was needed.

## Second reading by G1

I independently read the item's node (including its six proof steps), every node in
`stmt_deps`, the delivered module, and the recorded Mathlib definitions. The local
checkout lacks the untracked Stacks sources; I read the project's server copy of
`literature/stacks-project/algebra.tex` over read-only SSH: `situation-complex`,
`definition-rank`, and `proposition-what-exact` with its proof. The server's
`tags/tags` confirms 00MV = algebra-definition-rank and 00N1 =
algebra-proposition-what-exact. The situation introduces only a complex of finite
coordinate free modules over a ring; the proposition adds local and Noetherian.
The maximal-ideal matrix-entry reduction in the proof is not a hypothesis.
At i = e, r_e = n_e, so the proposition's determinantal ideal is exactly the
node's ideal. No statement correction is present or needed.

Clause-by-clause inventory and verdicts:

1. Commutative Noetherian local ring (R, m): `(R : Type u) [CommRing R]
   [IsNoetherianRing R] [IsLocalRing R]`. Exact match. The maximal ideal is intrinsic
   to the local ring, so no additional choice of m is needed. Read
   `Noetherian/Defs.lean:193-207` and `LocalRing/Defs.lean:30`; the latter includes
   nontriviality, as does the source's local-ring convention.
2. Integer e >= 1: `(e : ℕ) (he : 1 ≤ e)`. Exact match; every integer >= 1 is a
   natural number. No e = 0 case is claimed by the node.
3. Finite ranks n_0,...,n_e and their coordinate free modules: `(n : ℕ → ℕ)` and
   `(Fin (n i) → R)`. Exact match with R^{n_i}; values of n beyond e are unused and
   unconstrained. Read `Module.Free` in `FreeModule/Basic.lean:43-44` and the standard
   bases `Pi.basisFun` used by the delivered matrix conversion. Finite products and
   finite direct sums are the same coordinate module here, including rank zero.
4. Differentials phi_1,...,phi_e: `(φ : ∀ i : Fin e,
   (Fin (n (i.val + 1)) → R) →ₗ[R] (Fin (n i.val) → R))`.
   Exact match, with Lean φ i representing the source's phi_{i+1}.
5. Complex identities phi_i composed with phi_{i+1} = 0: `hcomplex` for
   `i : Fin (e - 1)` is exactly every consecutive pair. No extra end condition.
6. Exactness at intermediate terms R^{n_1},...,R^{n_{e-1}}: `hexact` is
   `LinearMap.range (φ (j+1)) = LinearMap.ker (φ j)` for all j in Fin (e-1).
   Exact match with the dependency's image = kernel notion, concretely rendered as
   submodules for linear maps. Read `ComposableArrows.Exact` in
   `Algebra/Homology/ExactSequence.lean:128-129`, `ShortComplex.Exact` in
   `ShortComplex/Exact.lean:45-46`, and `ShortComplex.exact_iff_image_eq_kernel` in
   `CategoryTheory/Abelian/Exact.lean:94`. No private exactness definition is made.
7. Exactness at the leftmost R^{n_e}, equivalently injection: `hinjective` says
   `LinearMap.ker (φ ⟨e - 1, ...⟩) = ⊥`. Exact match; no surjectivity at R^{n_0}
   is imposed. The leading zero module and its map are thereby implicit.
8. A is the n_{e-1} by n_e matrix of the last differential: the `A` binder and `hA`
   use `LinearMap.toMatrix (Pi.basisFun R _) (Pi.basisFun R _)`. Exact match, since
   he gives (e-1)+1=e. Read `Matrix` and `Matrix.submatrix` in Matrix/Defs.lean and
   `LinearMap.toMatrix` in Matrix/ToLin.lean:574-585: source basis indexes columns,
   target basis indexes rows. Both agree with the dependency nodes' signatures.
9. I generated by all n_e by n_e row minors: the local `let I : Ideal R :=
   Ideal.span (Set.range ...)` uses injective row selections and all columns (`id`).
   Exact match. Arbitrarily ordered injective selections enumerate each selected
   row subset in all orders; changing row order changes determinant only by a sign,
   a unit, and does not change the generated ideal. Read `Matrix.submatrix` at
   Matrix/Defs.lean:476 and `Matrix.det`/`det_apply` at Determinant/Basic.lean:60-64.
   These are the recorded dependencies, without duplicate notions.
10. First alternative I=R: `I = ⊤`. Exact match.
11. Second alternative: `∃ rs : List R, rs.length = e ∧ (∀ x ∈ rs, x ∈ I) ∧
    RingTheory.Sequence.IsRegular R rs`. Exact match, including order, ideal
    membership of every element, and final nonzero quotient. Independently read
    `IsWeaklyRegular`, `isWeaklyRegular_iff_Fin`, and `IsRegular` at
    Regular/RegularSequence.lean:135-147: regularity means injective multiplication
    on each successive quotient and `top_ne_smul` means the final quotient is nonzero.
    This is the recorded regular-sequence dependency, not weak regularity alone.

Edge cases: at e=1 the two Fin (e-1) hypotheses quantify over the empty type;
only the required injection remains. At n_e=0 there is one empty row injection
and its determinant is 1, giving I=top. If n_{e-1}<n_e there is no injective row
selection, so the span is bottom as in the node; the injection hypothesis has not
been relaxed. Intermediate ranks and n_0 may be zero. The zero ring is excluded
by both local-ring conventions, but zero free modules are included. No field,
characteristic, domain, positive-rank, or dimension hypothesis is added. `u` is
arbitrary, and coordinate modules live in the ring's universe as the node's
explicit R^{n_i} do. There are no schemes or additional module universes to bind.
All variables and the universe are explicitly bound.

Independent searches (2026-10-11), using different terminology from the worker:

- `msearch.py ... leansearch "Acyclic finite free resolution implies grade of the
  determinantal ideal of its leftmost differential is at least its length"`:
  service unavailable (HTTP Internal Server Error), recorded as unavailable, not
  as a negative search.
- `msearch.py ... leanfinder "Fitting ideal of an injective last differential in a
  free resolution contains a regular sequence of length the resolution"`: eight
  results, all regular-sequence definitions, equivalences, or cons lemmas, including
  `RingTheory.Sequence.IsRegular.cons'`; none states the determinantal assertion.
- `msearch.py ... grep "Buchsbaum|determinantal|ideal.*minors|minors.*ideal"`:
  zero Mathlib hits. Direct `rg` of Mathlib RingTheory, LinearAlgebra and
  Algebra/Homology for those terms and acyclicity found no candidate statement.
- Direct `rg` over `WeilConjectures`, repository `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for Buchsbaum, determinantal, last_minors, 00N1,
  and the node id found no existing theorem. Auslander--Buchsbaum UFD references
  and sheaf acyclicity results are different assertions. Therefore retain this
  module, with no new definition or dependency module.

Mismatches repaired: H8, the old declaration docstring lacked its source place and
compressed six proof steps into one sentence. It now names 00N1 and 00MV and
records base change of minors, avoidance of associated primes, choice of x,
the e=1 case, the reduced shortened complex, and lifting the regular sequence,
with the node's dependency identifiers. H9, added the standard copyright/license/
author header. No mathematical mismatch was found; the theorem signature and the
node's `lean.statement` are unchanged and were checked verbatim equal. No hollow
definition or extra theorem occurs; the sole theorem still has proof `by sorry`.
All lines are at most 100 characters. The original Worker report is retained.

Validation: `scompile.py G1 lem-weil-pbc-exact-free-complex-last-minors-regular-sequence`
on the sole delivered module compiled cleanly (exit 0, 1.4 s), with no warnings.
`deliver2.py ... --no-push` printed OK: preflight passed and server compilation
passed. The recorded signature equals the file's signature byte for byte.

## Reviewer fix (R-efm1013, stage 2)

Restated in the matrix-presented form of the landed sibling modules (H1 92f32df54
`exists_isUnit_maximal_minor_of_annihilator_eq_maximalIdeal`, F1 52d16f7c9): `φ i` is the
matrix of `φ_i : R^{n_i} → R^{n_{i-1}}` with the node's own indexing (`1 ≤ i ≤ e`), acting by
`Matrix.mulVec`; complex as `φ_i (φ_{i+1} v) = 0`, exactness at `R^{n_i}` (`1 ≤ i ≤ e-1`) as
`Function.Exact (φ (i+1)).mulVec (φ i).mulVec`, exactness at `R^{n_e}` as injectivity of
`(φ e).mulVec`; `I` is `Ideal.span` of determinants of `(φ e).submatrix r id` over `StrictMono`
row selections `r`, exactly H1's ideal, so step 2 applies H1 without an `A`/`toMatrix`
bridge or a sign argument for reordered rows. The delivered statement (linear maps on
`Fin n → R`, a separate `A` with `hA : A = toMatrix ...`, `Fin e`-indexed maps shifted by one,
injective row selections) was mathematically equivalent; the conclusion is unchanged.
