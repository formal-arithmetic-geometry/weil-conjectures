## Worker report

Item: lem-sfb-ordered-join-coset-comparison. The new module is
`Sheaf.AlgebraicTopology.OrderedJoinCosetComparison`, with main theorem
`AlgebraicTopology.OrderedJoin.CosetComparison.orderedJoinCosetComparison`.
All constructions are actual data; the sole postponed proof is the main theorem.
The statement of the DAG node is unchanged. No new nodes or dependency repairs.

Hypotheses and definitions, checked against the node:

- `G : Type u`, `[Group G]`, and `H : Subgroup G` give exactly the group and subgroup,
  with arbitrary universe and no topological or finiteness hypothesis.
- `n : ℕ`, `hn : 1 ≤ n`, and `a : Fin (n+1) → G` are the positive integer and
  separately indexed representatives a_0,...,a_n.
- `TupleSymbol Y q` is a list of length q+1 (integer length equality), and
  `TupleChain Y q` is `TupleSymbol Y q →₀ ℤ`. Thus the specified basis is exactly
  all ordered tuples, including repetitions. The empty list is the unique basis
  symbol in degree -1, canonically identifying that group with ℤ; below -1 there
  are no symbols and the group is zero. This does not use a free module on an
  unspecified basis.
- `tupleBoundary Y q p`, used at adjacent degrees, is the signed list of all
  `eraseIdx` faces, extended by `Finsupp.linearCombination ℤ`. At degree zero
  its one face is the empty list with coefficient 1, and the empty-list boundary
  is zero. `tupleMap (fun h ↦ g*h)` and `tupleMap (fun x ↦ ↑g*x)` give diagonal
  left translation, fixing the empty tuple.
- `Coset H a i = {x : G // ∃ h : H, x = ↑h * a i}` gives exactly Ha_i. These
  are separate members of the color-indexed family even when cosets coincide.
  `Chain (Coset H a) q` and `boundary` are the dependency's groups and boundary,
  unmodified. `translateVertex` constructs the stable left action using g*h;
  the induced `chainMap` fixes colors and the empty face.
- `vertex H a h i` is exactly ha_i. `comparison H a k` is P in degree k-1.
  The arity-zero branch sends the empty tuple to the empty face (identity on ℤ).
  The arity-one branch inserts color 0 with vertex h_0*a_0. The k+2 branch is
  the linear extension of S based at the head h_0, applied to P in arity k+1
  of the alternating boundary. Its input symbol has positive length, so the
  `headD 1` default is never used. This is the exact displayed recursion,
  not an arbitrary comparison or an existence assertion.
- `arityDegree 0 = -1`, `arityDegree (q+1) = q` is an indexing helper: arity
  counts vertices. Hence `arityDegree q` in the theorem is exactly q-1,
  including q=0; it adds no hypothesis or change of degree.
- `erasure H a q` enumerates all colors in increasing order, keeps those in
  the face, extracts their vertices, and sends that list to its tuple basis
  vector. This is exactly forgetting labels. `erasedComparison` is its composite
  with the explicit `comparison`.

Main theorem clauses, in order:

1. The first universal clause gives dP_q=P_(q-1)d for every natural q≤n, as
   equality of integer-linear maps, with the augmented target at q=0.
2. The second gives equivariance of P in every arity k≤n+1, that is degrees
   -1 through n, for every g:H and every chain (map equality).
3. For each q≤n, `∃ L : List (ℤ × Symbol (fun _ ↦ Fin(q+1)) q), ∀ h, ...`
   is the uniform finite formula. A formal Symbol has precisely q+1 distinct
   colors from Fin(n+1), naturally in increasing order, and a coordinate index
   in Fin(q+1) at every color. Applying `chainMap` replaces each index j by
   h_j*a_i. Coefficients are integers and the unreduced List permits repetitions.
   The existential precedes `∀ h`, so no coefficient, color or coordinate choice
   can depend on the values h_j or tests for their equality. There is no
   distinctness assumption on the h_j or the cosets.
4. The next clause is de_q=e_(q-1)d in all integer degrees.
5. The next is equivariance of erasure in all integer degrees.
6. The next describes P_-1 as the identity under the unique-empty-symbol
   identifications with ℤ: sum of input coefficients times the empty face.
7. The next similarly says e_-1=1.
8. The next says dA_q=A_(q-1)d for 0≤q≤n.
9. The next says A is equivariant in degrees -1 through n.
10. The next says A_-1=1 under the empty-tuple identification.
11. The final `LinearMap.range ... ≤ Submodule.span ℤ (Set.range ...)` says
    precisely that the image of A_n lies in the integer span of all tuples
    `[h_0*a_0,...,h_n*a_n]`, with independent h_i:H. It asserts neither
    surjectivity nor a closure of the span.

Dependency declarations read and used:

- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, its full class
  signature and docstring, and `Module.free_iff_set`. The actual specified free
  modules here use Mathlib `Finsupp` with `Finsupp.basisSingleOne`, as in the
  recorded ordered-join dependency. This import is exposed transitively by it.
- `Sheaf.AlgebraicTopology.OrderedJoinPartialContraction`:
  `AlgebraicTopology.OrderedJoin.Face`, `Symbol`, `Chain`, `symbolTerm`, `insert`,
  `boundary`, `contraction`, `chainMap`, `mapFace`, `expansionRecipe`, and
  `partialContraction`; the entire source, signatures and docstrings were read.
  The recorded contraction has its required order of the R-prefixes, permits
  noninjective maps of pointed families, and its identity only below top degree
  is exactly sufficient for this recursion. Both statement/proof dependencies
  are imported publicly, directly or transitively. The other direct import is
  Mathlib's subgroup interface, `Mathlib.Algebra.Group.Subgroup.Basic`.

Edge cases checked before finalizing:

- n=1: on [h0,h1], P_1 is
  `-[(0,h1*a0),(1,h0*a1)] + [(0,h0*a0),(1,h0*a1)]`, whose boundary is
  `[(0,h1*a0)] - [(0,h0*a0)]`, as required by P_0 d. The signs and order match
  the dependency's actual contraction.
- h0=h1 is permitted; equal output terms cancel without choosing a formula by
  vertex equality. A trivial subgroup or trivial group is permitted. All a_i
  can coincide and all Ha_i can coincide; labels still distinguish colors.
- q=0 has the one-term finite formula and its boundary is the empty symbol.
  Arity zero is precisely the augmented identity; degree -2 has no tuples or
  faces and the empty boundary vanishes. Empty Y is allowed in the tuple helpers.
- The recursion uses the contraction only on degrees q-1≤n-1, where the
  dependency's bound r-2=n-1 holds for r=n+1. No false top-degree contraction
  or full exactness assertion is introduced.
- In top degree the color set has n+1 members among n+1 possibilities, so
  erasure has precisely the claimed rectangular support, even for repeated
  representatives. Arbitrary group universes are retained.

Searches (2026-10-24; prescribed msearch wrapper, group Q138 and this item):

- leanfinder: `Equivariant augmented chain map from homogeneous group tuples to
  ordered join of subgroup cosets with uniform finite coordinate formula`:
  eight hits including Rep.barComplex.d, Rep.standardComplex and group homology
  chains; none constructs the specified ordered-coset join comparison.
- loogle: `Rep.barComplex, Rep.standardComplex`: one hit,
  `Rep.barComplex.isoStandardComplex`, the standard/bar-resolution isomorphism,
  not the join comparison or uniform formula.
- grep: `(ordered.?join|coset).*(chain.?map|contraction)|(chain.?map|contraction).*(ordered.?join|coset)`:
  zero Mathlib hits.
- leansearch: `Free abelian augmented chains on ordered tuples with deletion
  differential and equivariant comparison to ordered join cosets`: eight hits,
  including ChainComplex.augment, FreeAbelianGroup and standard/bar complexes;
  none states the comparison. Finsupp supplies the existing free-module
  construction, so no second definition of freeness is made.
- `rg` of both project source roots for ordered join, coset comparison, and
  homogeneous chains found the existing contraction and the parent's cocycle
  theorem, which only describes this construction in its proof docstring.
  `grep -rn` for this exact item in WeilConjectures found no declaration.
  Further exact-name searches for TupleSymbol, TupleChain, tupleBoundary,
  orderedJoinCosetComparison and the namespace in Sheaf, WeilConjectures and
  dag/lean_names_upstream.json found no existing declarations before writing.

Source reading: the current `literature/blueprint/latest/` direct-images proof,
paragraph (3), lines 19–25, supplies the application but contains no ordered-join
calculation, just as the node explicitly records. The seven agent arithmetic
steps in the accepted node supply the construction/proof, reproduced in the
main theorem's docstring. No external reference has been invented. No statement
fault or STATEMENT-DISPUTED issue found.

Validation: prescribed scompile.py compiled both sandbox and library-module modes
successfully (1.9s and 1.8s file times); no unexpected warning. The initial wrong
subgroup import path and integer-index elaboration were corrected. All universes
and variables are bound explicitly and autoImplicit is disabled. No global build,
live source edit or direct git operation was used.

## Second reading by Q138

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
