## Worker report

`ExponentCechComplex.lean` defines the fixed-exponent alternating Cech complex.
`ExponentCechHomology.lean` states the three cases for its cohomology, with the
proof left as `sorry`. The original item has no statement dependencies. The new
definition node `def-pc-exponent-cech-complex` supplies its complex.

The node's commutative ring is `{A : Type*} [CommRing A]`; `n >= 1` is `hn : 1 <= n`;
the exponent vector is `e : Fin (n + 1) -> Int`. `N_e` is the filter of `Finset.univ`
by `e i < 0`. The free degree-`p` module has basis `exponentCechBasis n e p`, a
subtype of finite subsets with card `p+1` and containing `N_e`. The differential
inserts each missing `k`, with coefficient `(-1) ^ card (J.filter (· < k))`.
`exponentCechDifferential_comp` states `d^2 = 0`, and `exponentCechComplex`
uses `CochainComplex.of`.

For `N_e = empty`, the first conjunct gives `Nonempty (H^0(C) ~= A)` as an
`A`-linear equivalence and zero cohomology in every `q != 0` as `Subsingleton`.
For nonempty proper `N_e`, the second conjunct gives `Subsingleton (H^q(C))`
for every `q`. For full `N_e`, the final conjunct gives a cycle equal to the
full-subset basis vector, an `A`-linear equivalence of `H^n(C)` with `A`
sending its class to `1`, and zero cohomology for every `q != n`.

Edge cases checked: `A` may be the zero ring; `n=1` has the expected two-term
complex; an empty negative set leaves all nonempty subsets; a proper negative
set remains nonempty after the chosen contraction vertex is removed; a full
negative set leaves only the full subset. The `n=0` case is outside the node's
own hypothesis. There is no condition on the sum of the coordinates of `e`.

Searches: `msearch.py leanfinder` with the fixed-exponent Cech-complex query
returned only standard simplex declarations; `msearch.py loogle` on
`CochainComplex, alternatingCofaceMapComplex` found no match; `msearch.py grep`
for exponent/Cech and simplex/cochain in Mathlib AlgebraicTopology found none.
`rg` in the source repository found the larger
`AlgebraicGeometry.ProjectiveSpace.monomialCechComplex` in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.MonomialCech`, but its degree
terms are families on all ordered tuples and all exponent vectors, so it is
not this fixed-exponent subset-basis complex. `rg` in the Sheaf library and
the DAG found no definition node for this notion; `blueprint_refs.py search`
also found none. No original dependency declarations were used.

## New nodes

`def-pc-exponent-cech-complex` defines exactly the subset-basis complex in
the item's first two sentences. Its source is Stacks Tag 01XS, NEG(e) cases.
The searches above found no existing node or declaration for it. The same
module has the named `exponentCechDifferential_comp` statement, whose proof
is postponed and whose docstring gives the pairwise sign cancellation.

## Earlier second reading (a previous round; superseded)

Pending independent reading by the second worker before delivery.

## Second reading by H1

Read the item, the new definition node, both delivered modules, Stacks
`coherent.tex` at `lemma-cohomology-projective-space-over-ring` (in the Tag
01XS section), and the source homology-class API. The repository's literature
checkout is absent on this machine; the complete Stacks text was read from
`/home/ubuntu/c1-stacks-review/coherent.tex`, lines 1603–1846. Its hypotheses
are an arbitrary commutative ring and n >= 0. The item deliberately addresses
n >= 1. Fixing an exponent needs no sum constraint: it belongs to the twist
of degree equal to its sum. No scheme assumptions enter this algebraic lemma.

Object, hypothesis and conclusion checklist, in the order of the node:

- A commutative ring: `{A : Type*} [CommRing A]`. Exact, arbitrary universe;
  neither a field nor a nonzero/Noetherian ring is assumed.
- n >= 1: `(n : ℕ) (hn : 1 ≤ n)`. Exact.
- e in Z^(n+1): `(e : Fin (n + 1) → ℤ)`. Exact; no degree or sign restriction.
- N_e: `exponentCechNegativeSet n e`, defined as the filter of all coordinates
  by `e i < 0`. Exact, including zero exponents.
- Degree-p free module: `exponentCechBasis n e p →₀ A`, with basis subtype
  `J.card = p + 1 ∧ exponentCechNegativeSet n e ⊆ J`. Exact subsets, with no
  repeated vertices or ordered-tuple substitutes.
- Differential: `exponentCechDifferential` extends the finite sum of insertions
  using `(-1 : A) ^ (J.1.filter fun j => j < k).card` and coefficient 1.
  Exact orientation and coefficient. `CochainComplex.of` has these adjacent
  differentials and zero nonadjacent maps (read its definition and `of_d`).
- Empty negative set: first implication gives `Nonempty (H⁰ ≃ₗ[A] A)` and
  `∀ q, q ≠ 0 → Subsingleton (H^q)`. Exact module isomorphism and vanishing.
- Nonempty proper negative set: second implication has precisely the two
  inequalities and gives `∀ q, Subsingleton (H^q)`. Exact, including q = 0.
- Full negative set: third implication supplies a cycle `z` equal to the
  full-subset `Finsupp.single ... 1`, together with `f : H^n ≃ₗ[A] A` taking
  its homology class to 1, and vanishing for every q != n. This is exactly
  free rank one on the stated class, not just an unspecified isomorphism.
  Read `CochainComplex.homologyClass` in
  `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat`: it is
  the quotient-of-cycles class map transported to categorical homology.
  Its index equalities follow from hn, and add no hypothesis.

All clauses agree, in the same quantifier order. A zero module is precisely
`Subsingleton`, since its additive zero supplies inhabitation. Degrees are
natural numbers, with the stipulated complex zero below degree zero; negative
degrees therefore have zero cohomology automatically.

Edge cases: the zero ring is admitted, including the generator equation 0=1
in that ring; characteristic 2 is admitted (the opposite signs still cancel).
The empty negative set is admitted, as are singleton proper negative sets and
the full negative set. The whole coordinate set cannot be empty under n >= 1;
n=1 gives the expected two-term complex. n=0 is excluded by the item itself,
although the definition remains meaningful there. Terms p>n have empty basis
and hence are zero modules. An empty scheme is not an object of this statement;
its possible zero coefficient ring is included. `Type*` leaves the ring
universe arbitrary, and the finite basis imposes no universe restriction.

Independent H4/H12 searches: LeanFinder query "cohomology of simplex cochains
supported on faces containing a fixed set of vertices" returned simplex faces,
group cochains, and `AlgebraicTopology.AlternatingCofaceMapComplex.obj`; none
states this complex or its computation. Loogle `CochainComplex, Finsupp`
returned no hits. LeanSearch "cohomology of relative simplex cochains containing
prescribed vertices" was unavailable (Internal Server Error), not a negative
verdict. The grep service query `prescribed|relative.*simplex|simplex.*cochain`
in AlgebraicTopology returned only relative simplicial morphisms and Kan
composition. Direct rg searches for negative/Cech, exponentCech, monomialCech
and relative simplex in Mathlib, WeilConjectures, Sheaf and the DAG found no
existing fixed-exponent definition or theorem. `blueprint_refs.py search
'exponent'` found no matching definition node. Also searched the upstream name
index. Read the source `ProjectiveSpace.MonomialCech` definitions: they use all
ordered tuples and all exponent vectors of a fixed total degree, not this
finite-subset fixed-exponent complex. The generic alternating coface complex
constructs a complex from a cosimplicial object; it supplies neither this
object nor this theorem. Thus no existing declaration can replace the delivery.

The new definition node was checked as a stage-1 definition: its explicit
basis and insertion differential agree with the Stacks graded-piece formula;
it needs no other paper-specific notion. Its definition also permits n=0,
which changes nothing for the node's domain n>=1. Its fields include the
source, three kinds of searches, empty proofs, creation record, ancestor/via,
chapter/unit, audit-none records and the module record. The item cites it.
The original item has no statement dependencies; no dependency replacement
modules or statement corrections are required.

Mismatch found and repaired: the homology theorem's proof docstring spoke of
"insertion" without distinguishing cochain-component evaluation from the
subset-basis homotopy. Replaced it with signed removal on basis elements,
the preservation/nonemptiness justification, pairwise cancellation, the
explicit degree-zero kernel/boundary argument, and the full-set argument.
The mathematical signatures and definitions were already right and were
left unchanged. Every theorem proof remains `sorry`; definitions contain real
data, and their square-zero obligation is the named
`exponentCechDifferential_comp`, with its cancellation proof in the docstring.
No hollow definition, unbound variable, extra instance, or statement correction
was found. Node signatures agree with the Lean signatures (whitespace-normalized).

Validation: both modules compiled together cleanly on the project server;
final compilation and delivery preflight are run after this docstring repair.
