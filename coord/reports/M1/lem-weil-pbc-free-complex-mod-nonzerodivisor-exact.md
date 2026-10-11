## Worker report

The module `Sheaf.AlgebraicGeometry.FreeComplexModNonzerodivisorExact` states
`free_complex_mod_nonzerodivisor_exact`, the Stacks Project Algebra Lemma 00MZ
(`lemma-div-x-exact-one-less`). It introduces a commutative local ring `R`, an
integer `e ≥ 2`, finite free terms represented by `Fin (n i) → R`, and matrices
`φ i : R^(n i) → R^(n (i-1))`. The hypothesis `hcomplex` renders the clause
`φ_i ∘ φ_(i+1) = 0` for `1 ≤ i < e`; `hexact` renders exactness at every term
with index `1 ≤ i < e` via `Function.Exact`; and `hinjective` renders
exactness at the leftmost term `R^(n e)`. The element hypotheses render
`x ∈ maximalIdeal R` and `x*y = 0 → y = 0`.

The conclusion defines `S = R ⧸ Ideal.span {x}`, the quotient map `q`, and each
reduced matrix `φbar i = (φ i).map q`. Its first conjunct says the reduced last
map is injective (exactness at `S^(n e)`), and its second says
`Function.Exact (φbar (i+1)).mulVec (φbar i).mulVec` for every `2 ≤ i < e`,
which is exactness at all remaining terms through `S^(n 2)`. The theorem proof is
`by sorry`, as required at stage 2.

Dependency declarations used: `Module.Free` from
`Mathlib.LinearAlgebra.FreeModule.Basic` (the finite free terms are represented
explicitly as finite coordinate modules); `CategoryTheory.ComposableArrows.Exact`,
`CategoryTheory.ShortComplex.Exact`, and `CategoryTheory.ShortComplex.ShortExact`
from `Mathlib.Algebra.Homology.ExactSequence` (the exactness notion); and
`Matrix` from `Mathlib.LinearAlgebra.Matrix.Defs` (the matrix notion).

Edge cases checked: `e = 2` leaves only the injectivity conjunct and no index in
`2 ≤ i < e`; all `n i` may be zero (including `n e = 0`), and the matrix indices
are finite; no positivity of the ranks is assumed. The local-ring and maximal
ideal hypotheses are retained exactly from Tag 00MZ, although the source proof
notes they are unused.

Searches made: `msearch.py ... grep "exact complex free modules quotient nonzerodivisor" Mathlib/RingTheory`
returned 0 hits; `msearch.py ... leanfinder "exact finite free complex modulo nonzerodivisor"`
returned candidates `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`,
`QuotSMulTop.map_exact`, and related regularity lemmas, none an exact statement of
this finite complex; `msearch.py ... loogle "Function.Exact QuotSMulTop IsSMulRegular"`
returned 0 hits. `rg` over the project/source found no existing declaration, and
`blueprint_refs.py search lem-weil-pbc-free-complex-mod-nonzerodivisor-exact`
found no blueprint node. The dependency declarations above were read from their
recorded Mathlib signatures.

## Earlier second reading (a previous round; superseded)

I reread the node and module together. The `CommRing` and `IsLocalRing`
instances render the local ring, `e` and `he` render `e ≥ 2`, and `n` plus the
matrix family render the finite free terms and maps. `hcomplex`, `hexact`, and
`hinjective` match the complex and exactness clauses one by one. The hypotheses
on `x` render membership in the canonical maximal ideal and the explicit
nonzerodivisor implication. The `let` bindings render the quotient, reduction
map, and entrywise reduced matrices. The two conclusion conjuncts match
injectivity at the left end and exactness precisely for indices `2 ≤ i < e`.
I changed only the import list (to permitted Mathlib modules) and the node's
verbatim signature field (removing the parser's trailing `:=`).

## Second reading by M1

I independently opened the item, all three statement dependency nodes and their
recorded Mathlib declarations, and the Lean module. The repository does not have
literature/stacks-project locally; I read the available Stacks checkout at
/home/ubuntu/c1-stacks-review/algebra.tex: ring conventions, Situation
situation-complex (24583-24605), and lemma-div-x-exact-one-less with its proof
(24765-24790). Its tags table confirms 00MS and 00MZ. The source assumes no
Noetherianity, domain condition, positive ranks or characteristic restriction.

The node's objects, hypotheses and conclusion clauses, matched in order:

1. Local ring (R,m): `(R : Type u) [CommRing R] [IsLocalRing R]`, with
   `IsLocalRing.maximalIdeal R` for m. Verdict: exact. CommRing matches the
   source's commutative unital ring convention. The local-ring class extending
   Nontrivial agrees with existence of a maximal ideal.
2. Integer e at least two: `(e : ℕ) (he : 2 ≤ e)`. Verdict: exact, since every
   integer at least two is a natural number.
3. Finite free modules R^(n_i): `(n : ℕ → ℕ)` and `Fin (n i) → R`.
   Verdict: exact; finite products are finite direct sums. I opened
   Module.Free.exists_basis in FreeModule/Basic.lean: possession of a basis.
   These concrete coordinate modules have the standard basis, so there is no
   private freeness predicate and no extra hypothesis.
4. All linear maps from term i to term i-1: matrices `φ i` with rows
   `Fin (n (i-1))`, columns `Fin (n i)`, acting by mulVec. Verdict: exact.
   I opened Matrix in Matrix/Defs.lean and Matrix.toLin' in Matrix/ToLin.lean;
   the latter identifies matrices with ALL linear maps of coordinate modules.
5. Complex relation for 1≤i≤e-1: hcomplex says successive mulVec maps
   compose to zero for `1 ≤ i` and `i < e`. Verdict: exact.
6. Exactness at terms 1 through e-1: hexact is
   `Function.Exact (φ (i+1)).mulVec (φ i).mulVec` on that range. Verdict:
   exact. I read Function.Exact (the generated additive version of MulExact)
   in Algebra/Exact/Basic.lean: kernel equals set-theoretic range. I also
   read the dependency's ComposableArrows.Exact, ShortComplex.Exact and
   ShortComplex.ShortExact. The existing bridge
   CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
   in ShortComplex/ModuleCat.lean identifies categorical exactness with
   Function.Exact on module maps. Thus this uses Mathlib's existing rendering
   of the dependency notion, not a private copy or a weaker surrogate.
7. Exactness at term e after the incoming zero map: hinjective states
   Function.Injective of `(φ e).mulVec`. Verdict: exact.
8. Element in m and nonzerodivisor: x, hxmem and
   `hx : ∀ y : R, x * y = 0 → y = 0`. Verdict: exact, retaining both source
   hypotheses even though locality and membership are unused in its proof.
9. Quotient ring and induced maps: S is `R ⧸ Ideal.span ({x} : Set R)`;
   q is Ideal.Quotient.mk; φbar is entrywise Matrix.map q. Verdict: exact;
   this principal ideal is xR and the reduced maps have precisely the source
   matrices, interpreted as S-linear maps.
10. Reduced left-end exactness: the first conjunct asserts zero kernel of
    `(φbar e).mulVec`. Verdict: equivalent to injectivity because mulVec is
    additive. It holds for zero ranks as well.
11. Reduced exactness at terms e-1 through 2: the second conjunct is
    Function.Exact for `2 ≤ i` and `i < e`. Verdict: exact. No exactness at
    term 1, nor surjectivity onto it, is asserted. Function.Exact implies
    zero composite, so it also supplies the shortened complex relations.

The infinite indexing of n and φ adds no hypotheses on the finite complex:
only indices through e are used, φ 0 is unused, and any finite data extend by
zero ranks and matrices. The order and ranges of quantification match the node.

Edge cases: e=2 leaves just reduced left-end injectivity, with an empty range
of internal exactness clauses. Every n i can be zero, including the entire zero
complex. e=0 and e=1 are excluded by the node itself. The zero ring has no
maximal ideal and hence is excluded by locality in both source and Lean.
For a field there is no regular x in its maximal ideal, as in the source.
No characteristic is excluded. Universe u is arbitrary and the coordinate
modules and quotient stay in that universe; no independent small-universe
quantifier is present. Empty schemes are not objects of this algebra statement.

Independent searches (recorded in searches.jsonl): LeanFinder for "Reduction
of an acyclic complex of finite rank free modules by a regular ring element
preserves acyclicity in degrees at least two" returned general acyclicity
lemmas, no match. Loogle for "Matrix.map, Function.Exact" returned no hits.
LeanSearch for "Exact finite free complex reduced modulo a regular element
is exact except at the last two terms" was unavailable (Internal Server
Error), not evidence of absence. Grep for
"map_first_exact_on_four_term|mod_nonzerodivisor|div_x_exact" found the
QuotSMulTop four-term candidate and its regular-sequence companion. I opened
IsSMulRegular.lean:173-183: the candidate is an exact pair on module quotients,
requiring separate identifications with finite coordinate modules and the
reduced matrices, not this finite-complex statement. Additional rg searches
for quotient complexes and regular-element exactness in WeilConjectures and
lean/Sheaf found no duplicate. The declaration name is also absent from
WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json.

Repairs: H8, expanded the theorem docstring from a brief mention of the short
and long exact sequences to all four node proof steps, including dependency
names and the endpoint argument. H9, added the standard copyright/license/
authors header. Moved this commutative-algebra module from AlgebraicGeometry
to RingTheory and updated lean.module and lean.file. The theorem signature
and mathematical node statement are unchanged. The node's lean.statement is
now exactly the signature up to := (its old value had a trailing space).
No new definition node or dependency module is needed: all notions exist and
all recorded dependencies are usable. There is one named theorem, by sorry,
no other proof and no hollow definition. Variables and universe u are bound.

Validation: the repaired file compiled on the server in 1.2 seconds, without
warnings. Delivery dry run and delivery recompile and run the preflight.
