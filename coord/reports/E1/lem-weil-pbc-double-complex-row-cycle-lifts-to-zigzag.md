## Worker report

The module states `HomologicalComplex₂.row_cycle_lifts_to_zigzag` in
`Sheaf.Algebra.Homology.RowCycleLiftsToZigzag`.  Its `A` is a first-quadrant
homological double complex of `R`-modules, using the dependency declaration
`HomologicalComplex₂.zigzagTotal` and `HomologicalComplex₂.zigzagCycles` from
`Sheaf.Algebra.Homology.ZigzagModule`.

The hypothesis `hrow` renders exactness of every row at positive horizontal
positions: `LinearMap.range d_{p+1,q} = LinearMap.ker d_{p,q}` for all `p>0` and
all `q`.  The element `x : (A.X 0).X n` is the `(0,n)` entry.  The hypothesis
`hcycle` renders the row-cokernel cycle condition: in degree zero it is
automatic, and in positive degree it says that the vertical differential of
`x` lifts through `d_{1,n-1}`.  The conclusion supplies a total-degree `n`
element in `zigzagCycles A n` whose `(0,n)` direct-sum component is `x`.

Dependencies used: `Sheaf.Algebra.Homology.ZigzagModule`, declarations
`HomologicalComplex₂.zigzagTotal`, `HomologicalComplex₂.zigzagCycles`, and
`HomologicalComplex₂.ZigzagIndex`; `def-weil-pbc-module-chain-complex-homology`
and `def-weil-pbc-exact-sequence` are represented by Mathlib's homological
complex and range/kernel exactness declarations.

Edge cases checked: `n=0` is admitted by the disjunctive cycle hypothesis;
`n=1` requires only the first lift; the first-quadrant indexing makes all
components finite and includes zero modules at the boundary.

Searches: `msearch.py leanfinder` for “double complex exact rows cycle lifts to
zigzag” (no match); `msearch.py loogle` for `HomologicalComplex₂,
ShortComplex.Exact, cokernel` (no combined theorem); grep of Mathlib
`Algebra/Homology` for zig-zag/cokernel-row lifting (no match); `rg` over
`WeilConjectures` and `lean/Sheaf` for the node id and row-cycle lifting (no
existing declaration).  The existing zigzag definitions were therefore used.

## Earlier second reading (a previous round; superseded)

The reader checked the node and module line by line.  `A`, positive-row
exactness, the degree/index variables, the row-cokernel cycle disjunction, and
the existence of a zig-zag with prescribed `(0,n)` component all occur in the
Lean signature.  No hypothesis or conclusion clause was omitted.


## Second reading by E1

Read the item node, its five proof steps, the sandbox module, all three
statement-dependency nodes and the signatures they record. Read Stacks
`algebra.tex` at `lemma-no-spectral-sequence`, including the preceding
commuting-double-complex and cokernel conventions, the surjectivity proof
(lines 18464--18481), and the chapter's convention that rings are commutative
with 1, including the zero ring. The locally available source copy is
`/home/ubuntu/c1-stacks-review/algebra.tex`; `tags/tags` line 807 verifies 00M1.
The containing lemma also assumes exact columns for its other isomorphism;
this extracted row-lifting argument uses only exact rows, as the node states.

Object/hypothesis/conclusion inventory, matched item by item:

1. Commutative ring R: `{R : Type*} [CommRing R]`. Matches exactly; no
   nontriviality, field, characteristic, finiteness or Noetherian assumption.
2. First-quadrant modules A_{p,q}, horizontal d and vertical delta:
   `A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
   (ComplexShape.down ℕ)`. Mathlib's `HomologicalComplex₂` is an iterated
   homological complex, with `(A.X p).X q` its (p,q) module,
   `((A.d p (p-1)).f q).hom` its horizontal map and
   `((A.X p).d q (q-1)).hom` its vertical map. Opened
   `HomologicalBicomplex.lean` and `HomologicalComplex.lean`: the outer and
   inner `d_comp_d'` fields impose the two square-zero conditions, and the
   inner complex morphism's `comm'` imposes COMMUTING squares, not
   anticommuting squares. Matches. The natural-number shapes encode
   concentration in nonnegative degrees; negative positions are omitted
   rather than additional data, exactly equivalent to extension by zero.
   Off-shape maps, including boundary self-maps, are zero by `shape`.
3. The contextual morphism Phi and its induced cokernel-complex morphism:
   the node describes these conventions but neither assumes a given Phi
   nor asserts a conclusion about it. Correctly no unused Phi binder.
4. Right-edge cokernel, projection pi and induced vertical differential:
   these are eliminated in the hypothesis rather than privately redefined.
   For n>0, delta^rt(pi(x))=pi(delta(x))=0 iff delta(x) lies in the image of
   d_{1,n-1}, iff there exists y with d(y)=delta(x). Precisely this is the
   second disjunct of `hcycle`. Read `Submodule.ker_mkQ` in
   `Mathlib.LinearAlgebra.Quotient.Basic` and the chain-complex/homology
   dependency's `HomologicalComplex.homology` and `cycles` signatures in
   `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`. No additional
   chosen lift is an input, and no hypothesis is strengthened. No missing
   definition node is necessary for this equivalent elementwise condition.
5. Exactness of every row at every positive horizontal position:
   `hrow : ∀ (p q : ℕ), 0 < p → LinearMap.range
   ((A.d (p+1) p).f q).hom = LinearMap.ker
   ((A.d p (p-1)).f q).hom`. Matches every q and every p>=1, with no
   exactness at p=0. Read the dependency's recorded `ShortComplex.Exact`
   notion and `ShortComplex.moduleCat_exact_iff_range_eq_ker` in
   `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`: this is exactly its
   specialization to modules, not a new definition of exactness.
6. Degree n>=0 and representative x in A_{0,n}: `(n : ℕ)` followed by
   `(x : (A.X 0).X n)`. Matches the node's order and range of quantifiers.
7. pi_n(x) is a cycle: `hcycle : n = 0 ∨ ∃ y : (A.X 1).X (n-1),
   ((A.d 1 0).f (n-1)).hom y = ((A.X 0).d n (n-1)).hom x`.
   Matches by item 4, including the unconditional degree-zero case.
8. T_n(A), Z_n(A), and contextual B_n(A): the imported dependency module
   `Sheaf.Algebra.Homology.ZigzagModule` supplies `ZigzagIndex`, `zigzagTotal`
   and `zigzagCycles` directly. Opened its declarations: the direct sum is
   over exactly p+q=n; `zigzagRelation` is horizontal image MINUS vertical
   image, and `zigzagCycles` is the common zero locus of those relations.
   Thus it uses exactly the node's unsigned equality between adjacent
   images. B_n is not used in this theorem's hypothesis or conclusion.
9. Conclusion: `∃ a : zigzagTotal A n, a ∈ zigzagCycles A n ∧
   DirectSum.component R (ZigzagIndex n) ... ⟨(0,n), by omega⟩ a = x`.
   Matches both clauses: a is a zig-zag and its actual (0,n) component equals
   the GIVEN representative x, not just its class. No quotient, uniqueness,
   or naturality conclusion has been substituted.

Edge cases: n=0 has a single (0,0) component and no zig-zag relations;
`hcycle` is automatically true. At n=1 only the first lift is needed.
There is no empty diagonal for natural n since (0,n) always belongs; zero
modules and the zero ring are admitted. No scheme or scheme-emptiness
hypothesis applies. Every characteristic is admitted. Compiled a scratch
`#check` with `pp.universes`: the theorem has independent ring and module
universes `u_1,u_2`, and `zigzagTotal` has the same independent universes.
No universe restriction or unbound variable was found.

Independent searches (using different terms from the first worker):

- LeanSearch via msearch: "Lifting a representative of a cycle in the
  horizontal cokernel of a commuting bicomplex with acyclic positive rows
  to compatible diagonal components". Service unavailable (HTTP Internal
  Server Error); recorded as unavailable, not a no-match verdict.
- Loogle via msearch: `HomologicalComplex₂, LinearMap.range`: zero hits.
- LeanFinder via msearch: "Surjectivity of diagonal compatible elements
  onto cycles of a row quotient in an exact first quadrant double complex".
  Eight hits: short-complex surjectivity-to-cycles, short-exact surjectivity,
  and five-lemma results. Opened the relevant module-category exactness
  signatures; none states this bicomplex lifting theorem.
- Mathlib grep via msearch: `bicomplex|acyclic|zig.?zag` in Algebra/Homology.
  Results concern total/shifted bicomplexes and acyclic homotopy categories,
  not this lift. Also independently searched source `WeilConjectures`,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `row_cycle|cycle.*lift|lift.*cycle|no_spectral|00M1|zigzagCycles`.
  Only the already imported zig-zag definitions and unrelated one-complex
  cycle lifts occur; no existing declaration states this theorem.

Mismatches and changes: H8 found: the original docstring summarized the
induction but omitted the n=0 case, precise partial-tuple claim, kernel-of-
projection first lift, commutation/square-zero calculation, and final tuple
assembly. Expanded it to carry all five node proof steps, with dependency
ids and source place. H9 found: `Mathlib.Algebra.Homology.ShortComplex.Exact`
was an unused import; removed it. No mathematical signature, node statement,
or node record changed. The recorded `lean.statement` was checked verbatim
against the theorem signature. There are no new nodes or dependency modules,
no hollow definitions, and the sole theorem proof remains `by sorry`.

Validation: the repaired module compiles on the project server with no
errors or warnings. The scratch universe check also compiled cleanly.

## Reviewer fix (R-drz0953)

The second reading accepted two elementwise re-renderings that replace the node's objects. (1) `hcycle` eliminated the row-cokernel complex A^rt and π_n into "∃ y, d y = δ x"; the node says π_n(x) is a cycle of A^rt. Restated with A^rt = `A.opcycles 0` (degree q = Coker(d_{1,q}) in the abelian category of chain complexes, the form of the sibling G1 zigzag-to-row-cokernel-map), π = `A.pOpcycles 0`, and the cycle condition `∃ c : (A.opcycles 0).cycles n, (A.opcycles 0).iCycles n c = (A.pOpcycles 0).f n x` (at n = 0 automatic, as the node's disjunct says). (2) `hrow` was a hand-written range = ker; restated as Mathlib's `ShortComplex.Exact` of A_{p+1,q} → A_{p,q} → A_{p-1,q} for p ≥ 1 (the recorded exactness notion, as in H1's sibling zigzag-trivial-if-row-boundary). Conclusion and zig-zag notions unchanged (recorded `zigzagTotal`/`zigzagCycles`/`ZigzagIndex`).
