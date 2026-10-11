## Worker report

The module states `HomologicalComplex₂.zigzag_trivial_if_row_boundary` for a homological double complex of `ModuleCat R`, a row-cokernel chain complex `C`, quotient maps `π`, commuting vertical maps, exact positive rows, and a zig-zag whose degree-n zeroth component is a vertical boundary in `C`; its conclusion is membership in `zigzagBoundaries`. The imported zig-zag notions are `HomologicalComplex₂.zigzagTotal`, `zigzagCycles`, and `zigzagBoundaries` from `Sheaf.Algebra.Homology.ZigzagModule`. The row exactness hypothesis is rendered by `ShortComplex.Exact` for the component horizontal maps; the boundary hypothesis is rendered by the displayed existential equality. The proof is intentionally `sorry`.

Edge cases checked: `n = 0` is admitted by the statement; zero modules and empty positive-row conditions are allowed; indices use `ℕ` and no finite-universe restriction is introduced. The chain map equation is only required for positive vertical degrees, matching the boundary at degree zero.

Searches: `msearch.py leanfinder "double complex exact rows zig-zag trivial boundary"` (no match); `msearch.py loogle "HomologicalComplex₂ zigzag cokernel"` (no match); `rg` over Mathlib and `WeilConjectures` for row-cokernel and zig-zag statements (only the project's `ZigzagModule` declarations). The dependency `def-weil-pbc-double-complex-zigzag-module` uses `Sheaf.Algebra.Homology.ZigzagModule`; `def-weil-pbc-exact-sequence` uses Mathlib `CategoryTheory.ShortComplex.Exact`; `def-weil-pbc-module-chain-complex-homology` matches Mathlib `HomologicalComplex.homology`.

## Earlier second reading (a previous round; superseded)

Read the node and module. The Lean binders correspond to the double complex, row-cokernel chain and quotient maps, commuting differential condition, exact positive rows, zig-zag cycle, and boundary conclusion. The source's row-cokernel universal property is represented by the explicitly supplied chain `C` and maps `π`; no additional object or characteristic hypothesis is introduced.

## Second reading by H1

Read the repository node, its two proof steps, all three statement-dependency
nodes, the delivered Lean file, the dependency module ZigzagModule.lean, and
Mathlib's HomologicalBicomplex, HomologicalComplex, ShortComplex.Exact,
exact_iff_image_eq_kernel, homology, and CokernelCofork.ofπ declarations.
The local literature directory does not contain algebra.tex; read the actual
project copy over SSH on the server, algebra.tex 18355–18512, and the preceding
setting at 18312–18358 in /home/ubuntu/c1-stacks-review/algebra.tex. The setting
has commuting squares, both differentials square zero, first-quadrant modules,
and row cokernels with the induced vertical differential. The larger lemma
also has exact columns, but this node is precisely its row-side injectivity
argument, which uses only exact rows. No column exactness belongs in this item.
The source's injectivity paragraph swaps some cokernel subscripts; the node's
explicit A_(1,q) → A_(0,q) convention agrees with the preceding definition of
R(A). Its + boundary convention agrees with the displayed quotient; the
source's later negative generator is the sign typo already documented in the
zig-zag dependency node. No change to the natural-language node is needed.

Object/hypothesis/conclusion inventory, with the final Lean rendering:

1. Commutative ring R: `{R : Type u} [CommRing R]`. PASS; no field,
   characteristic, finiteness, or Noetherian assumption.
2. First-quadrant commuting homological double complex of R-modules:
   `A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
   (ComplexShape.down ℕ)`. PASS. `(A.X p).X q` is A_(p,q),
   `(A.d p (p-1)).f q` is horizontal d, and `(A.X p).d q (q-1)`
   is vertical δ. The nested-complex definition enforces d² = δ² = 0
   and that each horizontal arrow is a vertical chain map, hence commutation.
   The ℕ shape encodes zero extension at the negative boundary.
3. Row cokernel objects and quotient maps: `C` is an ℕ chain complex,
   `π q : (A.X 0).X q ⟶ C.X q`, `hπzero q` says d_(1,q)π_q = 0,
   and `hπcokernel q : IsColimit (CokernelCofork.ofπ (π q) (hπzero q))`
   specifies exactly the cokernel universal property. FIXED, now PASS.
   This is an arbitrary presentation of the stipulated cokernel, uniquely
   isomorphic to Mathlib's chosen cokernel with its projection; it adds no
   mathematical hypothesis to the stipulated object. No private cokernel
   definition or new notion is introduced.
4. Induced differential: `hπ` is δ_(0,q) ≫ π_(q-1) = π_q ≫ C.d q (q-1)
   for q > 0. PASS. Epimorphic cokernel projections uniquely determine these
   maps; `C` also enforces square zero and the degree-zero shape condition.
5. The paragraph about morphisms Φ and their induced row-cokernel morphisms
   describes background functoriality, not a hypothesis or conclusion about
   the particular a. PASS: no unnecessary B or Φ parameter is introduced.
   The dependency's `zigzagTotalMap` and `zigzagMap` implement that background.
6. Every row exact at every p ≥ 1, q ≥ 0: `hrow : ∀ q p, 0 < p →
   (ShortComplex.mk ((A.d (p+1) p).f q) ((A.d p (p-1)).f q) ...).Exact`.
   PASS; its composite vanishes by the outer complex law. The recorded
   exact-sequence dependency includes `CategoryTheory.ShortComplex.Exact`;
   in ModuleCat its image = kernel interpretation is exactly the node's.
7. T_n, Z_n, B_n: use the existing `zigzagTotal A n`, `zigzagCycles A n`,
   `zigzagBoundaries A n` from Sheaf.Algebra.Homology.ZigzagModule. PASS:
   their direct-sum index is p+q=n, their relation is d a = δ a,
   and B_n is the range of the + boundary map. Opened and checked these
   definitions, not merely their names.
8. n ≥ 0 and a ∈ Z_n: `(n : ℕ) (a : zigzagTotal A n)` and
   `ha : a ∈ zigzagCycles A n`. PASS, with n before a and the boundary condition.
9. π_n(a_(0,n)) belongs to im δ^rt_(n+1): `hboundary` is existence of
   `y : C.X (n+1)` whose differential equals `π n` applied to
   `DirectSum.component R (ZigzagIndex n) ... ⟨(0,n), by simp⟩ a`.
   FIXED, now PASS. There is no unrelated existential component c.
10. Conclusion: `a ∈ zigzagBoundaries A n`. PASS, exactly the node's conclusion.

Mismatches found and repairs:

- H3: the original C and π were arbitrary, not row cokernels. Added hπzero
  and hπcokernel using Mathlib's existing cofork and universal property.
- H3: the original boundary condition was `∃ c, ∃ y, d y = π c`, satisfied
  by c = y = 0 independently of a. Replaced c with the actual (0,n)
  direct-sum component of a. These defects really made the old statement
  false: take R = ℤ, A concentrated at (0,0) = ℤ, and n = 0 with a = 1;
  the old boundary condition holds while B_0 = 0, even with the genuine C.
- H8/H9: added the standard copyright header, moved the module docstring
  directly after imports, and expanded the declaration docstring to give
  the source and both node proof steps with their cited node ids.
- Bound the independent ring and module universes explicitly as u and v.
  Dropped redundant direct imports of HomologicalBicomplex and ModuleCat.Basic;
  retained the chain-complex/homology dependency import, ZigzagModule, and
  the cokernel-cofork API import used by the repaired signature.
- Updated lean.statement verbatim from the final signature. The node's
  mathematical statement and all other fields are unchanged. No new nodes
  or dependency modules are needed. The earlier worker and earlier-reading
  claims that arbitrary π already represented cokernels are superseded here.

Edge cases: n = 0 has an empty zig-zag relation and no inductive elimination
steps; the initial two-component boundary lift suffices. For the concentrated
(0,0) example with genuine cokernel π = id, the repaired boundary hypothesis
forces a = 0, as required. Zero modules, the zero ring, and arbitrary
characteristic are included. The diagonal index set has n+1 positions and
is never empty for n : ℕ; a vanishing diagonal is allowed. There are no
scheme or nonempty-index hypotheses. Ring universe u and module universe v
are independent and explicitly bound; no auto-implicit variables remain.
The dependent direct-sum index proof uses only 0+n=n.

Independent searches (2026-10-11):

- LeanFinder via msearch.py: "bicomplex row exact cokernel projection detects
  zero homology class" returned eight single-complex homology/exactness lemmas,
  including homologyι_descOpcycles_eq_zero_of_boundary; none states this lemma.
- Loogle via msearch.py: `"CokernelCofork.ofπ"` returned the Mathlib declaration
  in Mathlib.CategoryTheory.Limits.Shapes.Kernels. Opened its definition:
  it is the standard cofork of a map annihilating the horizontal differential.
- LeanSearch via msearch.py: "In a first quadrant bicomplex with exact rows
  a zigzag is trivial if its image in the row cokernel complex is a boundary"
  was unavailable (Internal Server Error). No mathematical verdict inferred
  from the unavailable service.
- rg in Mathlib/Algebra/Homology, the whole source WeilConjectures tree,
  repository lean/Sheaf, and dag/lean_names_upstream.json, using zigzag,
  zig-zag, row/cokernel in both orders, trivial_if_row, 00M1 and
  lemma-no-spectral-sequence: no existing statement. The source's monoidal
  duality zigzag identities and category-connectivity zigzags are other notions.
  The project ZigzagModule declarations are the matching notions, already
  imported, not duplicated. Mathlib homology and ShortComplex.Exact signatures
  were read and match the two Mathlib dependency nodes.

Validation: the repaired 70-line module compiled on the project server with
scompile.py (exit 0, 1.3 seconds), with no errors or warnings. The sole theorem
proof remains sorry; no mathematical claim was proved, no data definition was
added, and all lines are at most 100 characters. Delivery dry run and final
submission are performed after this report is written.
