## Worker report

The module states `CategoryTheory.filteredHomotopy_spectralSequence_map_eq`.
It uses `C : Type u` with `[Category.{v} C] [Abelian C]`, cochain complexes `K L`,
and decreasing filtrations `F G`. The hypotheses `hKF` and `hLG` render the
node's degreewise boundedness using `DecreasingFiltration.complexStep`, with a
top and bottom step in every degree. The filtered maps are
`FilteredObject.Hom ⟨K,F⟩ ⟨L,G⟩`; `H : Homotopy a.hom b.hom` renders the chain
homotopy equation. The hypothesis `hshift` says explicitly that each homotopy
component on `F^p K^n` factors through `G^(p-1) L^(n-1)`, rendering the
one-step filtration decrease. The conclusion quantifies over every
`FilteredPageTwoModel C` and asserts equality of the induced spectral-sequence
morphisms, hence equality on all pages from page 2 onward.

Dependency declarations used: `Sheaf.CategoryTheory.Filtration`, declarations
`CategoryTheory.DecreasingFiltration`, `CategoryTheory.FilteredObject.Hom`,
and `CategoryTheory.DecreasingFiltration.complexStep`; and
`Sheaf.CategoryTheory.FilteredPageTwoModel`, declaration
`CategoryTheory.FilteredPageTwoModel`. The homotopy notion is Mathlib's
`CategoryTheory.Homotopy` from `Mathlib.Algebra.Homology.Homotopy`.

Edge cases checked: the bounds may depend on the cochain degree; no nonempty
index or positive degree is assumed; `p` ranges over all integers, including
negative values; zero filtrations and zero complexes are allowed; the shift is
exactly one step for every integer `p`.

Searches made: `leanfinder` for filtered chain homotopies inducing equal maps
on spectral sequences (homotopy-invariance declarations only, no match);
`loogle` for `SpectralSequence` and filtered homotopy (0 hits); grep of
Mathlib homological algebra for spectral homotopy (no filtered spectral-sequence
statement); `rg` over `WeilConjectures` and `lean/Sheaf` (no existing
statement with this node's conclusion). `grep -rl` over `dag/nodes` found only
the item and its citer `lem-sp-cartan-eilenberg-comparison-independence`.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. The two boundedness clauses match the
node's per-degree finite bounds, the filtered-map and homotopy binders supply
exactly `a,b` and `h`, and `hshift` is the clause
`h^n(F^p C^n) ⊆ F^(p-1) D^(n-1)` expressed by factorization through the
recorded subobjects. The conclusion is the induced map equality for every
page-two spectral-sequence model. No mismatch was found.


## Second reading by E1

Read the item node and its source with the Lean file open. The Stacks checkout is
not present under this clone's literature directory; I read the available full
Stacks source `/home/ubuntu/c1-stacks-review/homology.tex`, including labels
`lemma-spectral-sequence-filtered-complex-functorial` (012O),
`definition-filtration-cohomology-filtered-complex`,
`definition-filtered-complex-ss-converges` (012U), and the adjacent finite-filtration
convergence lemma. These assume an arbitrary abelian category, not a field,
Grothendieck category, or existence of countable sums. The countable-sums
hypothesis in the preceding d1 lemma is not assumed by 012O.

Object, hypothesis and conclusion checklist:

| Node clause | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary abelian category | `C : Type u`, `[Category.{v} C] [Abelian C]` | Exact; independent object and morphism universes. |
| Two cochain complexes | `K L : CochainComplex C ℤ` | Exact; no lower bound on cochain degrees. |
| Decreasing filtrations by subcomplexes | `F : DecreasingFiltration K`, `G : DecreasingFiltration L` | Exact: the steps are subobjects in the abelian category of complexes, not arbitrary degreewise subobjects. |
| Each filtration finite in each cochain degree | `hKF`, `hLG`: for every `n`, two integer steps with `complexStep = ⊤` and `complexStep = ⊥` | Exact; bounds may depend on degree and on the complex. |
| Two filtered chain maps | `a b : FilteredObject.Hom ⟨K,F⟩ ⟨L,G⟩` | Exact; underlying maps are morphisms of complexes, and `preserves` factors each step through its target step. |
| Maps h of degree minus one | `H : Homotopy a.hom b.hom`, component `H.hom n (n-1)` | Exact; Mathlib's `zero` field sets other components to zero. |
| a-b = d h + h d | `H.comm` | Exact: its additive equation is `a.f n = dNext + prevD + b.f n`. |
| h sends F^p into G^(p-1) | `hshift`: factorization through `G.complexStep (p-1) (n-1)` | Exact subobject form of the inclusion, in every integer p and n. |
| Equal induced maps on every E_r, r >= 2 | First conjunct: every `M : FilteredPageTwoModel C` has `M.S.map a = M.S.map b` | Exact; `SpectralSequence.Hom.hom` contains all pages r >= 2 and equality is componentwise. |
| Equal induced maps on filtered abutments | Second conjunct: `AF`, `BF` are pinned at every p to the image of `homologyMap` of the filtration inclusion; there exists one filtered map `t` with underlying map equal to both `homologyMap a.hom n` and `homologyMap b.hom n` | Repaired missing clause; a common filtered map says precisely that the two maps agree. |
| Equal induced maps on associated graded pieces | For every p there exists one `g : AF.gradedPiece p ⟶ BF.gradedPiece p` with the cokernel projection equation for the restriction of common t | Repaired missing clause. The filtration-step inclusion is mono, so the chosen restriction is unique; the cokernel projection is epi, so g is uniquely determined and is the map induced by both a and b. |

The universal `AF` and `BF` binders are presentations of the source's fixed image
filtrations: their steps are specified, not additional hypotheses on K or L.
These filtrations exist since images of the inclusions decrease with p. Neither
the cohomology map nor the graded map is arbitrary: the underlying-map equations
and the quotient-projection equation pin them to the source's induced maps.
The existence of the common maps is equivalent to their equality and adds no
conclusion beyond filtration preservation and equality already asserted by the
node. No additional convergence choice or arbitrary E-infinity isomorphism is
used. `def-sp-convergence`'s recorded exact-couple predicate is not appropriate
as a replacement for these concrete maps; the Stacks definition identifies the
abutment with filtered total cohomology. I read its node and the signatures of
`imageFiltration`, `WeaklyConvergesTo`, `AbutsTo`, and `ConvergesTo` in
`Sheaf.CategoryTheory.ExactCoupleConvergence`.

Dependency checks: opened `Sheaf.CategoryTheory.Filtration` and its node;
`DecreasingFiltration`, `FilteredObject.Hom`, and `gradedPiece` are exactly the
recorded filtration, morphism and quotient notions. Opened the entire
`Sheaf.Algebra.Homology.FilteredComplexSubquotients` and its node; `complexStep`
is the image of the subcomplex inclusion in degree n and is the required
boundedness/shift subobject. Opened the entire `Sheaf.CategoryTheory.FilteredPageTwoModel`
and its node; its page isomorphisms, quotient projection equations, differential
and naturality fix the induced maps (they are not arbitrary functors). Added
`def-sp-filtered-complex-subquotients` and `def-sp-filtered-page-two-model` to the
item's statement dependencies, since both landed definitions appear in its
signature. No definition or dependency module is delivered or duplicated.

Edge cases: zero complexes and zero filtration steps are allowed; the top and
bottom steps may coincide for a zero object. All p and n are integers, including
0 and negative values. No empty-index/nonempty-index assumption exists: the
filtration index is the source's fixed integer set. The zero abutment and its
zero graded pieces are covered by the same mono/epi uniqueness equations. An
empty scheme and characteristic constraints are inapplicable: the lemma is
categorical, hence also covers categories arising from any characteristic and
empty schemes. No universe equality or smallness hypothesis was introduced.

Independent searches (actual msearch invocations recorded in searches.jsonl):

- LeanFinder: "A chain homotopy lowering a filtration by one gives identical
  morphisms on the second and later spectral sequence pages": eight hits, headed
  by `AlgebraicTopology.DoldKan.homotopyPToId_eventually_constant` and ordinary
  `Homotopy.mkInductiveAux`/homotopy-cofiber declarations; none matches.
- Loogle: `Homotopy, homologyMap`: zero hits, unknown identifier `homologyMap`;
  this does not establish absence by itself.
- LeanSearch: "Filtered homotopic morphisms with filtration shift minus one agree
  on all spectral sequence pages starting at two and on filtered cohomology":
  service returned Internal Server Error; unavailable, no mathematical verdict.
- Mathlib grep: `homotop.*spectral|spectral.*homotop`: four text hits in
  `HomotopyCategory/SpectralObject.lean`. Opened that file: it constructs the
  mapping-cone spectral object, not the one-step shifted homotopy theorem.
- Independent rg over `WeilConjectures`, `lean/Sheaf`, and upstream name records:
  searched `homotop.*spectral|spectral.*homotop`, `homologyFiltration`,
  `cohomologyFiltration`, and the declaration name. No existing statement of this
  lemma. The project Cartan--Eilenberg statement cites this lemma in its proof
  and is specialized to resolutions, not this general statement.
- Opened Mathlib `Homotopy.homologyMap_eq`: this gives equality only on total
  homology. It supplies part of the future proof but not the page/filtration/graded
  statement, so existing:true would be incorrect.

Mismatches and repairs: the worker conclusion lacked both abutment clauses;
added the common filtered cohomology map and its common graded quotient maps.
The worker docstring and the node's proof step 2 claimed finite-page classes can
be represented by genuine cocycles. This is false in general: an r-cycle only
has dx in F^(p+r), even for a finite filtration. Replaced the docstring calculation
with `(a-b)x = d(hx)+h(dx)`, where h(dx) lies in F^(p+r-1), hence F^(p+1), and
hx lies in F^(p-r+1). This proves the same node statement without modifying the
node's statement or proof fields. The node proof's genuine-cocycle sentence
should be read as this corrected r-cycle calculation; no statement dispute
remains. Added the two missing recorded definition dependencies. Kept all correct
hypotheses and imports. No data definition, local notation, private declaration,
local instance, or new proof was introduced. The sole theorem remains `by sorry`.
The Lean record's statement was refreshed verbatim from the final signature.

Validation: server single-file compile passed cleanly (84 lines, 1.3 seconds),
with no errors or disallowed warnings. Inspected all variable/universe binders
and the unique graded-map equation by eye. The dry-run preflight and delivery
are run after this report is appended.
