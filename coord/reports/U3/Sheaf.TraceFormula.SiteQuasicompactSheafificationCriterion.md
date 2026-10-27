## What changed

Proved `CategoryTheory.site_quasiCompact_iff_sheafifiedYoneda_quasiCompact` in
`Sheaf.TraceFormula.SiteQuasicompactSheafificationCriterion` without changing its statement.
The proof follows all three steps of the current DAG: apply the covering-lift criterion,
restrict sections along the finite-image refinement, and use an epimorphic finite family of
sheafified arrows to obtain an actual covering refinement.

Added private proof imports of `Sheaf.CategoryTheory.Sites.EpimorphicFamilyCoverLifts`
and `Sheaf.CategoryTheory.Sites.SheafifiedArrowsCoverRefinement`. Their universe parameter
uses `uliftYoneda.{max u v}`, whereas the item uses `uliftYoneda.{u}`. An explicit
presheaf isomorphism and a proved private isomorphism-invariance lemma transport
quasi-compactness between these two encodings. No shared interface changes.

The source read was Stacks `sites.tex`, Definition 090H and Lemma 0D06, including the
finite-image refinement condition, rather than a finite-subcover condition. The current
unit record and latest blueprint unit were read; the unit route is retained.

## Proved and sorry left

Closed one existing hole:
`CategoryTheory.site_quasiCompact_iff_sheafifiedYoneda_quasiCompact`
(node `lem-trf-site-quasicompact-sheafification-criterion`).
There are zero holes left in the item and zero holes added. The private theorem
`quasiCompact_iso_iff` is completely proved.

The proof uses the existing declarations
`CategoryTheory.site_epimorphic_family_iff_cover_lifts`
(node `lem-trf-site-epimorphic-family-cover-lifts`) and
`CategoryTheory.sheafified_arrows_cover_refinement`
(node `lem-trf-site-sheafified-arrows-cover-refinement`). Those declarations currently
have their own holes; they are the current DAG's designated next proof obligations,
not new holes in this delivery.

## No longer needed

Removed the direct private imports `Mathlib.CategoryTheory.Sites.LocallySurjective`
and `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` from the item.
Local surjectivity, local representation, and local equality are now encapsulated in
the two existing DAG dependencies. Neither dependency nor its supporting mathematics
is claimed to be globally pruned. No node or module is withdrawn; both current
`proof_deps` are used, and the DAG's proof route is unchanged.

The required shorter-route searches ran through `msearch.py` using LeanFinder, Loogle,
and grep, and local `rg` searched the source library and Sheaf tree. No direct theorem
was found; the hits concerned quasi-compact schemes. The two declared dependency
statements already provide the planned shorter assembly.

## Where the brief, the DAG or earlier work was wrong

The item's existing docstring gives the older expanded two-direction argument, while
the current DAG has already extracted its local lifting and covering-refinement steps
into two lemmas. The proof uses that current three-step DAG plan. No mathematical
statement repair was necessary. The differing ULift universe parameters require the
explicit isomorphism described above; they are not definitionally equal.

Empty coverings and empty selected finite sets require no nonemptiness assumptions:
the proof uses finite images and the existing covering criteria directly. All original
public imports and the exact theorem signature are retained.

Validation: `lcompile.py` compiled the final module cleanly in 3.0 seconds with no
warnings. A direct comparison verified that the theorem signature is byte-for-byte
unchanged; all Lean lines are at most 100 characters.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
