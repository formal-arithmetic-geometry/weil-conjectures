## What changed

Replaced the hole in `CategoryTheory.Functor.secondFiltration_row_cohomology` with
a complete Lean assembly of the required spectral sequence from concrete
cycle/boundary quotient pages. Page zero is constructed from graded-piece terms;
its differential and square-zero identities are checked directly. The existing
`filteredComplex_graded_homology` identifies its homology with page one. For all
positive pages the existing uniquely specified representative differentials and
`filteredComplex_page_homology` provide the page complexes and successor
isomorphisms. Positive-page quotient comparisons are identities.

Proved the negative-resolution-degree clause directly: the interval `[p,p+q]`
is empty for `q<0`, hence the filtration step, graded term, cycle subobject, and
cokernel quotient are zero. The private helper
`gradedPiece_isZero_of_complexStep_eq_bot` proves the required step-to-graded
vanishing using the mono inclusion and epic graded projection.

Added one strictly smaller computation in
`Sheaf.CategoryTheory.SecondFiltrationSignedFirstPage`: it concerns only the
concrete first page with its representative differential. The existing theorem
retains every original binder, universe, conclusion, and visibility. It now
combines this one-page calculation with the complete page construction and the
independently proved negative-degree clause.

Replaced the general spectral-sequence public import by its statement dependencies;
see `coord/changes/second-filtration-row-imports.md`. Updated the item's node proof,
proof dependencies, and proof origin to follow the actual Lean argument.

Validation: both delivered modules compile cleanly with `lcompile.py --all`. The
unchanged direct importer `Sheaf.CategoryTheory.CartanEilenbergRowPages` also
compiles against the sandbox overlay, confirming that no adaptation is required
for the public-import replacement. `deliver3.py --no-push` printed OK (only the
second reader's section remains to be written); nothing was pushed.

## Proved and sorry left

Closed original hole:
`CategoryTheory.Functor.secondFiltration_row_cohomology`
(node `lem-sp-second-filtration-row-cohomology`). Its proof now contains no `sorry`.

Proved private helper:
`CategoryTheory.Functor.gradedPiece_isZero_of_complexStep_eq_bot`.

Added and left one hole:
`CategoryTheory.Functor.secondFiltration_signed_firstPage`
(node `lem-sp-second-filtration-signed-first-page`), in the new module
`Sheaf.CategoryTheory.SecondFiltrationSignedFirstPage`.

This is a decomposition: one upper hole closed and one strictly smaller hole added,
net zero new holes removed. The page assembly, page-zero comparison, higher-page
quotient clauses, and negative-degree vanishing are proved in Lean. Existing
imported page-differential, successor-homology and first-page kernel/image lemmas
retain their existing holes; this delivery does not add holes to those modules.

## No longer needed

Removed import `Sheaf.CategoryTheory.FilteredComplexSpectralSequence` and the
redundant direct proof import `Sheaf.CategoryTheory.DoubleComplexTotal`.
`Sheaf.Algebra.Homology.FilteredComplexSubquotients` is retained as a public
statement dependency instead of a redundant proof import.

The proof no longer needs the general existential construction node
`lem-sp-filtered-complex-associated-spectral-sequence-construction`
(module `Sheaf.CategoryTheory.FilteredComplexSpectralSequence`) or the
positive-pages assembly node `lem-sp-filtered-complex-positive-pages`
(module `Sheaf.CategoryTheory.FilteredComplexPositivePages`). Both modules are
absent from the new import closure of this item. This is local pruning; other
users may still need them. The DoubleComplexTotal module and its definition node
are still needed through CartanEilenbergPresentation and the one-page computation.
No other module is pruned from this item's import closure.

## Where the brief, the DAG or earlier work was wrong

The general associated-spectral-sequence theorem exposes quotient objects but
not a representative equation for its page-one differential. Consequently one
cannot simply apply its existential witness and assert that its differential is
the signed row map. The proof instead uses the specified
`FilteredComplexPageDifferential` record for every positive page.

Read Stacks `homology.tex`, `lemma-ss-double-complex` (Tag 0130), clauses 2 and 4,
and the filtered-complex representative formulas (Tag 012K), using the local
Stacks source. Tag 0130 omits its proof; the new node and theorem docstring write
out the diagonal-summand, kernel/image, cokernel, and cycle-representative argument.
The inherited unit record `sk-prop-av-pqf-finite` has empty `realized` lists and
provides no additional route step to bypass; the unit record was not changed.

## New nodes

`lem-sp-second-filtration-signed-first-page` identifies only the actual first-page
quotient objects with row cohomology and computes their specified differential.
It has no spectral-sequence existence assertion, page-zero clause, higher pages,
or negative-degree vanishing clause. Its detailed proof uses the diagonal
coprojections, the first-page kernel/image calculation, and the representative
equation. Edge cases checked in the mathematical argument: the zero bicomplex;
resolution degree zero (unit sign and zero incoming extension term); negative
complex index s (no first-quadrant assumption on s); and zero rows. No arbitrary
witness of a mere existence statement is used as a public definition.

Searches were run through `msearch.py`: LeanFinder returned total-complex
sign formulas, Loogle returned short-complex homology comparisons, and grep
returned general spectral-sequence interfaces. LeanSearch returned an internal
server error, recorded as unavailable. Repository and blueprint searches found
no existing concrete signed first-page theorem. The signed computation is stated
as a new node, not duplicated from the full spectral-sequence assertion.

Change record: `coord/changes/second-filtration-row-imports.md`.

## Second reading by E1

1. Compared the delivered `SecondFiltrationRowCohomology.lean` against the repository
   with `diff -u` and separately compared the complete theorem signature as bytes.
   Every binder, universe, typeclass, conjunction, index and visibility is unchanged.
   The only existing-node changes are `proof`, `proof_deps` and `proof_origin`.
   The public-import replacement has its change record. `downstream.py --uses`
   confirms that CartanEilenbergRowPages is the only external textual user; it
   separately imports FilteredComplexSpectralSequence. Verdict: no accidental
   interface or target change.

2. Read both delivered modules completely. Compiled both with `lcompile.py` and
   compiled scratch copies with explicit `#print axioms` for the original theorem,
   the new theorem and the private vanishing helper. The helper uses only
   `propext`, `Classical.choice`, `Quot.sound`; the two public theorems additionally
   use `sorryAx`, exactly as expected from the remaining named hole and imported
   open page lemmas. The original theorem has no local hole, the new theorem has
   exactly its one reported `sorry`, and there are no forbidden declarations or
   hollow definitions. In particular, D is chosen from an existence-and-uniqueness
   theorem on fixed concrete quotient objects; the local spectral sequence E is
   a real record construction, not an arbitrary existential spectral sequence.
   Verdict: valid conditional assembly, explicitly a decomposition rather than
   a proof free of `sorryAx`.

3. Read the local Stacks source at
   `/home/ubuntu/work-bp/sheaf/literature/stacks-project/homology.tex`,
   `lemma-ss-double-complex` clauses 2 and 4, and the displayed representative
   formulas preceding `lemma-spectral-sequence-filtered-complex` (Tags 0130 and
   012K). After flipping, resolution degree is the first coordinate of J, so
   the graded differential has coefficient one and the surviving page-one map
   has coefficient `(-1)^r`, as stated. The proposed diagonal projection/lift
   argument uses no injectivity or augmentation. For r=0 the incoming extended
   term is zero and the sign is one; for a zero row or zero bicomplex both sides
   vanish. Negative s is allowed: only the resolution coordinate must be
   nonnegative, and the step's interval is [s,s+r]. The bounded-below hypothesis
   makes each nonzero total diagonal finite. The new assertion fixes only one
   actual quotient page and its representative differential; it does not
   restate spectral-sequence existence, higher-page homology or negative-degree
   vanishing. Its source, complete proof docstring and matching node are present.
   Repeated independent searches with LeanFinder ("associated graded of total
   complex filtration computes homology of rows differential"), Loogle
   (`HomologicalComplex₂, HomologicalComplex.homology`), and grep
   (`graded.*[Hh]omology|[Hh]omology.*graded|second.*[Ff]iltration`), plus repository
   and upstream `rg`, found total-complex tools and gradedHomologyFunctor but no
   theorem giving this concrete signed comparison. The existing
   secondFiltration_graded requires first-quadrant vanishing and does not compute
   this page-one differential. This remaining calculation cannot be closed by a
   short application of those results. Verdict: true, strictly smaller split.

4. Checked the proof from its conclusion down: the explicit P supplies page zero;
   filteredComplex_graded_homology supplies its successor; the uniquely specified
   D and filteredComplex_page_homology supply every positive successor. Quotient
   comparisons are reflexive, and the empty-interval/mono/epi proof independently
   establishes q<0 vanishing. The general existential theorem would lose the
   representative equation needed for the signed comparison. A source-import
   closure comparison confirms exactly two removed modules:
   FilteredComplexSpectralSequence and FilteredComplexPositivePages; both are
   already listed under No longer needed. The old proof-dependency union loses
   only the general construction node, also listed there. Read the blueprint
   thm-sp-if-e1 row-computation paragraph and the inherited unit's empty realized
   entries; the row-cohomology route remains and the unit is unchanged. Public
   imports are statement dependencies; remaining imports are proof dependencies.
   Verdict: route kept and local pruning correctly reported.

5. Checked each node's recorded Lean statement against its module, and each
   proof_deps list against the union of its proof steps' uses. The original
   node describes the actual P/D/E construction and the independent negative
   clause; the new node describes just the signed quotient calculation. Its
   source, origin, searches, creation record, blueprint ancestry, chapter, unit
   and Lean record are present. Verdict: DAG and Lean agree.

Second-reading repair: added the plain proof import
`Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries` to
SecondFiltrationSignedFirstPage, because its node and proof docstring use that
existing kernel/image calculation. No statement, definition or proof was changed.
Recompiled the unchanged direct importer CartanEilenbergRowPages against the
sandbox overlay: clean. No further holes were added or closed by this reading.
