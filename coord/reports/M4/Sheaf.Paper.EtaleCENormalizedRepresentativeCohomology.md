## What changed

Replaced the sorry in
`AlgebraicGeometry.Etale.exists_etaleCE_normalized_representative_cohomology`
with a complete composition proof. Its existing signature and docstring are unchanged.
The proof obtains signed comparisons with actual sections-row homology, rewrites the
first-page comparisons through those row comparisons, applies the ordinary row
naturality square, and postcomposes the row representative equation. The resulting
categorical equality is the original equation from every test object.

Added `Sheaf.Paper.EtaleCERowOrdinaryComparison` with explicit constructions
`ceRowOrdinaryIso`, `ceRowSectionsMap`, and `cePresentationRow`, and the row naturality
statement. The iso is built from extension homology, mapExtendIso, evaluation at 1 and
the specified resolution's Ext equivalence. No data is chosen from an unproved
existence theorem. Added `Sheaf.Paper.EtaleCENormalizedRowRepresentatives` with the
normalized CE construction and the representative calculation in row homology.
These are strictly different parts: the construction's representative conclusion
contains a row homology map, while row naturality involves two single injective
resolutions and no filtration, spectral sequence, total, or representatives.

Replaced the public import of `EtaleCEStationaryPageNaturality` by
`EtaleCETotalSections`, which supplies the actual statement's CE total types. Added a
proof-only import of the new normalized row construction. The direct importer
`EtaleCEPrescribedNormalizedFirstPages` already publicly imports the stationary-page
module itself. Updated the parent node's proof route to the two parts and their
explicit composition. No existing statement or definition has been changed.
The public-import pruning has a change record at
`coord/changes/EtaleCENormalizedRepresentativeCohomology-imports.md`.
The sole direct importer compiled unchanged against the delivered overlay.

The modules were compiled locally with lcompile.py. The top proof needs full unfolding
only for the final associativity comparisons, because the representative page object's
cokernel and the differential's page object agree definitionally through semireducible
categorical colimit constructions. The unused-variable option retains the original
signature's dependent binders without compiler warnings.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_etaleCE_normalized_representative_cohomology`
(node `lem-weil-pbc-ce-normalized-representative-cohomology`). No sorry remains in the
item's module.

Added two named holes, both with complete source-based proof plans in their docstrings:

- `AlgebraicGeometry.Etale.ceRowOrdinaryIso_naturality`, node
  `lem-weil-pbc-ce-row-ordinary-naturality`, in
  `Sheaf.Paper.EtaleCERowOrdinaryComparison`.
- `AlgebraicGeometry.Etale.exists_etaleCE_normalized_row_representatives`, node
  `lem-weil-pbc-ce-normalized-row-representatives`, in
  `Sheaf.Paper.EtaleCENormalizedRowRepresentatives`.

This delivery is a decomposition: one upper hole closed, two strictly smaller holes
added (net minus one). It is not a complete proof with only the three allowed axioms.
All definitions in the delivery are actual constructions; none contains sorry.

## No longer needed

Removed import `Sheaf.Paper.EtaleCEStationaryPageNaturality`: the representative
calculation does not use stationary pages or abutment naturality. Its node
`lem-weil-pbc-ce-stationary-page-naturality` and module are unnecessary for this
module's route; other importers may still need them.

The former dependency `lem-weil-pbc-sheafH-ext-derived-comparison` and module
`Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison` are unnecessary for this
route: the explicit row Ext/sections comparison replaces an abstract comparison with
derived global sections. The parent now directly needs only the two new nodes.
The other former proof dependencies are retained below the new nodes: the generic
hypercohomology construction, row pages, graded homology, page differential,
normalized homology, Ext-to-sections construction and pullback computation.
No claim is made that these modules are globally unreachable.

For completeness, the old dependencies retained transitively are
`def-weil-pbc-ext-resolution-sections-iso`, `lem-sp-cartan-eilenberg-row-pages`,
`lem-sp-filtered-complex-graded-homology`, `lem-sp-filtered-complex-normalized-homology`,
`lem-sp-filtered-complex-page-differential`, `lem-weil-pbc-ext-pullback-resolution-sections`
and `thm-sp-if-e1`. The old dependency omitted altogether from the new route is
`lem-weil-pbc-sheafH-ext-derived-comparison`; stationary-page naturality was an import,
not an entry in the old proof_deps. No additional old dependency was silently discarded.


## Where the brief, the DAG or earlier work was wrong

The existing generic hypercohomology and row-page existence interfaces do not retain
representative equations or normalized successor comparisons. Their objectwise
Nonempty quotient comparisons alone cannot identify supplied page maps. The new
construction records the precise missing row-homology compatibility; the proof does
not assume it for arbitrary pre-existing CE presentations or arbitrary choices of j.
The Ext pullback/sections theorem already in the library handles chosen resolutions
and the pulled-back coefficient sheaf. The new single-row statement additionally
handles arbitrary prescribed injective resolutions and a coefficient map into an
arbitrary target sheaf; its augmentation equation is essential.

Checked the edge cases in the new statements: degree zero, zero rows, zero coefficient
maps, empty schemes and empty diagonals use the same Ext evaluation and cokernel
calculations. No injectivity of inverse-image terms is assumed. No unit statement or
realized step was bypassed; the unit record sk-prop-h2 has no realized entry for this
auxiliary node. LeanFinder and Loogle returned generic homology/sections tools but no
matching statement; LeanSearch returned Internal Server Error, which is recorded.

## New nodes

`lem-weil-pbc-ce-row-ordinary-naturality` isolates the Ext comparison square on two
nonnegative injective rows. Its source is Stacks Tags 06XR, 01F8 (equations 01F9 and
01FA), with the site pullback computation in 08J6. The comparison data is explicit.
Its node records the comparison-homotopy argument and evaluation at 1.

`lem-weil-pbc-ce-normalized-row-representatives` isolates normalized CE construction,
the signed first-page-to-row comparison, and the local equality in actual row homology.
Its source is Stacks Tags 015J, 015K and 012K; its proof records finite totals, unique
normalized successor comparisons and the diagonal-to-row calculation. It does not
assert the ordinary cohomology pullback formula. The two new nodes inherit the
parent's chapter, unit and blueprint ancestry, with real searches recorded.

Change record: `coord/changes/EtaleCENormalizedRepresentativeCohomology-imports.md`.


## Second reading by M4

1. Compared every delivered module with the repository. The original theorem's full
   signature is byte-for-byte identical, as is its existing docstring. Its only source
   changes are the replacement proof, two local elaboration/linter options, and imports.
   The two other modules are new. The existing node differs only in proof, proof_deps
   and proof_origin. The public import pruning has its change record. No target,
   existing definition, hypothesis or conclusion was changed. Verdict: pass.

2. Compiled all three delivered modules in import order through lcompile.py, with no
   errors or warnings. Read the complete calc: he factors both first-page comparisons,
   hrow substitutes the cohomology map, hc supplies the row representative equality,
   and associativity gives the original result. The original module has no sorry;
   the new modules have exactly the two named theorems listed above. No prohibited
   declaration, sorry in a definition or arbitrary witness construction occurs.
   A scratch axiom file prints each of the three definitions and three theorems:
   ceRowOrdinaryIso, ceRowSectionsMap and cePresentationRow use only propext,
   Classical.choice and Quot.sound; the three theorems additionally use sorryAx,
   as expected for this decomposition. Verdict: pass as a decomposition, not a
   completed axiom-free proof of the item.

3. Read the two new statements, their docstrings and nodes against Stacks
   [015J](https://stacks.math.columbia.edu/tag/015J),
   [015K](https://stacks.math.columbia.edu/tag/015K),
   [012K](https://stacks.math.columbia.edu/tag/012K),
   [0130](https://stacks.math.columbia.edu/tag/0130),
   [06XR](https://stacks.math.columbia.edu/tag/06XR),
   [01F8](https://stacks.math.columbia.edu/tag/01F8) and
   [08J6](https://stacks.math.columbia.edu/tag/08J6). The single-row square assumes
   precisely the augmentation compatibility needed for its Ext calculation; the
   inverse-image row need not be injective. The CE statement replaces ordinary
   cohomology pullback by the actual row-homology map, and fixes its comparison
   with firstPageIso explicitly. These are distinct parts of the argument, not
   renamed copies of the original conclusion. Checked p=0 (incoming boundaries
   zero, sign +1), negative q (integer sign still a unit), zero coefficient maps
   (both class maps zero), zero rows, empty schemes and empty diagonals.
   Independent LeanFinder queries about resolution-independent Ext/sections and
   associated-graded row cocycles, a Loogle homotopy query, and grep for extension
   homology/derived comparison naturality found component tools, not either complete
   statement. Read ExtPullbackResolutionSections, ExtPullbackHomComplex,
   EtaleSheafHExtDerivedComparison, ExtRightDerivedCocycleComparison and
   SecondFiltrationRowCycleComparison. The existing chosen-resolution pullback
   formula and same-site comparison tools do not directly close the arbitrary-row,
   arbitrary-coefficient square. Neither remaining hole has a short direct proof
   from those interfaces. Verdict: true, needed lower statements; two holes remain.

4. Checked the imports against every signature and explicit definition body.
   EtaleCETotalSections supplies the CE total types; normalized homology supplies
   the public successor predicate; the new row module is proof-only in the item.
   The explicit row comparison needs extension homology and the Ext/sections
   construction in its exposed definition. The new CE statement publicly needs
   the row definitions. Read the sole direct importer, which independently exports
   EtaleCEStationaryPageNaturality, and compiled its unchanged source against the
   delivery overlay. The No longer needed section now explicitly accounts for
   every old proof dependency. Read sk-prop-h2.json: its realized statement and
   sole realized step are empty, and this auxiliary change does not alter either
   the unit record or its Kummer argument. Verdict: route retained and pruning
   correctly scoped to this module, with no claim of global unreachability.

5. Matched each Lean theorem with its node. The parent proof's two dependencies
   are exactly the two lemmas used by the calc. The new node proof_deps equal the
   union of their proof-step uses, and their chapter, unit, ancestry, sources,
   creation records and Lean records are present. All definitions are concrete:
   extension/map isomorphisms and Ext evaluation, the sections unit followed by
   phi, and the actual CE row with its supplied augmentation and resolution proofs.
   Verdict: pass. Repaired the new Lean statement fields to contain the actual
   multiline signatures verbatim, and added the independent search results.

Second reading changed documentation and metadata only: added the missing module
blueprint labels, made explicit that ordinaryComparison composes isoRightDerivedObj
with ceRowOrdinaryIso (their domains differ), expanded dependency-pruning accounting,
and recorded verbatim new signatures and fresh searches. The existing theorem,
new theorem signatures, proof terms and definitions are unchanged. One original hole
is closed and two lower holes are added: net minus one, explicitly a decomposition.
