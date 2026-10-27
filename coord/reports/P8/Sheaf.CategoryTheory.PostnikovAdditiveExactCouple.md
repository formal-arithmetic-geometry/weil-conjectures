## What changed

The item now assembles the normalized canonical Postnikov couple, its additive iterated
page functors, a spectral-sequence realization, stabilized entries, a natural half-plane
abutment, and a proved transport argument. Its statement is unchanged.

The ten witness definitions moved verbatim into
`Sheaf.CategoryTheory.PostnikovAdditiveExactCoupleData`, publicly reexported by the item.
This breaks the dependency cycle between witness interfaces and their construction lemmas.
Their signatures, visibility, bodies and docstrings are byte-identical; a direct text
comparison verifies this. There are zero current Lean importers of the item; DAG parents
remain attached and still need the original theorem. No source-library file changed.
The change record is `coord/changes/postnikov-additive-witness-data.md`.

The canonical couple uses Mathlib's canonical truncation triangle and its three homological
exactness positions. Homology full faithfulness on single-degree objects constructs the
normalized natural layer isomorphism. The single-functor shift comparisons give the initial
page comparison. The generic additive iteration proves identities, composition and addition
by cancelling the image inclusions, kernel inclusions and homology projections. The
Postnikov page construction supplies the three initial naturality squares, including the
boundary shift. The transport proof explicitly converts the PBC filtration interface to
the standard decreasing-filtration interface, retaining the same steps, and uses image
isomorphisms and cokernel functoriality. Stable entries use the actual cokernel of
stationary boundary inclusions into stationary cycles. The late-page projection
characterizes its isomorphism; cancellation gives naturality, functor laws and addition.
Stationarity makes the cycle lift epic, proving compatibility with the next-page
homology projection.

The import-ordered compile of all nine packet modules passes, including the final
assembly theorem. Two redundant tactics reported by that check were removed. The
packet contains exactly two occurrences of `sorry`, both the public theorems listed
below. All Lean lines are at most 100 characters and all node JSON parses. The first delivery
preflight caught two `lean.statement` records that included context or structure fields;
those records now contain exactly the declaration signatures. Nothing was pushed by
that failed check.

## Proved and sorry left

The original hole `DerivedCategory.exists_postnikov_additive_exact_couple` is replaced by
an explicit assembly proof. This is a decomposition, not a sorry-free proof of the full
original theorem: one upper hole is closed and two strictly separate lower holes remain.

New theorem proofs supplied in this packet:

- `DerivedCategory.exists_postnikov_canonical_exact_couple`
  (`lem-per-postnikov-canonical-exact-couple`).
- `CategoryTheory.BigradedExactCouple.exists_additive_page_data`
  (`lem-sp-additive-exact-couple-pages`).
- `DerivedCategory.exists_postnikov_page_data`
  (`lem-per-postnikov-page-functoriality`).
- `DerivedCategory.postnikov_abutment_transport`
  (`lem-per-postnikov-abutment-transport`).
- `DerivedCategory.exists_postnikov_stable_data`
  (`lem-per-postnikov-stable-pages`).

The two remaining public theorem holes, each in its own module with its own complete
proof in words and DAG node, are:

- `DerivedCategory.exists_postnikov_spectral_data`
  (`lem-per-postnikov-spectral-sequence`): realization as a Mathlib spectral sequence.
- `DerivedCategory.exists_postnikov_abutment_data`
  (`lem-per-postnikov-natural-abutment`): natural half-plane filtration and infinity data.

Neither repeats the original existence statement: each assumes the already constructed
initial couple and additive pages, and constructs one independent further object.
Zero new holes occur inside definitions or private declarations. No axioms are added.
Before any dependency pruning is accounted for, this decomposition has one hole closed
and two holes added, a net change of minus one; landing is not claimed as net proof progress.
Small-case checks for the new statements: the zero functor and zero object give zero
couples and all zero pages; a single-degree object gives the expected shifted initial
page. Empty half-plane subcategories cause no choices of objects. The stable-entry
construction requires only stationary finite subobjects, not arbitrary intersections.
Translations rho of either sign change total degrees but preserve all structure degrees.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.CategoryTheory.TruncationTriangle`: the normalized truncation layer is constructed
  directly from Mathlib's canonical successive-truncation triangle and homology full
  faithfulness. The dependency `lem-weil-pbc-truncation-triangle` is not used by this route.
- `Sheaf.CategoryTheory.ExactCoupleMorphism`: the declared theorem is currently commented
  out in the adopted module. The natural-abutment argument instead uses the actual
  derived-couple functoriality and the normalized diagonal-colimit universal property.
  This item's dependency on `lem-sp-couple-morphism` is removed; its source module is
  not withdrawn, and other consumers may still need it. The obsolete top-level
  `tool_uses` approvals for this node and the truncation-triangle node are removed.
- `WeilConjectures.CategoryTheory.DerivedCoupleExact`: the direct import is redundant.
  The canonical derived-couple definitions and their proved exactness remain used through
  the exact-couple interface; this is not a claim that exact-couple iteration is pruned.

No module is withdrawn. The unit statement and all realized unit steps are preserved.
The witness-data module preserves the original public imports needed by its statements;
construction imports are private proof imports.

## Where the brief, the DAG or earlier work was wrong

The planned dependency `Sheaf.CategoryTheory.ExactCoupleMorphism.coupleMorphism` has no
active Lean declaration: its whole theorem is inside a comment marking an upstream-sync
repair. Its proof plan remains useful mathematically, but cannot be applied as a Lean
lemma. The actual proved `derivedCoupleFunctoriality` supplies page and limiting-cycle
maps, while naturality of the abutment and filtration still needs the separately stated
argument. Also, convergence and transport use two distinct decreasing-filtration
interfaces; the transport construction now explicitly preserves their common step data.

The launcher paused and resumed this session to shorten the compile queue. Interrupted
compiles were checked before retrying; failed missing-sibling-olean checks were repaired
by compiling the prerequisite data module as part of the import-ordered set. No delivery
had started before this resume. The current resumed attempt is
`Sheaf.CategoryTheory.PostnikovAdditiveExactCouple.1792773514` (session
`01a1692b-861a-7e12-8065-fee8a142ece6`); its reference start is 16:38 UTC,
whereas the unchanged claim began at 09:09 UTC and recorded searches began at 10:15 UTC.
This records the reset; no budget metadata was modified.

## New nodes

`def-per-postnikov-additive-witness-data` owns the unchanged relocated witness interfaces.

`lem-per-postnikov-canonical-exact-couple` records normalized initial couple construction.

`lem-sp-additive-exact-couple-pages` records the generic mono/epi cancellation induction.

`lem-per-postnikov-page-functoriality` records its canonical Postnikov application.

`lem-per-postnikov-abutment-transport` records filtration and quotient transport.

`lem-per-postnikov-stable-pages` proves additive stationary-entry quotients and their
canonical late-page comparisons.

`lem-per-postnikov-spectral-sequence` retains realization by Mathlib spectral sequences
with the prescribed differential and homology transition.

`lem-per-postnikov-natural-abutment` retains the natural half-plane filtration and
infinity comparison. These last two nodes are named theorem holes. All new nodes use
the existing Postnikov witness interfaces and preserve the unit route. Search covered
the adopted library, Mathlib, and the imported blueprint (no matching blueprint node for
additive exact couples). The change record is
`coord/changes/postnikov-additive-witness-data.md`.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
