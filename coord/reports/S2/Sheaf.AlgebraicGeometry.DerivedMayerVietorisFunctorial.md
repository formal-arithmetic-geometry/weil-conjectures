## What changed

Reduced `AlgebraicGeometry.schemeDerived_mayerVietoris_directImage` to two independent
comparison obligations. The item now constructs the open and middle isomorphisms and
assembles the triangle isomorphism with `Triangle.isoMk`; its naturality, distinguishedness,
image distinguishedness, quasi-coherence and component formulas are proved in Lean.
The existing naturality proof is factored through the proved private `canonicalMV_spec`,
which verifies the exact explicitly constructed data used by both clauses.

Added `DerivedMayerVietorisCanonicalData`, with real constructions of the fixed resolution,
adjunctions, transported boundary, triangle, normalized composition and sectionwise
restriction comparisons, and biproduct comparison. Added proof-only imports of
`DerivedMayerVietorisDirectImageSquares` and `DerivedMayerVietorisDirectImageBoundary`.
The data module is public because the corrected comparison formulas in the signature use it.
No other existing module is changed, and no target declaration changes.

The compile-time repair makes the canonical resolution use a named construction with proved
K-injectivity and injective-term instances
and supplies universe parameters explicitly when calling `canonicalMV_spec`. A proved
private `transport_boundary_square` handles the transport algebra without expanding the
scheme functors during rewrite matching. The reducible `schemeMVModuleAbelian` alias reuses the existing Mathlib abelian structure;
the data module and item prefer it locally, avoiding generic sheafification searches.
The retained signature diagnostic measured a reduction from 24 seconds to 3 seconds.
In this repair, the canonical-data module compiled in 32–33 seconds, and the completed
main proof passed a source check in 46 seconds; the full artifact compile then passed in 55 seconds (the data module took 19 seconds
and the two frontier modules about 3 seconds each).
The canonical data retain their exported definition transparency. The main module marks
the comparison constructions irreducible locally, explicitly unfolds the middle comparison
only for its projection calculation, and binds the square conjunction before its projections;
this avoids expanding the constructed comparisons during pattern elaboration. Both
frontier modules use the same local abelian-instance alias as the data and main modules.
The named `schemeMVDirectImageTriangulated` alias reuses the proved right-derived-functor
instance. `schemeMVImageTriangle` names the actual mapped triangle with its shift
commutation elaborated once, and `schemeMVImageTriangle_distinguished` proves its standard
triangulated-functor property. These avoid rebuilding the same structures at every repeated
image-triangle occurrence; they add no holes and are definitionally the original image.
`schemeMVDerivedRestriction` abbreviates the original exact derived restriction functor
with its exactness witnesses elaborated once. The direct-image clause uses this
definitionally equal abbreviation; the existing naturality signature is unchanged.

The held intermediate statement's comparison formulas were corrected: selecting an arbitrary
isomorphism from `Nonempty` loses the source's canonical normalization. Composition now uses
the witness constrained by the existing right-derived unit equation. Open restriction uses
the explicit derivation of the sectionwise identity from the existing dependency's proof.
The hypotheses, objects and triangle-component requirements are unchanged. This correction
is recorded in `coord/changes/DerivedMayerVietorisCanonicalComparisons.md` and the parent node.

## Proved and sorry left

Original hole: `AlgebraicGeometry.schemeDerived_mayerVietoris_directImage`
(node `lem-pc-derived-mayer-vietoris-functorial`). Its body now has no `sorry`, but its
comparison normalization was corrected as described above; this is a decomposition of the
corrected statement, not a proof of the old arbitrary-choice statement or a net hole reduction.
`AlgebraicGeometry.schemeDerived_mayerVietoris_naturality` was already proved and remains proved
with its signature text unchanged. The new resolution-property instances and both abstract
identity-square helpers are proved without holes. The private `canonicalMV_spec` is fully proved.

Two holes added, each in its own module, each strictly a part of the argument:

- `AlgebraicGeometry.schemeMV_directImage_squares`
  (`lem-pc-derived-mayer-vietoris-direct-image-squares`): only the first and second squares;
  no boundaries, naturality, distinguishedness, quasi-coherence or triangle isomorphism.
- `AlgebraicGeometry.schemeMV_directImage_boundary`
  (`lem-pc-derived-mayer-vietoris-direct-image-boundary`): only the boundary square for
  the constructed families; no other squares, naturality, distinguishedness, quasi-coherence
  or triangle isomorphism.

No `sorry` remains in the item's module. No data definition has a hole. The only data chosen
from an existence theorem is the composition witness whose determining right-derived unit
equation is part of that theorem. All boundaries and restriction comparisons are constructed.

## No longer needed

Removed the unused public imports `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`
and `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`. Their wrapper declarations
`derivedDirectImageComposition` (`lem-pc-derived-direct-image-composition`) and
`schemeDerivedDirectImage_openRestriction` (`lem-pc-restrict-derived-direct-image-open`)
are no longer used by this proof. The normalized ringed-space composition theorem and the
explicit derived sectionwise restriction construction replace them. The corresponding proof
edges are removed from the delivered nodes. This does not claim either wrapper globally
unreachable: other modules can still import them independently.

The other removed direct proof edges are `lem-sc-derived-k-injective-restrict-open`,
`lem-pc-derived-functor-termwise-split-ses-triangle`, and
`lem-weil-pbc-right-adjoint-preserves-kinjective`. They are used by the canonical-data
construction or the new boundary obligation rather than directly by the parent proof;
their modules remain needed in this delivery's dependency closure. No globally unreachable
module is claimed pruned.

The sole downstream Lean caller of either wrapper is `CartesianTensorDataComparison`,
which already imports `DerivedDirectImageCompositionUnbounded` directly. Other downstream
mentions are comments. Existing public imports needed for the remaining interface stay;
all remaining proof imports are used in the representative-level argument.

## Where the brief, the DAG or earlier work was wrong

The retained attempt timed out at conjunction pattern elaboration. A named conjunction
and its projections compile without expanding the comparison constructions there.
The boundary-square simplification selected the core type-functor lemma when given
unqualified `Functor.map_id`. The proved private `boundary_square_identity` now performs
this categorical identity calculation before specializing to schemes, avoiding tactic
matching through the constructed triangle component types. The first-square identity is likewise handled by the proved private
`first_square_identity`. The middle component formulas are closed by the explicit biproduct projection
lemmas. These repairs add no holes and change no mathematical data.

The earlier interface described `Classical.choice` of a bare `Nonempty (F ≅ G)` as canonical.
It is not determined by that proposition: a proof returning a constructed isomorphism has
its witness erased by proof irrelevance. For example, both an isomorphism and its negative
inhabit the same `Nonempty` proposition, whereas a unit compatibility equation distinguishes
them. New fixed-adjunction square claims using those arbitrary choices would therefore be
unjustified. The normalized composition theorem already states the needed determining
unit equation, and the existing open-restriction proof supplies an explicit construction;
this delivery retains that data rather than inventing a new normalization axiom.

There are no actual Lean calls to the corrected directImage clause elsewhere in the sources:
three modules mention it only in docstrings. The change record lists every downstream importer
and its holder. No adaptation is necessary. All target signatures and their mathematical
meaning are preserved. The unit's route is unchanged; this item does not realize a unit-level
step in `dag/units/sk-thm-picard-semicon.json`.

The first dry run compiled the modules and ran the axiom probes, but preflight found
stale citer metadata from the retained attempt after fetching the current base. The
first worker's statement-change record then named the two citers:
`lem-pc-perfect-hom-mayer-vietoris-triangle-cocone` and
`lem-pc-rf-mv-base-change-connecting-square`. Both explicitly require pinned canonical
comparison maps, so their statements remain valid. The metadata field `by` uses the
checker-required `S2 stage 2` spelling even for this stage-3 correction.

The source files themselves are not present in this checkout. The official Stacks pages for
Tags 08BV, 08FE, 0D5T and 0DJ9 were read online. Mathlib search ran through the required wrapper:
LeanSearch was unavailable (HTTP internal server error), LeanFinder returned generic
short-exact-sequence and Mayer--Vietoris primitives, Loogle found `Triangle.isoMk`, and the
recorded grep queries found no specialized direct-image compatibility theorem.

Small cases checked for the new statements: zero objects make all three squares zero;
an empty member of the cover removes the corresponding summand and intersection; the cover
with both opens equal to the whole scheme yields the diagonal/difference split sequence.
The normalized comparisons are sectionwise identities in these cases. Non-quasi-coherent
objects are allowed by the intermediate statements because the representative construction
and split-sequence comparison use all module complexes, independently of quasi-coherence.

## New nodes

`def-pc-derived-mayer-vietoris-canonical-data` records the real constructions in
`lean/Sheaf/AlgebraicGeometry/DerivedMayerVietorisCanonicalData.lean`; it adds no hole.

`lem-pc-derived-mayer-vietoris-direct-image-squares` records the first two arrow squares
in `lean/Sheaf/AlgebraicGeometry/DerivedMayerVietorisDirectImageSquares.lean`.

`lem-pc-derived-mayer-vietoris-direct-image-boundary` records the third arrow square
in `lean/Sheaf/AlgebraicGeometry/DerivedMayerVietorisDirectImageBoundary.lean`.

Change record: `coord/changes/DerivedMayerVietorisCanonicalComparisons.md`.

## Second reading by S2

1. Compared all four delivered modules with the repository. Three are new. The existing
   `schemeDerived_mayerVietoris_naturality` signature is byte-for-byte unchanged. The only
   public statement correction is `schemeDerived_mayerVietoris_directImage`, explicitly
   recorded in `coord/changes/DerivedMayerVietorisCanonicalComparisons.md`: normalized
   comparisons replace bare `Nonempty` choices. Its hypotheses and triangle conclusions
   are preserved. The remaining abbreviation and explicit-order annotations are
   definitionally the original expressions. No target file or existing definition changes.
   Repository searches confirm that other modules mention the corrected clause only in
   docstrings; no downstream Lean call requires adaptation. Verdict: pass with the declared
   intermediate-statement correction, not a proof of the previous arbitrary-choice formula.
2. Compiled all four modules using `lcompile.py --all`: canonical data 18.2 seconds,
   boundary 2.9 seconds, squares 3.1 seconds, parent 53.4 seconds, no errors or warnings.
   Source audit finds exactly the two reported named theorem holes, no hollow definition,
   and no forbidden axiom, unsafe, opaque, extern or kernel-check bypass. The composition
   choice is constrained by `exists_derivedModuleDirectImageComposition`'s right-derived
   unit equation; the universal property determines it. Resolution preimages are the
   actual localization construction, and resolution and boundary data are explicit.
   The required delivery dry run checks all declarations' axioms. Verdict: source and
   compilation pass; closure remains conditional on the two holes and upstream holes.
3. Read both new statements, their complete docstring arguments, and their nodes against
   Stacks Tags 08BV, 08FE, 0D5T and 0DJ9. The squares obligation contains only the first
   two arrow identities; the boundary obligation contains only the third identity.
   Neither restates the full item. Zero objects, an empty cover member, and two copies
   of the whole space reduce respectively to zero maps or the split diagonal/difference
   sequence. The proof uses all module complexes, so removing quasi-coherence from these
   compatibility obligations is legitimate. Independent searches with `msearch.py`
   (LeanFinder: localization triangle under pushforward; Loogle: `Triangle.isoMk`;
   grep: mapped short-exact-sequence triangles) and `rg` found generic assembly primitives
   but no existing specialized compatibility theorem. These holes cannot be closed by a
   few-minute application of the search results. Verdict: true, strictly partial obligations.
4. Checked the construction from the parent downward: it proves naturality and
   distinguishedness, uses existing quasi-coherence and triangulatedness results, and
   assembles the triangle isomorphism using `Triangle.isoMk` and the three arrow identities.
   The two removed comparison wrappers are replaced by normalized constructions.
   Completed the report's list of all five removed old direct proof edges, distinguishing
   obligations moved below the parent from modules actually pruned. The unit record
   `sk-thm-picard-semicon.json` has empty realized slots; no realized unit step is bypassed.
   Tested making `KInjectiveRestrictOpen` and `RightDerivedFunctor.FullyFaithful` plain
   imports. Lean correctly refuses their use inside the exported comparison definition
   (`Unknown identifier kInjective_of_restrict_open`, imported privately, and the missing
   composite preservation instance). Restored both public imports: the definition's body
   needs them, even though their contributions are proof fields. The frontier modules
   remain plain imports in the parent, where they are used only in theorem proofs.
   Verdict: route retained; no global module pruning claimed.
5. Checked all four nodes: each `proof_deps` equals the union of its proof steps' `uses`;
   the parent records the actual assembly and corrected comparison normalization; new
   nodes have source, searches, creation, blueprint, chapter, unit and Lean records.
   The two holes match their named declarations and module paths. Verdict: pass.

Second reading changed only report completeness; the tested import change was reverted. This is a
one-upper-hole/two-lower-hole decomposition of the corrected intermediate statement,
not a net hole reduction or an unconditional new proof. The already proved naturality
clause stays proved.

Final second-reader dry run: `deliver3.py S2
Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial --no-push` printed OK at
`870f98527d`. All modules compiled and the all-declaration axiom probes passed with no
unexpected axioms; preflight passed with review class CODEX for the recorded statement
correction, new nodes and public data. The tested import demotion is not delivered.

The final push attempt fetched a newer base and preflight refused stale citer metadata:
K3 had replaced `lem-pc-rf-mv-base-change-connecting-square`'s direct dependency with
`lem-pc-rf-mv-base-change-connecting-square-data` and
`lem-pc-rf-mv-base-change-connecting-square-equation`. Read both new nodes and updated
the parent's `statement_change.citers`. The data node uses the unchanged existence and
distinguishedness conclusions. The equation node's use of naturality and pinned mates
is preserved by the normalization correction. Neither declaration names the replaced
choices, so neither needs adaptation. This checks preservation under our change, not
the separate truth of the equation node's arbitrary boundary/shift interface.
No Lean source changed in this metadata repair.
