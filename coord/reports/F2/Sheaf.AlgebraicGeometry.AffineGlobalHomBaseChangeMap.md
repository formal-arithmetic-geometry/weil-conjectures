## What changed

Returned-delivery identifier: `e086dc9a4be846f5`.
The incoming transport API and its comparison proof are retained in
`Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap`. Two proved helper modules
are retained: `Sheaf.CategoryTheory.DerivedCategory.AdjunctionNormalization` and
`Sheaf.AlgebraicGeometry.OriginalCounitAdjunctionTransport`. The generic helper
identifies normalized adjunctions by their representative Hom formula and the
right-derived universal property. The scheme helper proves equality of the
legacy adjunction with the original-counit adjunction transported along the
inverse universal-counit comparison. The item exposes unit, counit and both Hom
transport equations and uses the transported adjunction in its comparison proof.

All existing signatures, definitions, visibility and docstrings are unchanged.
`GlobalHomOriginalCounitNormalization` is a public import because the new public
signatures use it. `OriginalCounitAdjunctionTransport` and the generic uniqueness
helper are proof-only imports where their theorems are used.

The returned consumer, `ProperFlatImageGlobalHomBaseChangeIso`, is included as
an unchanged copy of the current baseline, as are `ExtensionKFlatQuasiIso` and
`AffineSectionsSquareComparisonCoherence`. The consumer already contains
`SheafOfModules.overFunctor.{u}`. The second reader compiled that exact baseline
against the delivery overlay successfully in 16.5 seconds. The incoming report's
reproduction removed this annotation; it did not establish that the current
baseline needed adaptation. Consequently the second reader removed the redundant
local restriction-functor edit and its change record.

Retained change record:
`coord/changes/affine-pullback-original-counit-transport.md`.
The shared original-counit definition REPAIR marker stays open; this transport
API does not claim to replace the legacy counit construction.

## Proved and sorry left

Initial item: 0 direct sorries. Holes closed: 0 (no declarations).
Holes added: 0 (no declarations). Sorry split-offs: 0. This is a returned-delivery
repair and proved transport API, not a reduction of the sorry ledger.
Every delivered Lean file has no local sorry.

The seven added public transport/uniqueness theorems are proved:

- `CategoryTheory.Adjunction.eq_of_normalization`
- `AlgebraicGeometry.schemeHomPullbackAdjunction_eq_original_transport`
- `AlgebraicGeometry.canonicalPullbackAdjunction_eq_original_transport`
- `AlgebraicGeometry.canonicalPullbackAdjunction_unit_original`
- `AlgebraicGeometry.canonicalPullbackAdjunction_counit_original`
- `AlgebraicGeometry.canonicalPullbackAdjunction_homEquiv_original`
- `AlgebraicGeometry.canonicalPullbackAdjunction_homEquiv_symm_original`

`AlgebraicGeometry.exists_globalHomPullbackComparison` remains proved with its
unchanged statement. The second reader's axiom probe covered every declaration
of the item, the two new public helper theorems and the three carried modules'
public theorems. All item declarations, both helpers, extension preservation and
sections coherence use only `propext`, `Classical.choice` and `Quot.sound`.
`AlgebraicGeometry.properFlatImage_globalHomBaseChange_isIso` additionally uses
`sorryAx` from existing imported obligations. No imported hole is claimed closed,
and no new unproved data choice is introduced.

All six modules compiled in dependency order through the supported lcompile.py,
with no errors or warnings and the default 60-second per-file limit:
ExtensionKFlatQuasiIso 2.0 s; ProperFlatImageGlobalHomBaseChangeIso 17.1 s;
AdjunctionNormalization 1.0 s; OriginalCounitAdjunctionTransport 18.4 s;
AffineGlobalHomBaseChangeMap 46.3 s; AffineSectionsSquareComparisonCoherence 38.0 s.
The exact baseline consumer separately compiled against this overlay in 16.5 s.
The axiom scratch module compiled in 1.7 s.

## No longer needed

No project import, dependency node or library module is pruned. All four old
item proof dependencies remain used. Both proved transport helpers are used.
The generic helper needs only the public Adjunction.Basic and RightDerived
imports; it does not need the broader derived-adjunction constructor API.
No experimental scratch composition statement is delivered.

## Where the brief, the DAG or earlier work was wrong

The generic brief assumes a sorry-containing item, but this returned item has no
direct sorry. The supported returned-delivery repair exception applies.

The incoming report incorrectly called the consumer edit a forced adaptation:
the exact current baseline compiles against the changed dependencies. Its
reported failure was obtained by removing the baseline's existing universe
annotation. The redundant edit and associated record have been withdrawn;
the consumer is included unchanged to validate the returned dependency set.

The original and composition-counit adjunctions require the proved transport;
proof irrelevance alone would not identify them. The definition-changing shared
original-counit repair remains open. No unit or chapter route or target statement
changes. The unit record's realized field currently has empty statement/step
lists; this delivery does not modify that pre-existing metadata gap or bypass
any recorded realization.

## New nodes

Two incoming proved nodes are retained, with no sorry:
`lem-pc-derived-adjunction-normalization-unique` records the triangle calculation
and right-derived extensionality;
`lem-pc-original-counit-adjunction-transport` records the legacy/original counit
transport. Both have sources, natural-language proofs, searches, creation and
blueprint records, matching Lean statements, and their own new modules.
The existing item's changed fields are only lean, proof, proof_deps and
proof_origin. Every proof_deps list equals the union of its proof steps' uses.

## Earlier second reading (a previous round; superseded)

1. Compared each of the six delivered modules with the read-only repository.
   Parsed declaration tables confirm byte-identical existing signatures and
   no changed definition bodies. The two helpers are new modules. The public
   transport equations and their required public import are declared in the
   retained change record. No target statement or definition changes. PASS.
2. Compiled all modules locally in dependency order; no errors or warnings.
   Scanned for sorry and forbidden declarations/attributes: none. Axiom probes
   confirm only the three permitted axioms, except the carried proper-flat
   consumer's existing imported sorryAx. No hollow definition or new arbitrary
   witness is introduced. PASS.
3. There are no sorry split-offs. Read both new proved helpers and tested their
   mathematical edge cases: the categorical proof needs no objects/nonemptiness
   assumptions and works for empty categories, zero and identity functors. The
   scheme proof is valid for identity maps and makes no claim that the counit
   comparison is identity. Independent msearch calls used grep, Loogle and
   LeanFinder with new wording; local rg covered Mathlib and both source roots.
   The related upstream derived_eq_ofNatIsoLeft compares particular Mathlib
   constructor adjunctions with stronger absolute-derived hypotheses, whereas
   this helper compares arbitrary normalized witnesses. No duplicate statement
   or shorter applicable theorem was found. PASS.
4. Read the item top down and both imported comparison constructions. The proof
   uses existing tensor-Hom, scalar-extension, evaluation-mate and sections
   normalization results; the new uniqueness argument directly uses Mathlib
   ext_counit and rightDerived_ext. Public imports supply signature/definition
   data; new proof-only imports are plain import. All four old proof_deps remain
   used, so No longer needed is complete. The unit record and blueprint route
   are unchanged, including the pre-existing empty realized field. PASS.
5. Read all three delivered node files against the Lean. Statements and Lean
   records match; proof steps describe the actual construction and transport;
   proof_deps equals the union of uses. Both new nodes contain the required
   source, proof, origin, searches, status, creation, blueprint, chapter, unit
   and Lean fields. Existing node changes stay within stage-3 fields. PASS.

Second-reading changes: removed the unnecessary consumer proof edit after
compiling the exact baseline against the overlay; withdrew its redundant change
record; corrected the retained change record and report. Retained the mathematically
correct transport proofs without rewriting them. Review scratch artifacts are
under scratchpad/current-second-reading and are not delivery files.

## Second reading by F2

1. PASS. Compared all six sandbox modules to the current read-only repository.
   Existing signatures and docstrings are byte-identical, and every existing
   definition body is unchanged. Only exists_globalHomPullbackComparison changes
   its proof body. The five added item equations and required public import are
   declared in the change record; the two proved helpers have their own modules.
   ExtensionKFlatQuasiIso, ProperFlatImageGlobalHomBaseChangeIso and
   AffineSectionsSquareComparisonCoherence are exact baseline copies. No target
   statement or definition changes.
2. PASS. Recompiled all six files through lcompile.py in dependency order: 1.8,
   16.4, 1.1, 16.5, 43.0 and 37.4 seconds respectively, with no errors or warnings.
   Scanned the delivered source: no local sorry or forbidden declaration or
   attribute. A fresh scratch axiom probe covers every public item declaration,
   both helpers and all carried public theorems. Only the permitted three axioms
   occur, except imported sorryAx in the unchanged proper-flat consumer. The
   helpers contain no witness choice; existing normalized choices and concrete
   scalar-extension constructions are retained. No new hollow definition.
3. PASS. There are no split-off holes. Read the triangle calculation: evaluating
   each representative equation at the underived counit gives equality after
   the specified right-derived unit; rightDerived_ext and ext_counit give actual
   equality of adjunctions. No inhabited-category assumption is hidden, so empty
   categories and identity or zero functors cause no exception. The scheme proof
   uses the inverse counit factorization with the correct orientation, including
   identity scheme maps, and never asserts the counit comparison is identity.
   Fresh Loogle, LeanFinder and grep queries use different wording; local rg and
   reading the Mathlib and upstream results found no duplicate or shorter
   applicable theorem. Upstream derived_eq_ofNatIsoLeft compares specific
   constructor adjunctions with additional derived-property assumptions.
4. PASS. Read the item from its comparison construction down to the imported
   evaluation-mate and sections normalization results. It retains all four old
   proof dependencies and adds the proved transport. The generic helper uses
   Mathlib directly. The new helpers are plain proof imports at their use sites;
   the new public import supplies types appearing in the exposed equations. No
   dependency is pruned. The unit and chapter route is unchanged; the unit's
   pre-existing empty realized lists are recorded, not replaced or bypassed.
5. PASS. Checked all three node files against the Lean declarations and proof
   bodies. proof_deps is exactly the union of step uses. The existing node changes
   only lean, proof, proof_deps and proof_origin. Both new nodes have the required
   sources, complete proofs, search verdicts, creation, blueprint, chapter, unit
   and verbatim normalized Lean statement records. The current F2 return's B7/G1
   request is satisfied: both failed LeanSearch entries contain an explicit
   unavailable verdict and valid JSON.

Changes in this reading: made the retained change record's Old definition block
verbatim from the current repository; appended the independently executed search
results to both new nodes and this review to the report. No Lean proof repair was
needed. Holes closed: 0; holes added: 0; split off: 0; pruned: none. Scratch axiom
checks are under scratchpad/final-second-reading and are not delivery files.
