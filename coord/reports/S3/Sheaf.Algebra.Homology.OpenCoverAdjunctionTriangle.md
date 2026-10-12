## What changed

Reduced `SheafOfModules.open_cover_adjunction_triangle` without changing its statement or
`openRestrictionComparison`. Its complete Lean proof now constructs the exact extension
functors from the existing localized-site adjunction theorem, chooses a representative complex,
uses the termwise short exact sequence, and transports its distinguished triangle to the chosen
left adjoints. Both arrow equations and the shifted boundary equation are proved.

Added `OpenCoverMateComplexShortExact` for the geometric sequence before localization, and
`OpenDerivedMatePresentation` for compatibility of a single nested mate with localization.
The latter also contains actual constructions `Adjunction.onDerivedCategory` and
`Adjunction.derivedPresentation` and the proved `Adjunction.derivedPresentation_counit`.
There are no postponed data constructions: the extension functors and the localized adjunctions
are concrete; existential adjunctions and the representative complex are used locally in a
proposition proof.

All additional imports in the original module are proof imports. Updated its DAG proof to match
this reduction, with two new nodes. The existing signature and visibility remain unchanged.

## Proved and sorry left

Closed the original hole in `SheafOfModules.open_cover_adjunction_triangle`
(`lem-sc-open-cover-adjunction-triangle`). No sorry remains in the item's module.

Added exactly two holes, one per new module:

- `SheafOfModules.open_cover_mate_complex_shortExact`
  (`lem-sc-open-cover-mate-complex-short-exact`): the geometric short exact sequence of
  complexes, with the degreewise mate formulas. This concerns sheaves and complexes only;
  it has no derived object, localization, or distinguished-triangle conclusion.
- `CategoryTheory.Adjunction.derivedPresentation_mate`
  (`lem-sc-localization-nested-adjunction-mate`): a generic equality comparing one nested
  mate before and after exact localization. It has no open cover, short exact sequence,
  or distinguished-triangle conclusion.

This is a decomposition: one original hole closed and two strictly lower holes added, not
an unconditional proof or a positive net reduction in holes. The counit compatibility and
all triangle assembly are fully proved. The original module compiled without warnings against
both new modules through the launcher compiler. Empty opens, equal opens, and the empty space
are covered by the same stalk description in the new geometric theorem; the generic lemma
uses no geometric nonemptiness assumption.

## No longer needed

No original imports were removed and no globally unreachable module is claimed. Pruned: none.

The original node no longer uses `lem-sc-module-extension-by-zero-stalk-maps` and
`lem-weil-pbc-module-stalk-exact` directly: their geometric work belongs below the new
complex-sequence node, which still needs them. They are therefore not claimed as pruned.
`DerivedMayerVietorisTriangle`, `DerivedOpenShriekAdjunction`,
`OpenExtensionMayerVietorisShortExact`, and `OpenExtensionRestrictionIso` are not imported
by this proof. They were considered as possible shorter routes, rather than removed imports.
The unit's `realized` fields contain no statement or step bound to this node; its route is kept.

## Where the brief, the DAG or earlier work was wrong

The planned existing geometric declarations cannot be imported here: the import-direction
checker rejects `DerivedMayerVietorisTriangle`, `OpenRestrictionAdjunctionExact`,
`ModuleExtensionByZeroStalkMaps`, `ModuleStalkExact`, and `OpenExtensionRestrictionIso`.
They reach this item through `Sheaf.Paper.DerivedHomMayerVietoris`, whose proof imports
`OpenHomTriangleRealization`, which already imports this item. Thus directly implementing
the original list of imports would close an import cycle. No other module was adapted.
The proof instead uses the lower-level `LocalizedModuleAdjunctionExact`, which passes the
import-direction check, and states the remaining geometric and localization steps separately.
Future work on the geometric node will need to address this shared-interface import issue
before using those existing stalk declarations; their mathematical content was not discarded.

The local `literature/stacks-project/cohomology.tex` archive is absent. The source arguments
were read at https://stacks.math.columbia.edu/tag/08BU,
https://stacks.math.columbia.edu/tag/08BT, and
https://stacks.math.columbia.edu/tag/08BW, together with the pinned Mathlib localization,
short-exact-triangle and adjunction-uniqueness files. LeanSearch returned Internal Server Error
for both new queries; this is recorded as unavailable. LeanFinder, Loogle and source searches
ran successfully and did not supply the missing full statements.

## New nodes

`lem-sc-open-cover-mate-complex-short-exact` records the short exact complex sequence and
its canonical degreewise maps, sourced from the proof of Tag 08BU and the nested restrictions
of Tag 08BW. Its module has one public postponed theorem with a complete proof in words.

`lem-sc-localization-nested-adjunction-mate` records the generic exact-localization mate
identity. The same module constructs the localized adjunction and comparison isomorphism
and proves counit compatibility using Mathlib's localization formula and `leftAdjointUniq`.
Its only postponed theorem is the single nested mate identity. No change record is needed:
no existing statement, definition, signature or visibility was changed.

## Second reading by S3

Independent second reader, 2026-10-13; did not write these proofs.

1. **Unchanged interface: PASS.** Read the complete diff against the repository module.
   Both existing declarations, `SheafOfModules.openRestrictionComparison` and
   `SheafOfModules.open_cover_adjunction_triangle`, retain byte-identical statements and
   visibility. The comparison definition itself is unchanged. The only original-module
   additions are proof imports, a private proved exactness helper, the heartbeat option,
   and the triangle proof. No existing definition or statement was altered; no change
   record or forced adaptation is required. The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`.
2. **Kernel proof and constructions: PASS, conditional on the listed holes.** Compiled all
   three delivered modules in import order through `lcompile.py`: 5.0, 2.8, and 25.3 seconds,
   without warnings or errors. Read every declaration and scanned for forbidden constructs.
   Exactly the two reported public named theorems contain `sorry`; neither definition does.
   Scratch-copy `#print axioms` checks show only `propext`, `Classical.choice`, and
   `Quot.sound` for the comparison, `onDerivedCategory`, `derivedPresentation`, and
   `derivedPresentation_counit`. The main triangle theorem and the two postponed theorems
   additionally use `sorryAx`, as expected. The exact extension functor is explicitly
   constructed; adjunction choices and the representative complex are local to a
   proposition proof. The public constructions use localization and unique compatible
   adjunction comparisons, not arbitrary witnesses from an unproved existence theorem.
3. **Split statements and searches: PASS.** The geometric lemma asserts short exactness
   before localization, with exactly the mate components consumed by the main proof.
   The generic lemma asserts one arrow equality, with no cover, exact sequence, or triangle.
   Neither restates the original theorem. Read their full source/proof docstrings and their
   nodes, and checked the arguments against Stacks Tags 08BU, 08BT, and 08BW and the pinned
   localization formulas. In the geometric statement, the zero complex gives the zero
   sequence; U empty forces V total and gives the identity on the V summand; U=V forces
   both total and gives diagonal difference followed by addition; an empty space gives
   zero stalks throughout. All calculations work in characteristic two. Changing the
   chosen adjunctions conjugates the component maps and does not alter exactness. In the
   generic statement, identity functors/adjunctions and e=id give f=id and the identity
   equality; even an arbitrary natural comparison c cancels with its inverse in this
   case. Arbitrary e and adjunction choices are accounted for by naturality and the
   left-adjoint-uniqueness unit/counit laws.
   Repeated searches with different wording through msearch LeanFinder, Loogle, and grep,
   plus rg on both library roots and the upstream source, found the generic localization
   and adjunction-uniqueness formulas and degreewise short-exactness, but no theorem
   supplying either full missing statement. The existing geometric short exact theorem
   is degreewise, uses specific chosen adjunctions, and does not give the prescribed
   component formulas or complex map. Its import, like the stalk-map and existing derived
   triangle imports, also closes a cycle through this item. Thus neither hole has an
   immediate existing-lemma closure; the localization equality still requires the
   factorization/naturality calculation described in its docstring.
4. **Top-down route, imports, and pruning: PASS.** Followed the proof from the target to
   its two lower steps. It uses the existing localized-site exact adjunction, Mathlib's
   short-exact distinguished triangle, and unique adjoint comparison, and explicitly
   verifies both arrow squares, the V sign, and the shifted boundary square. Confirmed
   the claimed import-cycle obstruction using import_direction.py for the existing
   derived triangle, stalk maps, and geometric short exact sequence. All newly added
   imports in the original module are plain proof imports. The new modules' public
   imports support their statements or concrete public definitions, including the
   filtered-colimit instance needed for small sheaf categories to be abelian. The two
   old dependencies no longer used directly are exactly the two listed under No longer
   needed; both remain prerequisites of the geometric split. No pruning is claimed.
   The unit sk-thm-picard-duality has empty realized statement and step lists; this
   reduction changes neither its route nor its realization records.
5. **DAG agreement: PASS.** Checked every delivered node against its Lean file: each
   lean.statement occurs verbatim, and proof_deps is exactly the union of proof-step uses.
   The main node records the concrete exactness specialization, complex sequence,
   localized presentations/mates, and triangle transport actually used. Both new nodes
   have source, complete proof steps, search records, status, creation, blueprint,
   chapter/unit, and Lean records required by the stage-3 brief.

**Changes made by the second reader:** added this independent review and recorded the
additional real searches in searches.jsonl. No mathematical or Lean repair was needed;
no declarations, imports, or node fields were changed. Removed the temporary axiom probes.
The delivery remains a decomposition: one original hole closed, two lower holes added,
net minus one hole closed; it is not an unconditional proof of the target.
