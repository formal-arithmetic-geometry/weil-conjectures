## What changed

Replaced the sorry in `AlgebraicGeometry.exists_supported_detector_open_lift_core`
with the finite-cover induction and shifted-retract argument. Its signature,
universes, visibility, and original docstring are unchanged. The proof constructs
all data explicitly: the erased-cover union, the smaller affine cover, the pulled-back
support, and the zero quasi-coherent object. It applies the given induction hypothesis
and the existing supported perfect map lift, proves quasi-coherence of the lifted
perfect object, and transfers orthogonality through its retract.

Added two proved statement modules:
`Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction` supplies fixed-universe
localizations on the open scheme and its opens and the derived restriction adjunction;
`Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison` supplies quasi-coherent
cohomology, support, shifted Hom, and zero-object comparisons. The second reader closed
the first worker's proposed localization/adjunction hole using existing library APIs.

All new proof imports are plain `import`. The item's public imports are unchanged.
Proof elaboration uses local additive/composition instances and ZeroObject notation.
A declaration-scoped unused-variable linter option preserves the original unused
existential binder `adj` without a warning. The scanner's conservative command-change
record is `coord/changes/supported-detector-open-lift-core-proof-context.md`.
No existing statement, definition, or downstream module is changed.

## Proved and sorry left

Closed the original item's one hole:
`AlgebraicGeometry.exists_supported_detector_open_lift_core`
(node `lem-pc-supported-detector-open-lift-core`).

Added and proved:
`AlgebraicGeometry.open_derived_localization_adjunction`
(node `lem-pc-open-derived-localization-adjunction`), and
`AlgebraicGeometry.open_derived_restriction_comparison`
(node `lem-pc-open-derived-restriction-comparison`).

No sorry remains in any delivered module; no holes are added. The proposed hole
`AlgebraicGeometry.open_derived_localization_adjunction` was closed during second
reading before delivery. This is one original hole closed, zero added, not a
net-zero decomposition. Existing dependency holes are not claimed closed, and
whole-library/target-closure progress remains the pinned ledger's measurement.
All three modules compile in import order without errors or warnings. Axiom prints
for each delivered theorem use only `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx` inherited from still-open dependencies.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral` and its sole removed
old DAG proof dependency `lem-pc-ringed-spaces-derived-adjoint-general`.
The open adjunction now uses the proved upstream unbounded exact-left-adjoint API,
not general derived tensor pullback. No claim of removing this module from other
targets or transitive imports is made.

Retained `PerfectSupportedMapLift`, which is actually applied, and added the
comparison, perfect-to-pseudo-coherent, pseudo-coherent-to-QCoh and quasi-coherent
restriction proof imports actually used. The new localization proof uses the
proved `DerivedOpenLocalization` theorem and upstream right-derived adjunction
and K-injective APIs. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan did not isolate the comparisons between localized module sites
and open subschemes. The first worker implemented the cover, support and retract
argument but missed the proved upstream
`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction` and the proved
`AlgebraicGeometry.nonempty_derivedOpenLocalization`. The second reader found these
through alternative searches and closed the proposed remaining hole. Transport of
localization along the exact module equivalence uses its derived equivalence and
`MorphismProperty.hasLocalizationOfLocallySmall`.

The perfect-to-QCoh argument must confine its family of open-scheme localization
instances to that subproof, preserving the induction detector's already installed
localization on U. The delivered proof does so. There are no new definitions and
no arbitrary witness from a mere existence theorem used as definition data.

Empty and full opens, empty and total support, repeated restricted charts, zero
complexes, and every integer shift were checked. Image cardinality only decreases,
compactness of the pulled-back complement uses quasi-separatedness, and support
comparison works even for a nonclosed subset. The adjunction is for all module
objects, so no unsupported quasi-coherence of direct image is assumed.

The unit `sk-thm-picard-duality` has empty realized statement/step lists; no recorded
realizer is removed. The K-injective resolution statement from the smooth-purity
chapter is used solely as a generic tool. Stacks Tags 079W and 0A9A were checked
against their online statements and proofs. Second-reader searches used LeanFinder
on exact derived adjunctions, Loogle on localization smallness, and alternative
`rg` queries on both Lean roots. The new statements have no exact existing public
match, though the found ingredients prove both.

## New nodes

`lem-pc-open-derived-localization-adjunction`:
`lean/Sheaf/AlgebraicGeometry/OpenDerivedLocalizationAdjunction.lean`.
Its theorem is proved by exact-equivalence transport, the existing localization-on-opens
theorem, and the proved unbounded derived-adjunction API. Its proof dependency list
records these ingredients and the generic K-injective theorem.

`lem-pc-open-derived-restriction-comparison`:
`lean/Sheaf/AlgebraicGeometry/OpenDerivedRestrictionComparison.lean`.
Its theorem is proved using the localization/adjunction theorem, the existing QCoh
restriction criterion, homology and stalk isomorphisms, shifts, and full faithfulness.
Both nodes inherit the item's chapter/unit and blueprint ancestor. Both have source,
proof steps, searches, creation fields, and matching Lean records. Neither restates
the detector theorem or has an unproved clause.

Change record: `coord/changes/supported-detector-open-lift-core-proof-context.md`.

## Second reading by C2

1. Compared the delivered item to the repository with `diff`. Existing declaration
signature, universes, visibility, definitions and public imports are byte-for-byte
unchanged. Only proofs, proof imports and recorded proof-elaboration commands differ.
The two added modules are new. No forced adaptations. Verdict: pass.

2. Compiled all three modules through `lcompile.py --all`, without warnings or errors.
Scanned for sorry, axiom, unsafe, opaque, implemented_by, extern and skipped kernel
checking: none in the delivered sources. Printed the axioms of all three public
theorems in scratch copies: only the standard axioms and dependency `sorryAx`.
There are no definitions or internal holes in this delivery. Verdict: pass.

3. Read both new statements, their docstrings and nodes, and checked empty/full
opens, unrestricted support, all shifts and zero objects. Repeated library searches
with alternative wording. The proposed localization hole is strictly part of the
argument and true, and was then proved with existing APIs. No split-off sorry remains;
no duplicate public result or restatement of the item was found. Verdict: pass.

4. Read the proof from the detector conclusion backwards through the shifted retract,
map lift, induction and explicit cover/support construction. The route follows
Tag 0A9A and preserves the unit's recorded route. All imports serve statements or
proofs. The report lists the only old proof dependency removed, the general
ringed-space derived adjunction. Verdict: pass after closing the proposed new hole.

5. Compared the DAG steps and proof dependency unions with the Lean implementation.
Checked source, chapter/unit, blueprint, creation, search and Lean fields on the
new nodes. Updated the localization node to record the proved smaller-open
localization API and actual upstream adjunction route. Verdict: pass.

Changes by the second reader: closed
`AlgebraicGeometry.open_derived_localization_adjunction`; added its required plain
proof imports and local instances; replaced the two new theorem proof docstrings
with the actual proof routes; updated the localization node and rewrote the report
to record one original hole closed and zero added. The original core proof is kept.
