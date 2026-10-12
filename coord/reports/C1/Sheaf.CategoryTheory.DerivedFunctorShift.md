## What changed

Proved `CategoryTheory.Functor.isTriangulatedLeftDerivedDefinedAt_shift_iff` in
`Sheaf.CategoryTheory.DerivedFunctorShift`, preserving its entire signature and visibility.
Added six private, fully proved construction/transport helpers in the same module:
`pro_map`, `pro_iso`, `pro_reindex`, `pro_reindex_iff`, `shiftOver`, and
`shiftOver_equivalence`. These implement the existing node's denominator-equivalence
and essential-constancy steps directly; they add no public interface or proof obligation.
The comparison of the supplied cones uses Mathlib limit uniqueness and hom-extensionality.
Updated the node's proof, proof_deps, and proof_origin to match this route.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Functor.isTriangulatedLeftDerivedDefinedAt_shift_iff`
(node `lem-pur-derived-functor-shift-05su`). No holes remain in the item;
no holes were added or split off. This is a complete proof, not a decomposition.
Local compilation passes with no warnings. An explicit `#print axioms` of the
proved theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The prescribed dry run printed OK (only the second reading is pending); nothing pushed.

## No longer needed

Removed the proof imports
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit` and
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`.
The hom-colimit lemma, node `lem-pc-essentially-constant-pro-hom-colimit`, is unnecessary
for this proof and was removed from proof_deps: the statement already supplies limit
cones, so Mathlib's `IsLimit.conePointUniqueUpToIso` proves their uniqueness directly.
The essential-constancy definition, node `def-pc-essentially-constant-pro-diagram`,
is still used and remains in proof_deps; its separate direct import is redundant
because the retained public import exports it. No other planned dependency is pruned.
This reports the item's dependency pruning, not a claim that no other target uses the
hom-colimit module. The unit `sk-def-sf-operations` has empty realized statement and
step lists, so no fixed unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous theorem docstring described the hom-colimit theorem as identifying the
supplied limit values, but its actual signature only asserts Hom-colimit bijectivity.
It is unnecessary here. The Stacks 05SU(2) proof is omitted; the existing DAG's
shift-denominator and essential-constancy argument was completed explicitly in Lean.
The local Stacks source file is absent, so the source statement was checked at
https://stacks.math.columbia.edu/tag/05SU and Mathlib's relevant source files were read.
Recorded searches used leanfinder, loogle, and grep through the prescribed msearch tool;
no existing theorem of this exact statement was found.

## Second reading by C1

1. PASS: Diffed the sole delivered module against the read-only repository version,
   and mechanically compared the existing theorem signature byte for byte through
   `:= by`. It is identical, with unchanged public visibility. No existing definition
   or statement was altered; the additions are private proved helpers and a concrete
   denominator functor. The remaining changes are proof, documentation, authorship,
   and removal of two plain proof imports. No change record is needed.
2. PASS: Independently compiled the delivered file through lcompile.py with no errors
   or warnings. A fresh scratch copy printed axioms for all six helpers and the main
   theorem: every declaration uses only propext, Classical.choice, and Quot.sound.
   Scanned the delivered source for holes and prohibited constructs: none occur.
   shiftOver explicitly constructs its object and morphism maps; asEquivalence uses
   a proved full/faithful/essentially-surjective argument, not an unproved witness.
3. PASS: There are no split-off statements or new holes. Read every helper proof:
   functoriality transports the retraction and factorization equations; naturality
   cancels the diagram isomorphisms; the equivalence's counit and inverse unit give
   the correctly oriented earlier-stage maps. Small cases checked mathematically:
   n = 0 gives identity-shift transport; a one-object constant diagram preserves its
   split retraction; an empty index cannot satisfy essential constancy and cannot
   become nonempty under equivalence. Shift membership works for either sign of n,
   and proof irrelevance makes the leg equation independent of the chosen hs.
4. PASS: Repeated searches with different wording using prescribed grep, leanfinder,
   and loogle calls, and rg over Sheaf, the upstream library, and Mathlib. No existing
   proved result replaces the complete argument. The library's more general
   initial_iff_essentiallyConstantProDiagram is still sorry and would introduce
   avoidable dependencies; direct equivalence transport is justified here. Mathlib's
   conePointUniqueUpToIso and hom_ext are already used for comparison and uniqueness.
   The one retained public import is needed by the statement; there are no proof-only
   public imports. The removed hom-colimit node is exactly the sole old proof_deps
   entry not retained, and No longer needed names both removed modules. Essential
   constancy remains available through the necessary public import. Read the unit
   sk-def-sf-operations: its realized statement and step lists are empty, and this
   denominator/shift argument stays within the item's route.
5. PASS: Diffed the node JSON; only proof, proof_deps, and proof_origin changed.
   The union of the proof steps' uses equals proof_deps. Its four steps describe
   the actual denominator equivalence, transport, reverse implication via inverse
   shift, and limit comparison. The statement, source, unit, and Lean record are
   unchanged. No new nodes are required for open obligations, since none were added.

Second reading changed only this report: added the independent review above.
The Lean proof, imports, and node metadata required no repair. One original hole
was closed, zero were added, and zero were split off.
