## What changed
Proved `smoothProperCurve_dualizing` by specializing `smoothProper_dualizing` to `Spec k`, using the canonical compact and locally Noetherian instances. Added the intermediate module `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafOneIso` and transported its degree-one isomorphism through the derived single and shift functors.

## Proved and sorry left
`smoothProperCurve_dualizing` is proved. `exteriorSheaf_one_iso` remains a sorry, split as node `lem-sc-smooth-proper-curve-dualizing-exterior-one`.

## No longer needed
No planned imports or nodes were removed; the original sole proof dependency
`lem-sc-smooth-proper-relative-dualizing-general` remains used.

## Where the brief, the DAG or earlier work was wrong
The general theorem concludes with the custom `exteriorSheaf`; the curve target uses `relativeDifferentials` directly, requiring an explicit degree-one exterior-sheaf identification.

## New nodes
`lem-sc-smooth-proper-curve-dualizing-exterior-one`: canonical identification of the first exterior sheaf with the original sheaf. Node file: `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-curve-dualizing-exterior-one.json`.

## Second reading by F1

1. Compared both delivered modules with the repository. The existing curve theorem's
signature and docstring are byte-for-byte unchanged; its only interface change is a plain
proof import, invisible to downstream modules. The exterior-one module is new. No existing
definition or target statement changes; no change record is required.

2. Both files compile locally without errors or warnings. The curve theorem has no direct
sorry. The only delivered sorry is the named `exteriorSheaf_one_iso`, with its matching
node and complete docstring proof. No forbidden declarations or hollow definitions were
introduced. Scratch-copy `#print axioms` checks for both theorems show only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`, permitted here because the imported general
duality theorem and the degree-one lemma are still open.

3. The split-off lemma is true for arbitrary sheaves, with no smoothness, properness or
local-freeness restriction needed. Tested its mathematical edge cases: the zero sheaf,
the empty scheme and arbitrary-rank modules on affine opens all have first exterior
power equal to the original module. Restriction compatibility follows on singleton
wedges and hence on all sections. Sheafification of an already-sheaf is identified by
the invertible adjunction counit. Loogle, Lean Finder and grep searches, plus searches
of both library roots, found sectionwise `exteriorPower.oneEquiv` and sheafification
infrastructure, but no existing theorem about this custom `exteriorSheaf`. This is
strictly a part of the argument, not a restatement of the curve-duality theorem.
An attempt to close it locally hit elaboration's heartbeat limit while constructing
the presheaf isomorphism; the attempted proof was removed, leaving the stated reduction.

4. The proof specializes the existing general theorem and maps the exterior-one
isomorphism through the derived single and shift functors. The canonical field-spectrum
instances synthesize without local instance declarations. All imports are used for
signatures or the proof; both proof imports are plain `import`. No original proof
dependency or planned import is pruned. Read `dag/units/sk-thm-picard-duality.json`:
its `realized` statement and step lists are empty, and this delivery leaves the recorded
unit route unchanged. Checked the general-duality source against
[Stacks Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT); the degree-one specialization
matches it. The local Stacks TeX is absent on this machine.

5. Repaired the existing curve node so its second proof step and `proof_deps` explicitly
cite the new exterior-one node. The first step still cites the general-duality node.
Repaired the new node's proof and dependencies to name the exterior-sheaf construction;
recorded all four actual searches (LeanSearch returned HTTP 500 and is marked unavailable). Lean declaration records agree with the files.
No existing node statement or definition was changed.

Changes by the second reader: removed two redundant `letI` declarations (and their
linter warnings); expanded the split-off theorem's source and complete docstring proof;
completed the new node's searches and proof dependencies; delivered the existing curve
node with accurate proof steps and dependencies. One of one original sorry is closed
by reduction; one intermediate theorem is split off; none pruned.
