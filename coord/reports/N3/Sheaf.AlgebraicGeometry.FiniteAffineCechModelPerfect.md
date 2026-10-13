## What changed

Proved the unchanged `AlgebraicGeometry.Scheme.Modules.finiteAffineCechModel_perfect`
from two strictly narrower statements in new modules:
`Sheaf.AlgebraicGeometry.FiniteAffineCechModelDerivedComparison` and
`Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect`.
The first compares the specified complex with derived direct image for an arbitrary
quasi-coherent module over a separated quasi-compact morphism to an affine base;
it has no properness, relative flatness or perfection conclusion. The second proves
perfection of the direct image of a finitely presented relatively flat single module;
it has no cover or specified Cech model. Neither is a restatement of this item.

The private, fully proved `flatOver_restrict` helper transports the affine section
flatness condition along the two open immersions, using `morphismRestrict_appLE`
and `Scheme.Opens.ι_appIso` to identify scalar actions. Properness, finite presentation,
quasi-compactness and finite presentation of the restricted module follow by instances.
The proof applies both intermediate statements and composes their local derived
isomorphisms, retaining exactly the supplied target and localized-open localizations.
Only the source localization is chosen standard, independently of the target universe.
Added proof-only imports of the two new modules.
No existing statement, visibility or definition changed. The original node's proof
and dependencies now describe the actual reduction. No forced adaptations.

All three delivered modules compile with `lcompile.py --all` and the final parent
module also compiles alone. Edge cases checked in the intermediate statements:
empty cover forces empty source; empty intersection and zero module give zero terms;
zero rings and empty opens require no extra hypotheses. The second statement does
not assume flatness of the morphism, in agreement with Stacks 0B91(2).

Searches: Lean Finder for Cech-model perfection returned only affine-limit results;
Loogle for IsPerfect returned unrelated pairing and graph results; direct grep found
no Mathlib derived Cech/perfection result. A separate Lean Finder search for proper
perfect direct image returned only flat morphism results. LeanSearch was attempted
for both components and returned Internal Server Error. Blueprint search found the
existing Cech-resolution node and the projective Noetherian special case, neither
providing the explicit-model comparison or the general usable single-module interface.
Sources were read at https://stacks.math.columbia.edu/tag/01XD,
https://stacks.math.columbia.edu/tag/01FK,
https://stacks.math.columbia.edu/tag/0B91 and
https://stacks.math.columbia.edu/tag/0A1H.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.Modules.finiteAffineCechModel_perfect`
(node `lem-pc-finite-affine-cech-model-perfect`). No sorry remains in the item's module.
The private helper `AlgebraicGeometry.Scheme.Modules.flatOver_restrict` is fully proved.

Two holes added, each exactly a named public theorem's whole proof:

- `AlgebraicGeometry.Scheme.Modules.finiteAffineCechModel_derivedComparison`
  (node `lem-pc-finite-affine-cech-model-derived-comparison`).
- `AlgebraicGeometry.properFlat_single_derivedDirectImage_perfect`
  (node `lem-pc-proper-flat-single-derived-direct-image-perfect`).

This is a decomposition: one original hole closed, two lower holes added, net minus
one hole closed. It is not a sorry-free proof. The lower modules have complete proof
plans with sources and independent source/base localization universes; their only
sorries are these two declarations. No data are defined from an arbitrary existence
witness, and no sorry appears inside a definition or a private helper.

## No longer needed

No original imports removed: all five public imports support the unchanged statement
or the definitions it mentions. No globally unreachable module is claimed.

The item's proof no longer directly uses `lem-pc-cech-resolution`
(`Sheaf.AlgebraicGeometry.CechResolution`) or `lem-pc-rf-perfect-base-change`
(`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`): both would close import
cycles. Their usable mathematical components are isolated in the two new statements.
`lem-pc-alternating-cech-computes` is no longer a direct dependency of the parent;
it remains part of the derived-comparison node's proof plan and is not globally pruned.
The explicit-model definition remains a statement dependency rather than a separate
proof dependency. The second reader removed the unused proof-only import of
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` from the parent module;
compilation succeeds without it. No unused trial import remains in the delivered files.

## Where the brief, the DAG or earlier work was wrong

The stated plan cannot be implemented by importing its recorded declarations into
this item. `import_direction.py may` rejects CechResolution and
PerfectDirectImageBaseChange: each already reaches this item. In particular,
CechResolution reaches AffineOpenPushforwardAcyclic, then the source
DirectImage.AffineMorphism, DirectImage.FiniteFreeComplex, ProperFlatCechModel,
ProperFlatCohomologyModel, ProperFlatCohomologyProperties,
ProperFlatFinitePresentationModel, ProperFlatBoundedPresentationModel and
ProperFlatAffineCechPerfectModel, which imports this item.
PerfectDirectImageBaseChange reaches ProperSupportPerfectDirectImage, then
NoetherianApproximationData, the source DirectImage umbrella, and the same
FiniteFreeComplex chain. The existing alternating exchange resolution has the
same problem. Importing lemmas with sorry was not the obstacle; import cycles were.

The perfect-direct-image theorem also imposes global scheme localization and tensor
pullback additivity families absent from this item's signature. Choosing a global
standard family works only after transporting the supplied target localization;
the two new independent-universe interfaces avoid imposing or transporting that
family. The supplied target and open-site localizations are kept directly.

The unit route remains the original finite affine Cech identification and proper
perfect direct image via Noetherian approximation. No unit or chapter record changed.

## New nodes

`lem-pc-finite-affine-cech-model-derived-comparison`, in
`dag/nodes/sec-picard-framework/`, records the derived comparison for the specified
section complex, with the augmented acyclic-resolution and ordered-tuple comparison
as its two proof steps. Its module is
`lean/Sheaf/AlgebraicGeometry/FiniteAffineCechModelDerivedComparison.lean`.

`lem-pc-proper-flat-single-derived-direct-image-perfect`, in the same chapter,
records the proper-single-module perfection component of Stacks 0B91(2), proved in
words by the Noetherian approximation and Noetherian perfect-image argument of 0A1H.
Its module is
`lean/Sheaf/AlgebraicGeometry/ProperFlatSingleDerivedDirectImagePerfect.lean`.
No change record is needed: existing interfaces and definitions are unchanged.


## Second reading by N3

1. Compared the parent module with the repository using `diff -u`: the existing
   theorem signature, docstring, visibility, and every definition are byte for byte
   unchanged. Only its proof, a proved private helper, and proof-only imports differ.
   Both other modules are new, with no existing interface modified. No change record
   or forced adaptation is required. Verdict: pass.
2. Compiled all three modules in dependency order with `lcompile.py --all`, then
   compiled the parent alone after removing its unused import. A scratch copy with
   `#print axioms` for the parent and both new theorems reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The scratch file was removed.
   Inspected all delivered source: the only direct sorries are the two reported
   whole public theorem proofs; the helper is proved and no definition is added.
   No prohibited declaration or foreign implementation appears. Verdict: pass as
   a decomposition, not a complete proof.
3. Read Stacks 01XD and 01FK for the affine acyclic resolution and ordered complex,
   and 0B91(2) and its proof 0A1H for the single-module theorem. Separatedness over
   an affine target supplies affine intersections; quasi-coherence is explicit in
   the comparison. Properness plus local finite presentation gives the finite
   presentation required by 0B91(2); relative flatness is a hypothesis on F and
   no flatness of f is used. Checked r=0 (cover forces empty source), r=1 (the
   affine section model), repeated cover opens, empty intersections, zero module,
   and zero base ring. Both statements are true independent components: one
   identifies a specified complex without perfection, the other proves perfection
   without a complex or covering. Their docstrings and nodes state sourced proof
   plans. Independent Lean Finder searches for acyclic affine-cover pushforward
   and proper pushforward with finite Tor amplitude, Loogle for perfect/image, and
   grep for acyclic resolutions found no usable replacement. Read CechResolution,
   AlternatingCechComputes, PerfectDirectImageBaseChange and
   NoetherianPerfectDirectImage: the first two do not identify this specified model,
   and the perfect-image interfaces need additional localization/tensor data.
   The related FlatOverAffineOpenRestriction module exposes a spectrum-chart
   theorem; its restriction-only helper is private, so it cannot replace the
   short private helper directly. Neither large new hole can be closed in a few
   minutes from the available interfaces. Verdict: pass.
4. The actual parent proof restricts the module, applies the two components,
   maps the comparison isomorphism through exact open restriction, and composes
   with each strictly perfect witness. All original public imports support the
   unchanged statement. Removed the unnecessary new proof-only import
   DerivedOpenRestrictionMaps and recompiled successfully. The No longer needed
   section accounts for all five old proof dependencies: perfect-complex stays;
   explicit-model becomes statement-only; alternating comparison moves to the
   lower plan; CechResolution and PerfectDirectImageBaseChange cease to be direct
   dependencies. The unit's Cech/Noetherian-approximation route is retained.
   `dag/units/sk-thm-picard-coherence.json` already has empty `realized` arrays;
   this pre-existing realization gap is reported here and no unit record is
   changed by this proof delivery. Verdict: proof route passes; existing unit
   realization metadata remains incomplete.
5. Compared the old and delivered parent node: only proof, proof_deps and
   proof_origin differ. Its three proof steps match the restriction argument,
   derived comparison, and local witness composition. Both new nodes have source,
   complete proof steps, dependency unions, searches, split status, creation and
   blueprint provenance, chapter/unit and matching Lean records. Read the cited
   acyclic-resolution, approximation, Noetherian perfect-image and relatively
   flat base-change node statements; they supply the mathematical components
   described. Traversing proof_deps with the delivered nodes overlaid found no
   cycle returning to the item. Verdict: pass.

Second-reading changes: removed one unused proof-only import, corrected the report's
import inventory, and recorded this independent review and the existing unit metadata
limitation. No theorem statement, definition or proof argument was changed. One old
hole is closed and two lower holes remain added, a decomposition with net -1.
