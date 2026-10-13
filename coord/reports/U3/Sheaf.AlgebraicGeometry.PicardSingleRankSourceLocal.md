## What changed

Proved `AlgebraicGeometry.Scheme.picardUniversalSingleRankMatch_of_source_local`
in `Sheaf.AlgebraicGeometry.PicardSingleRankSourceLocal`, preserving its signature
and public import. The proof constructs an inverse-image neighborhood, applies
its local universal condition, identifies the smaller open with its image, and
transports both rank witnesses using open base change and tensor composition.

Repaired the landing refusal by deleting the local private `tensorRank` and
`tensorRankComp` theorems, and the local private `tensorIso` definition.
Added the proof-only `import all
Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction` and reused that
module's existing private `tensorIso` and `tensorRankComp`. Ordinary import
would hide these private declarations; `import all` makes them accessible
without changing either module's public interface. Updated the node's proof,
proof dependencies, and proof origin to record this reuse.

The remaining private open-base-change helper is adapted from the sectionwise
argument in `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.
No other module was edited.

## Proved and sorry left

Closed the only hole:
`AlgebraicGeometry.Scheme.picardUniversalSingleRankMatch_of_source_local`
(node `lem-sc-picard-single-rank-source-local`). No `sorry` remains in the
item and no holes were added or split off. This is a proof, not a decomposition.
The repaired module compiles without errors or warnings in 10.8 seconds.
The existing imported helpers are proved; their module's other declarations
are not newly proved by this delivery.

## No longer needed

No import is removed relative to the repository version: its sole public import,
`Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch`, is retained. During the
first worker's repair, the redundant direct proof import
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank` and local `tensorRank`,
`tensorRankComp`, and `tensorIso` declarations were removed from the earlier
candidate. The final proof-only conjunction import supplies the existing helpers.
No original proof dependency is unused: both the single-rank definition and
tensor pullback composition remain used. No DAG module is pruned; the conjunction
node is added as the home of the reused helpers.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated the statements of the private `tensorRank`
and `tensorRankComp` helpers in `PicardUniversalRankMatchConjunction`, triggering
the landing tool's duplicate-statement refusal. The repair imports and uses
the existing declarations instead. It also removes the duplicated `tensorIso`
construction. No signature, visibility, definition used by a target, or unit
route was changed. The prior second-reading record has been removed because
it reviewed the superseded version; the second reader must check this repair.

## Second reading by U3

1. PASS: compared the sole delivered module against the repository with `diff`.
The existing public theorem signature, its visibility, docstring, and the sole
public import are byte for byte unchanged. The added import is proof-only
`import all`; the three new definitions are private proof helpers. No existing
statement or definition changes, and no change record is required.

2. PASS: compiled the module locally through `lcompile.py`, without errors or
warnings (8.6 seconds). Compiled a scratch copy with `#print axioms` for
`tensorRestrict`, `pushforward_restrict_square`, `directImageOpenIso`, and
`picardUniversalSingleRankMatch_of_source_local`, as well as the imported
`tensorIso` and `tensorRankComp`. Every result lists only `propext`,
`Classical.choice`, and `Quot.sound`; none lists `sorryAx`. The delivered source
contains no `sorry` or forbidden declaration. Choices are of adjunctions and
composition isomorphisms justified by proved universal properties, not arbitrary
witnesses of an unproved existence assertion.

3. PASS: there are no split-off statements or new holes. Checked that the local
comparison definitions implement restriction along an open cartesian square;
the reference witness is transported along the explicit pullback lift. Empty
test schemes have no points to check; rank zero and empty fibres require no
extra assumption. Searched both library roots with `rg`, Mathlib's module-sheaf
sources, Loogle for `SheafOfModules.pushforwardComp`, and LeanFinder for
restriction/direct image along an open cartesian square. The existing tensor
rank helpers are reused. The analogous private comparison in DirectImage.Sections
would require importing that large higher-cohomology module; the present local
sectionwise construction uses the same Mathlib primitives without that import.
No missing split-off node or duplicate public statement was found.

4. PASS: read the proof from the target downward. It chooses the inverse-image
neighbourhood, applies the local hypothesis, takes the image of the resulting
smaller open, and transports the two exact rank witnesses. It uses both original
proof dependencies; none belongs under No longer needed. The public import is
needed by the statement, and the proof-only import supplies both reused helpers.
Read `dag/units/sk-prop-av-cube.json`: its statement, steps, and `realized` are
unchanged, and this local reduction bypasses no unit step. No module is pruned.

5. PASS: compared the delivered node with the original. Only `proof`,
`proof_deps`, and `proof_origin` change. Their steps match the restriction square,
image-open isomorphism, tensor composition, and reference pullback lift in Lean.
The proof dependencies are the union of the steps' uses, including the home of
the reused private helpers. The statement and Lean signature record are unchanged.

Second-reading changes: corrected No longer needed to distinguish imports
removed from the earlier candidate from the final diff against the repository;
added this review and axiom-check evidence. No Lean or DAG repair was necessary.
