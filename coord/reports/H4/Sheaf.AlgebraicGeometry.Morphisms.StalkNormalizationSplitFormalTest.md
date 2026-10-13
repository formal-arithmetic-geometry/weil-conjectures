## What changed

Replaced the item's single sorry by a complete Lean assembly: apply
`AlgebraicGeometry.Scheme.exists_smooth_section_completion_chart` to the smooth
local pullback and its section, apply the new fixed-test splitting theorem, and
evaluate the entire-section equality at the closed point. The existing declaration's
signature and all public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalSplit`, with one
named theorem for the unresolved splitting calculation. It takes an already
constructed flat test and the two actual chart equations, and only produces its
splitting over the test. Updated the item's node to match this route.

Removed the earlier attempt's unnecessary `StalkNormalizationFormalData` module
and node: the existing completion-chart theorem already gives its conclusion and
more. Removed unchanged dependency copies from the sandbox; these were not changes
to the library. Removed the stale second-reading text because the proof and helper
interface have now changed and require a fresh independent reading.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_normalization_split_formal_test`
(node `lem-sbc-stalk-normalization-split-formal-test`). Its proof constructs the
formal test using the existing chart and then combines the fixed-test splitting
with the origin equality. No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_normalization_formal_split`
(node `lem-sbc-stalk-normalization-formal-split`). Its proof is exactly `by sorry`.
This is a decomposition, with one hole closed and one added, not a fully discharged
mathematical theorem. Compared with the earlier sandbox attempt, there is one fewer
new hole. There are no definitions, axioms, or forced adaptations in this delivery.

## No longer needed

The direct proof imports removed from the item are:

- `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness`
- `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`
- `Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`
- `Sheaf.AlgebraicGeometry.Morphisms.SmoothSectionPowerSeriesChart`
- `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense`
- `Sheaf.RingTheory.FlatLocalDepthFormula`
- `Sheaf.RingTheory.NormalLocalDepthTwo`
- `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionFullyFaithful`

All except `SmoothSectionPowerSeriesChart` remain proof dependencies of the new
splitting item, so they are not claimed as pruned from the target closure.
`lem-sbc-smooth-section-power-series-chart` and its module are unnecessary on this
route: its extra generic-image conclusion is not used, and the existing
`lem-sbc-smooth-section-completion-chart` provides the required entire-section
compatibility. Other callers may still need the larger chart theorem.

The earlier sandbox-only `StalkNormalizationFormalData` module and
`lem-sbc-stalk-normalization-formal-data` node are unnecessary and not delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier new nodes had empty proof steps, placeholder natural-language
statements, copied blueprint tags and incorrect verbatim Lean records. The surviving
new node now has a self-contained statement, its own blueprint tag, the actual Lean
signature and the three remaining proof steps with their dependency nodes.

The earlier splitting helper assumed only equality of the images of the closed
point. Its written proof instead needed the entire zero-section equation and the
base equation to identify the punctured zero slice. The corrected helper requires
both equations; the existing completion-chart theorem supplies them. No existing
library statement or definition changes.

Checked the route against Stacks Project
[0EYJ](https://stacks.math.columbia.edu/tag/0EYJ),
[0EY6](https://stacks.math.columbia.edu/tag/0EY6), and
[0EY9](https://stacks.math.columbia.edu/tag/0EY9).
The new statement includes zero variables (the restriction is then the identity),
the trivial group (one summand), and disconnected torsors. Empty torsors cannot
satisfy the rational-point hypothesis. It does not require an invertible group
order: the formal depth-two calculation is separate from the trait case.

Searches: LeanFinder returned smoothness and completion flatness lemmas, Loogle
returned constant-coefficient identities, and library grep found the existing
completion chart but no fixed compatible test splitting theorem. LeanSearch was
unavailable (Internal Server Error); this is recorded without a search verdict.
The unit's completion followed by punctured-section splitting and depth-two
extension route is retained.

## New nodes

`lem-sbc-stalk-normalization-formal-split` states splitting of an already fixed flat
power-series map with its base and section compatibility equations. It isolates
the final part of the original argument, not the existence of the test. Its module
is `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalSplit`. Its three
steps are normalization/depth identification, splitting on the punctured section,
and extension of that splitting over the fixed formal test. No change record is
needed because no existing interface changes.

## Second reading by H4

1. **Interface unchanged — pass.** Compared the delivered item with the repository
   by `diff` and extracted the theorem text through `:= by`: the existing signature
   is byte-for-byte identical, including all hypotheses, local instances, the
   finite-normalization premise, the G-indexed coproduct equation, and the origin
   equality. Public imports are unchanged. The existing node differs only in
   `proof`, `proof_deps`, and `proof_origin`; no change record is needed.
2. **Lean proof and trust — pass.** Both modules compile locally through
   `lcompile.py --all`, without errors or warnings. The item constructs d and t
   with `exists_smooth_section_completion_chart`, passes its two compatibility
   equations to the fixed-test theorem, and applies `congrArg` at the closed
   point. The sole new sorry is the reported named theorem
   `exists_stalk_normalization_formal_split`; there are no definitions or forbidden
   declarations. Scratch copies with `#print axioms` were checked separately;
   the only axioms are `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
   from the explicitly open splitting calculation and its open dependencies.
3. **New statement — pass as decomposition.** Read the fixed-test signature,
   docstring and node against Stacks 0EYJ's depth-two local calculation, 0EY9's
   full faithfulness, and 0EY6's uniqueness and flat base change. The flat test is
   supplied, not chosen from an unproved existence theorem to define data. Its
   base equation identifies the punctured-base open, and its entire-section
   equation identifies the zero slice; equality only at the closed point would
   not suffice. The missing calculation is strictly the splitting of this fixed
   test: it neither constructs the chart nor proves the item's point equation.
   Normality and finite normalization supply boundary depth via going down and
   S2; flat base change preserves that depth. The split comparison has depth two
   by flatness over A. The generic rational point and torsor identity give
   exactly G copies on the punctured section. For positive d, full faithfulness
   lifts the isomorphism and its inverse; for d=0 the slice is the identity.
   Trivial G gives one copy, disconnected torsors are allowed, and empty torsors
   contradict hZ. The depth-two part does not use the invertibility assumption
   needed in the trait argument. Independent LeanFinder search for a finite
   etale cover trivial on the formal punctured zero section found only ordinary
   etale algebra lemmas; Loogle `MvPowerSeries, Scheme` returned an unknown
   identifier, not a positive verdict. msearch grep and direct rg over both
   library roots found no fixed-test splitting declaration. Also inspected
   `PowerSeriesPuncturedFiniteModel`: it gives an unspecified finite coefficient
   model, not this G-indexed splitting. Closing the new hole needs the substantial
   remaining normalization/section assembly, not a few-minute existing lemma.
4. **Route and pruning — pass.** Read the unit's `realized` record (currently
   empty) and its depth-two/completion step. The delivery keeps that route:
   completion, punctured-section splitting by full faithfulness, and extension
   by depth-two uniqueness. The weaker existing completion-chart theorem is
   enough; the larger power-series-chart theorem's generic-image clause is not
   used. All eight former direct proof dependencies are listed under No longer
   needed; seven move to the new calculation and only the larger chart is
   bypassed. Both new imports in the item are proof-only plain imports. The new
   helper's public imports provide its signature, while its plain imports name
   the remaining DAG proof inputs. No closure pruning beyond the reported chart
   bypass is claimed, and the net hole change is zero.
5. **DAG agreement — pass.** The item's two steps name exactly the completion
   chart and the fixed-test calculation used in Lean. The new node's self-contained
   statement includes both compatibility equations, its Lean signature is
   verbatim, and its proof steps have proof_deps equal to their union. Its source,
   searches, creation record, blueprint ancestry, chapter, unit and Lean record
   are present. The seven imported remaining dependency statements supply the
   normality/density, depth, uniqueness, action, generic fullness and punctured
   full-faithfulness inputs described in its proof.

Second reading changed only this report: added the independent checks and explicit
zero-net decomposition assessment. No Lean proof, statement, definition or node
needed repair. Axiom scratch copies are excluded from delivery.
