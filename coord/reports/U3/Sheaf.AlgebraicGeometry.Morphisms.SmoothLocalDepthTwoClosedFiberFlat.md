## What changed

Replaced the sorry in `SmoothLocalDepthTwoClosedFiberFlat` by a complete Lean reduction,
without changing its signature or any existing public import. Added proof-only imports
of `ClosedFiberPowerSeriesTest`, `PowerSeriesTestFiniteExtensionFlat`,
`Sheaf.RingTheory.FlatLocalDepthFormula`, Mathlib faithfully flat ring maps, and
`Mathlib.RingTheory.MvPowerSeries.Equiv` for the Noetherian instance.

Four proved private helpers implement descent of flatness along a faithfully flat
ring map, stalkwise flatness descent from a flat test scheme, compatibility of an
etale restriction with base change, and preservation of boundary depth under flat
base change. The main proof constructs the formal test, transfers the hypotheses,
applies the power-series calculation, and descends to the specified original stalk.
Updated the assigned node to record those actual steps and dependencies.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.flat_stalk_of_smooth_local_depth_two_closed_fiber`.
Its proof is a decomposition, not an unconditional axiom-free proof: one upper hole
closed and two strictly separate lower holes added. No sorry remains in the item's module.

The two new sorries, each the entire proof of a public named theorem, are:

- `AlgebraicGeometry.Scheme.exists_closed_fiber_power_series_test`
  (`lem-sbc-closed-fiber-power-series-test`): geometric test construction,
  independent of the finite cover.
- `AlgebraicGeometry.Scheme.flat_of_power_series_depth_two_finite_extension`
  (`lem-sbc-power-series-test-finite-extension-flat`): purity calculation on a
  positive-dimensional power-series spectrum, independent of the original smooth
  morphism and closed fibre point.

All three modules compile together without warnings using lcompile.py.
The boundary-depth transfer uses the existing named flat local depth formula;
its existing dependencies are retained, not proved or restated here.

## No longer needed

None. The original module had no proof-dependency imports and its node had no
proof_deps. Every added proof-only import is used. The existing public imports
and unit route are preserved. No existing node or module is pruned. The second
reading narrowed both new modules' public power-series imports from Equiv to Basic;
Equiv is used only as a proof import of the main module.

## Where the brief, the DAG or earlier work was wrong

The assigned node's proof text cited several non-elementary Stacks results, but
its uses and proof_deps were empty. There were no named declarations to instantiate
for its geometric formal-chart construction or power-series purity calculation.
The two new nodes make precisely these separate pieces available as further items.
The earlier sandbox attempt left the original sorry and two useful descent scratch
files; their descent argument is now incorporated and compiled in the main proof.

The new statements were checked on empty finite covers, the open equal to the whole
spectrum, and relative dimension zero. The geometric test needs no cover; dimension
zero is excluded by density and the closed point lying outside U. The purity lemma
includes empty covers and the whole open, and explicitly requires n > 0 as in 0EYA.
No witnesses are placed in a definition: the existential formal test is eliminated
only inside the theorem proof. The generic prime is specified by equality of its
actual prime ideal with the extended maximal ideal, not by an unspecified point
lying over the closed base point.

Searches of the whole blueprint for power series and completion produced no exact
existing blueprint statement. LeanFinder returned smooth-chart and etale algebra
facts, not either new statement; Mathlib grep searches returned no matching purity
or formal-chart theorem. LeanSearch returned Internal Server Error and is recorded
as unavailable, not as absence. Source: Stacks Project Tags 0EYB and 0EYA, read
from their published pages; the local literature checkout is absent on this machine.

## New nodes

`lem-sbc-closed-fiber-power-series-test` in
`lean/Sheaf/AlgebraicGeometry/Morphisms/ClosedFiberPowerSeriesTest.lean` isolates
residue extension, the etale slice, and completion of the smooth chart. It returns
a genuine power-series spectrum with a flat map, a point meeting the original closed
boundary point, the punctured-base open condition, and the extended-maximal-prime
open condition. It assumes nothing about E or p.

`lem-sbc-power-series-test-finite-extension-flat` in
`lean/Sheaf/AlgebraicGeometry/Morphisms/PowerSeriesTestFiniteExtensionFlat.lean`
is the finite depth-two extension consequence of Tag 0EYA and uniqueness in 0EY6(2).
It has no smooth morphism, no original base A, and no chosen closed fibre point.
There are no statement changes, forced adaptations, or change records.

## Second reading by U3

1. Compared the delivered main module with the repository using diff and checked the
   existing theorem signature byte for byte. PASS: the original docstring, signature,
   visibility and public imports are unchanged; only proof imports, private proved
   helpers and the proof body are added. There are no definitions or interface changes.
2. Compiled all three modules in import order using lcompile.py, including after the
   import repair below. PASS: no errors or warnings. A scratch copy with explicit
   #print axioms for all three public theorems reports only propext, Classical.choice,
   Quot.sound and sorryAx. The two named new theorems are the only new holes; the main
   theorem has no sorry in its body. Read the tensor-injectivity descent argument,
   pullback-point construction, restriction square and depth transfer: all establish
   precisely the required local flatness. No forbidden declarations, data definitions,
   or choice of an unproved existential witness in a definition occur.
3. Read Stacks https://stacks.math.columbia.edu/tag/0EYB (closed-point construction),
   https://stacks.math.columbia.edu/tag/0EYA (both open conditions and positive dimension),
   and https://stacks.math.columbia.edu/tag/0EY6 (uniqueness, part 2).
   PASS: the geometric lemma assumes exactly the local smooth chart hypotheses and
   concludes only a test construction, with no finite cover. The purity lemma assumes
   exactly the two open conditions of 0EYA, plus the finite extension and its boundary
   depth needed for 0EY6(2). The extended maximal prime is specified by ideal equality,
   so it cannot be replaced by an arbitrary closed-fibre point. These are separate,
   strictly smaller arguments, not renamed copies of the assigned theorem.
   Checked empty covers, V = the whole spectrum, and n = 0: the first two are harmless;
   the geometric construction excludes n = 0 because the closed boundary point would
   be generic in its smooth closed fibre and hence lie in the dense open. In the test
   construction the finite local and localized etale base changes have zero-dimensional
   local closed fibres, so no nonclosed point of the new local base lies above the old
   closed point. Flatness makes the formal closed-fibre generic map to a generic of
   the smooth fibre, where density applies.
   Independently searched LeanFinder for extension of finite etale covers across a
   power-series punctured base and completion along a smooth section; results concern
   standard etale algebras and formal-smooth lifting, not these statements. The msearch
   grep for section/completion and power-series/etale likewise gives no replacement.
   Searched lean/, dag/nodes/ and the upstream WeilConjectures sources by Stacks tags,
   purity and power series. No matching lower lemma is already stated. Neither lower
   hole can be closed in a few minutes from those results.
4. PASS: the proof starts at the assigned hole, constructs the test, transfers etaleness
   and depth by proved helpers and the existing flat local depth formula, invokes the
   separate power-series calculation, and descends flatness. Every added proof import
   is used. The original proof_deps was empty, so there are no omitted prunings.
   Read dag/units/sk-prop-input-spreading.json, including its realized record (all
   entries currently empty). This delivery does not alter that record or bypass a
   realized unit node; it refines the same local completion/purity argument below it.
5. PASS: the existing node changes only proof, proof_deps and proof_origin. Its five
   steps match the Lean construction, restriction, depth transfer, purity application
   and descent. Checked all three lean.statement records verbatim against their files
   and each proof_deps against the union of step uses. Both new nodes have source,
   complete prose proof, searches, split status, creation/blueprint/unit records and
   their new Lean module/declaration records. Their docstrings give the same proofs.

Changed during second reading: replaced the public MvPowerSeries.Equiv imports in
both new statement modules by MvPowerSeries.Basic, which suffices for their signatures.
Moved Equiv to a plain proof-only import in the main module, where its Noetherian
power-series instance is used for boundary-depth transfer. This avoids exposing a
proof dependency through the new interfaces. No proof or statement was rewritten.
Recompiled successfully and checked signatures, dependency unions and line widths.
