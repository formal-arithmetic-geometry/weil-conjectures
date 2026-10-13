## What changed

The original declaration keeps its signature and now has a complete Lean proof.
Its geometric preparation and categorical lifting are implemented in two proved new modules:

- `StalkNormalizationFormalPuncturedRestriction.stalk_normalization_formal_punctured_restriction`
  proves that the normalization and constant cover restrict to finite etale covers, and proves
  the exact punctured-zero-slice condition. It uses relative normalization's integral-morphism
  isomorphism and smooth open base change; normality and depth are unnecessary for this step.
- `PowerSeriesPuncturedSplitAssembly.powerSeries_punctured_split_assembly` lifts both directions
  of a slice isomorphism using surjectivity and checks their inverse identities using injectivity.
  It also transports an isomorphism across an isomorphic base change.

The remaining geometry is stated in `StalkNormalizationFormalZeroSliceSplit`: splitting only
on the zero slice, via the rational point, extended group action, and generic-point full
faithfulness. This is strictly smaller than splitting on V: for positive d the zero section
is not an isomorphism. The main proof uses the existing punctured-section full-faithfulness
result for positive d, and proves the d=0 branch from `MvPowerSeries.isEmptyEquiv`.

The four modules compile together without errors or warnings through lcompile.py.
No existing statement, definition, or visibility is changed, and no adaptation is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.exists_stalk_normalization_formal_punctured_split`
(node `lem-sbc-stalk-normalization-formal-punctured-split`).

Also proved, without new holes:
`AlgebraicGeometry.Scheme.stalk_normalization_formal_punctured_restriction`
(node `lem-sbc-stalk-normalization-formal-punctured-restriction`) and
`AlgebraicGeometry.Scheme.powerSeries_punctured_split_assembly`
(node `lem-sbc-power-series-punctured-split-assembly`).

Exactly one added hole remains:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_zero_slice_split`
(node `lem-sbc-stalk-normalization-formal-zero-slice-split`). Its proof is exactly `by sorry`,
with a complete source-based proof in its docstring and node. No sorry remains in the item.
This is a decomposition: one original hole closed and one strictly smaller hole added,
not a claim that the complete geometric theorem is now axiom-free.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension` and
`Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`.
The old direct dependencies `lem-sbc-generic-fibre-action-extension` and
`lem-sbc-normal-integral-generic-hom-full` are no longer direct dependencies of the item.
Both remain needed by the zero-slice argument, and their imports moved to that new module. `PowerSeriesPuncturedSectionFullyFaithful` stays directly imported and is used.
No existing DAG node or module is claimed globally pruned.

The preparation proof does not need the originally suggested normal-smooth-scheme argument:
relative normalization over the original open already agrees with the integral finite cover.
It needs no normality, depth, flatness of t, section, rational point, or G-action.
No unused new proof import remains in either proved auxiliary module.

## Where the brief, the DAG or earlier work was wrong

The original numbered plan packaged several distinct comparison steps into one paragraph.
The three old dependency signatures do not directly expose the normalization/test comparisons
or the actual zero-slice isomorphism needed to apply full faithfulness. The new preparation
proves the former; the new slice node states the latter. The unit's prescribed local computation
is retained, including rational-point splitting and Tag 0EY9; no unit route changes.

The normality justification for agreement of relative normalization with PA over C_U was
unnecessary: PA -> C_U is finite, hence integral, and Mathlib already proves the required
isomorphism of its source with its relative normalization.

Read Stacks Tags 0EYJ (final local calculation), 0EY9 (fully faithful punctured restriction)
and 0BQM (generic-point full faithfulness), and the relevant Mathlib normalization source.
Tested the new statements conceptually on d=0, the trivial group, disconnected torsors,
and an empty finite etale cover in the generic assembly. The preparation also permits arbitrary
finite index types, including empty ones; its proof is independent of a group action.
LeanSearch returned an internal-server error. LeanFinder returned etale base-change and
forgetful-functor facts, not the geometric slice splitting. Loogle could not resolve the
unqualified preimageIso identifier; rg located and verified the categorical tool and the
normalization instances in source. No existing module states the complete zero-slice result.

## New nodes

`lem-sbc-stalk-normalization-formal-punctured-restriction` is fully proved in
`StalkNormalizationFormalPuncturedRestriction.lean`, including its private pullback and
stalk-point comparison helpers. Its proof depends on the existing smooth-normalization
base-change Mathlib leaf and standard proved primitives.

`lem-sbc-power-series-punctured-split-assembly` is fully proved in
`PowerSeriesPuncturedSplitAssembly.lean`. Its hypotheses are generic hom-set bijections
or an isomorphic base, and its categorical assembly adds no geometric hole.

`lem-sbc-stalk-normalization-formal-zero-slice-split` is the sole unfinished statement, in
`StalkNormalizationFormalZeroSliceSplit.lean`. It asserts an isomorphism only after pullback
along the zero section. It does not assume depth, flatness of t, or finiteness of n.
Its proof dependencies are the proved preparation, the existing action-extension node,
and the existing normal-integral generic-point fullness node. No change record is needed.

## Second reading by D2

1. **Interfaces: PASS.** Diffed the delivered item against the repository version. The sole
   existing theorem signature is byte-for-byte unchanged, including its local instances,
   flatness and finiteness hypotheses, depth hypothesis, and isomorphism base equation.
   Only its proof, proof imports, and explanatory text change. The other three modules are
   new; no definition or existing visibility changes, and no change record is needed.
2. **Lean proofs and axioms: PASS as a decomposition.** Independently compiled all four
   modules in import order through lcompile.py without errors or warnings. Scratch copies
   with #print axioms show exactly propext, Classical.choice and Quot.sound for the
   preparation and assembly; the slice statement and main theorem additionally use sorryAx.
   The slice theorem is the sole delivered sorry, exactly `by sorry`. No axiom declaration,
   unsafe/opaque/extern/implemented_by, kernel-check bypass, hollow definition, or arbitrary
   data chosen from an unproved existence theorem occurs. The proof's two branches correctly
   separate d=0 (an isomorphic restricted zero section) from positive d (full faithfulness).
3. **New statements: PASS.** Checked all three signatures against their nodes and tested the
   arguments on d=0, a trivial group, disconnected torsors, and empty covers/index types
   where the signatures permit them. The zero-slice theorem only asserts a splitting after
   base change; it removes the power-series lifting step and does not assume depth,
   flatness of t, or global finiteness of n. Its rational generic fibre splits by the torsor
   identity; generic-point full faithfulness over the normal punctured local base extends
   that splitting. Its docstring and node give the comparison and inverse-identity steps.
   This is a genuine proper reduction, not a renamed whole conclusion. Independently read
   [Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ),
   [Tag 0BQM](https://stacks.math.columbia.edu/tag/0BQM), and
   [Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9).
   Searched via msearch with a constant-generic-fibre query (LeanFinder), fully qualified
   CategoryTheory.Functor.FullyFaithful.preimageIso (Loogle), and split/generic/sigmaDesc
   patterns (grep), then read upstream torsor and split-neighbourhood components with rg.
   No exact zero-slice result was found. The hole needs substantial geometric pullback
   comparisons and cannot be closed by a short application of the results found.
4. **Route and pruning: PASS.** Read the proof top downward, the old dependencies, and the
   unit's local-calculation step. The preparation uses Mathlib's integral-morphism
   toNormalization isomorphism and smooth normalization base change, without a needless
   normality argument. The categorical assembly implements preimageIso's argument while
   converting the actual finite-etale objects to scheme maps and including an isomorphic
   base alternative. Its existing correct proof was retained. The main proof retains the
   prescribed rational-point/G-action slice argument and Tag 0EY9 lifting route. All proof
   imports are plain imports, and new public imports supply signature/instance vocabulary.
   Every removed old proof dependency is now explicitly named under No longer needed; both
   moved nodes remain transitively needed, so no module is claimed globally pruned.
   The repository unit's realized lists are already empty; this delivery changes neither
   those lists nor the unit route and makes no claim to repair that existing bookkeeping.
5. **DAG: PASS.** All four lean.statement records match the signatures literally. Each
   proof_deps equals the union of its proof steps' uses. The main node records preparation,
   slice splitting, and assembly with the d=0/positive-d alternatives. The preparation and
   assembly nodes describe their proved implementations. The slice node describes the
   sourced remaining argument and lists its normalization, action, and generic-point
   dependencies. New nodes have sources, origin, search records, creation data, blueprint
   provenance, chapter/unit, and Lean records. No unrecorded interface adaptation occurs.

Second-reading changes: corrected the main and slice proof docstrings to justify relative
normalization agreement by finite/integral morphisms and smooth open base change; removed
one extra blank line; explicitly named both moved old dependency nodes in the pruning
report; added this independent review. No proof or signature was rewritten. The net hole
change is zero (one closed, one added); this remains a decomposition.
