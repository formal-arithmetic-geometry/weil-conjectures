## What changed

Added the proof of `GaloisCover.stalk_normalization_trait_flat`. The proof imports the
standard tame-chart reduction and the existing fpqc flatness descent theorem. It proves
flatness of each chart by `Polynomial.Monic.free_adjoinRoot`, the finite Pi free-module
instance, and `RingHom.flat_algebraMap_iff`. Added the intermediate chart theorem module
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts`.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_flat`
now has a complete reduction proof. Added one hole: the new intermediate declaration `GaloisCover.stalk_normalization_trait_charts` remains `sorry`;
it is recorded as node `lem-sbc-stalk-normalization-trait-charts`.
This is a decomposition (one hole closed, one added; net zero), not an axiom-free proof
of the target. The algebraic flatness and descent steps are fully proved.

## No longer needed

No imports or nodes from the original module were removed. The proof uses only the chart
node, `lem-weil-pbc-monic-quotient-free` through Mathlib's `Polynomial.Monic.free_adjoinRoot`,
and `lem-weil-pbc-fpqc-descend-flat` through `Sheaf.AlgebraicGeometry.FlatOfFpqcCover`.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan omitted the concrete chart interface required to connect the
Stacks tame-normalization argument to the Lean `fromNormalization` pullback. This delivery
states that geometric step separately; it does not repeat the flatness conclusion.
The second reader corrected the chart proof references: 0307 is localization of integral
closure, and 03GE/03GV give etale base change; 0ABP does not state localization.

## New nodes

`lem-sbc-stalk-normalization-trait-charts` is the chart theorem described above and is
implemented by `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts`.

## Earlier second reading (a previous round; superseded)

The delivered modules compile together. The target statement is unchanged; the chart theorem is a strict intermediate result used to establish flatness. The unit route remains the trait tame-normalization route.

## Second reading by X3

1. Interface: PASS. Read the complete diff against the repository. The original declaration
   `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_flat` has a byte-identical
   signature. Its only Lean changes are three plain proof imports and the proof body. There
   are no changed definitions, target interfaces, or forced adaptations. The chart theorem
   is new and constructs no data from its unproved existence assertion in a definition.
2. Proof: PASS as a decomposition. Both modules compile with lcompile.py. Scratch-copy
   `#print axioms` checks show only propext, Classical.choice, Quot.sound, and sorryAx for
   the chart theorem and the reduced flatness theorem. The descent theorem and monic
   AdjoinRoot freeness have only the three standard axioms. The only explicit sorry in
   the delivery is the whole proof of the public named chart theorem. No forbidden
   constructs or hollow definitions occur. The algebraic proof handles any finite
   number of factors, including zero, and transports flatness using the over-base
   isomorphism equation before descending along the etale family.
3. Split statement: PASS. Read Stacks 0EYJ's trait paragraph, 0EYG, 0EYH, 09EB, 0307,
   03GE, and 03GV. The chart conclusion is their geometric local-form step, with the
   normalization comparison over the affine base; it does not assert flatness. Small
   cases checked: an empty family covers an empty local total space; an empty cover
   is an empty product (zero ring); off the divisor the cover splits with e=1,f=1;
   disconnected torsors use stabilizer subgroups, and ramification indices and residue
   degrees divide their orders. Repeated searches with different queries via leanfinder,
   loogle, and grep found ramification algebra and monic freeness, but no matching chart
   existence result. Read the related library statements: the section-dependent etale
   extension and chart results impose extra hypotheses and cannot supply this theorem.
   The remaining geometric step is not formalizable in a few minutes from available
   declarations. Its docstring supplies the argument and its node records the statement.
4. Route and pruning: PASS. The complete algebraic part uses Mathlib directly, followed
   by the already proved fpqc descent theorem. Only the geometric tame local-form step
   remains open. Each added proof import is used; the chart's AdjoinRoot import is public
   because its signature uses that type. Original public imports supply statement notions
   and are retained. The original node had empty proof_deps, so there are no obsolete
   dependencies to report. The unit sk-prop-input-spreading explicitly calls for standard
   tame forms in its trait step, and this reduction retains that route. Its realized
   fields are empty in the base and are not changed by this delivery.
5. Records: PASS after repair. Both recorded Lean statements match the modules verbatim,
   and proof_deps is exactly the union of the proof steps' uses. The existing node records
   the chart, monic-freeness, and flat-descent steps. The new node has its source, searches,
   creation and blueprint records, chapter, unit, and Lean record. Its natural-language
   statement now spells out all hypotheses instead of referring to the parent statement.

Second-reading changes: corrected chart-proof references (0307 for localization,
03GE/03GV for etale base change); made the residue-separability argument explicit;
made the new DAG statement self-contained and recorded the independent searches;
corrected the DAG step order (transport before descent); and corrected the report to
count one hole closed and one added, net zero. No Lean signature or proof body changed.

Source checks: [tame local normalization](https://stacks.math.columbia.edu/tag/0EYH),
[localization](https://stacks.math.columbia.edu/tag/0307),
[etale integral closure](https://stacks.math.columbia.edu/tag/03GE), and
[scheme normalization base change](https://stacks.math.columbia.edu/tag/03GV).
