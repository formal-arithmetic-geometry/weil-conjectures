## What changed

The target theorem now combines two named intermediate statements.

## Proved and sorry left

`higherDirectImageRawOverPullback_toSheaf` is proved from
`higherDirectImageRawOverPullback_comparison` and
`higherDirectImageRawOverPullback_restriction`. Those two intermediate declarations remain `sorry` and have DAG nodes. The imported
`higherDirectImageRawTransition_toHom` and `higherDirectImageRawTrianglePullback_restriction`
remain `sorry` in their dependency modules and are existing proof dependencies.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The earlier direct proof exceeded the compiler time limit while unfolding the derived
comparison. Decomposing the argument into its two mathematical components makes the
main theorem compile.

## New nodes

`sbc-lem-higher-image-raw-over-comparison`, `sbc-lem-higher-image-raw-over-restriction`,
`sbc-lem-higher-image-raw-transition-to-hom`, and `sbc-lem-higher-image-raw-triangle-restriction`.

## Earlier second reading (a previous round; superseded)

The top-level theorem has the exact target signature and combines the two strictly
smaller components. The intermediate statements retain the required comparison and
restriction clauses without changing the target.

## Second reading by E2

1. Compared the target module with the repository version. Existing declarations and definitions retain their signatures; only a redundant import was removed and a proof-only import was added. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py`; all compile successfully. Remaining `sorry`s are named split-off declarations. Verdict: pass.

3. Checked both split-off statements and their DAG nodes as strict components of the conjunction, with source explanations and no hollow definitions. Verdict: pass.

4. The target proof uses both component declarations directly; transition and triangle modules are required proof dependencies. No additional pruning was found. Verdict: pass.

5. DAG proof dependencies and origins match the imports and proof route, and the unit's realized route remains comparison followed by restriction. Verdict: pass.

The comparison node prose was corrected to describe the evaluated section equality of its Lean declaration rather than an unevaluated morphism equality.
