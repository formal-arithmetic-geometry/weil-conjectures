## What changed

Repaired the false arbitrary-q split in
Sheaf.Paper.ScalarPullbackRightRoosNormalization by requiring the existing
ScalarPullbackQuotientFormula. The sole caller,
Sheaf.Paper.ScalarPullbackRightRoos, passes its existing hq; its signature stays
identical. The right-route node's proof is updated accordingly. The caller was
unclaimed on the server when checked.

The item chooses a good representative R of the pulled object, obtains its
coherent presentation D, and applies SX.normalization. Finite evaluations prove
D K-flat, hence its scalar counit is invertible. Scalar-completion normalization
then identifies the scalar-model route with the ordinary completion augmentation
and the inverse of the explicit Roos presentation isomorphism. Naturality moves
this equation along eR, and cancellation of scalarCompletionIso on the complete
pulled object proves the corrected equation from scalarPullbackCompletionRoos.

The remaining named theorem is a quotient/Roos augmentation equation. Its inputs
contain no SX, no scalar realization, no completion inverse, no constructibility
or derived completeness, and no geometric invertibility assumptions. It is the
strict quotient calculation after model normalization, not the original statement
with a new name. The item's proof performs that model normalization and the
completion cancellation in Lean.

Validation: all three sandbox modules compile cleanly in import order through
lcompile.py. The normalization theorem compiled in 35 seconds; the lower module
and caller also stayed below 60 seconds. The direct-importer scan finds only
Sheaf.Paper.ScalarPullbackRightRoos, and no other source mentions the changed
normalization name. The metadata statement-change check passes with its sole
citer accounted for. The original caller was also compiled against the repaired
signature: it fails because hF is supplied where ScalarPullbackQuotientFormula
is expected. The delivered caller passes its existing hq at that argument.

## Proved and sorry left

Original holes proved without a statement change: 0 of 1. The original statement
was false and is explicitly repaired; it is not counted as proved.

The corrected WeilConjectures.ScalarExtensionTower.scalarPullbackRightRoos_normalized
has a complete combining proof. Its former textual hole is removed by a
decomposition, not a net proof: one hole closed syntactically, one new hole added,
net zero. There are zero holes in the delivered item itself.

One sorry remains in the delivery:
WeilConjectures.ScalarExtensionTower.scalarPullbackCompletionRoos, node
lem-pur-scalar-pullback-completion-roos, in the new module
Sheaf.Paper.ScalarPullbackCompletionRoos. Its proof is exactly by sorry and its
docstring and node give the augmentation/quotient argument in full.

No axiom or sorry is added to a definition. The caller remains sorry-free.

## No longer needed

No original imports were removed and no modules were withdrawn. The direct use
of lem-pc-kflat-resolution from the old node plan is unnecessary: the existing
good-complex localization supplies the representative, and
coherentPrimitiveReductionPresentation supplies its coherent quotient system.
K-flat resolutions remain used transitively by that existing localization; they
are not claimed to be removed from the target closure.

The independent lower calculation uses the stated sequence-system and ordinary
scalar/pullback tower maps. The item's new proof uses those constructions through
that lower lemma; no additional unused dependency module is imported.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old normalization equation allowed arbitrary q while its
left side depends linearly on q and its right side does not. Postcomposing q with
negation changes only the left side. Identity pullback and coefficient embedding
on a nonempty geometric point, with a nonzero completed rank-one object, give the
incompatible two signs. The parent statement already includes hq. Restoring it
repairs an invalid split rather than weakening a genuine source statement.

The sole DAG citer, stage3-pur-scalar-pullback-right-roos, still holds: it already
assumes precisely the tensor-unit formula now passed to the repaired lemma. The
statement_change records the exact old statement and that audit. No target or
unit statement is changed.

The source places were read locally: sites-cohomology.tex, derived tensor product,
derived pullback/tensor compatibility, and lemma-derived-limit-is-ok; and
sites-modules.tex, lemma-tensor-product-pullback. The project-specific quotient
calculation is explicitly recorded as an agent expansion of these arguments.

## New nodes

lem-pur-scalar-pullback-completion-roos records the remaining compatibility of the
scalar completion augmentation with the pulled coherent quotient tower. It has
its own new module, one theorem, the exact Lean statement, source and detailed
proof, and actual leansearch, leanfinder and grep searches. The edge cases checked
are zero complexes, empty sites, identity maps and coefficient embeddings, the
first quotient n=0, and ramified embeddings; none requires finite quotient scalar
extension to be flat. The source-side scalar realization model has been eliminated
from this obligation.

Change record: coord/changes/A5-scalar-pullback-right-normalization.md.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ScalarPullbackCompletionRoos": "149a21f91ebc5910381cebbe4cab0661f16dff7d", "Sheaf.Paper.ScalarPullbackRightRoos": "d7d04cbf95c68adbc66ee43c28988cade7a606af", "Sheaf.Paper.ScalarPullbackRightRoosNormalization": "316d36ea6ba547f9c2cbc8528a701919e32a1ba0"}, "results": {}, "time": "2026-10-28T10:30:11+0800", "transitive": 0, "version": 1}
```

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
