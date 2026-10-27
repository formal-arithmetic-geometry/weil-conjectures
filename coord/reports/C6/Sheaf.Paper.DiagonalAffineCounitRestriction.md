## What changed

Reduced diagonalAffineCounitRestriction to two independent geometric steps:
DNC orientation naturality under an etale correspondence, and normalization of
that orientation on the ordered affine projection. The combining proof constructs
an affine chart, restricts the coordinate correspondence to the common target
open, substitutes model normalization, and cancels site-comparison isomorphisms
using naturality. It keeps the original theorem statement.

Moved the four OrientationCounit constructions verbatim to a publicly reexported
data module to avoid cycles. Added the open-square comparison restrictionAlong
and the explicit localInverse isomorphism. See
coord/changes/C6-diagonal-counit-comparison-data.md.

Validation: all three dependency modules compiled remotely. The assigned theorem
then compiled cleanly in 7.9 seconds with the final proof and without diagnostic
options. Source checks confirm the original theorem statement and the four moved
definition signatures/bodies are verbatim. The overlay DAG has no cycle through
any affected node.

## Proved and sorry left

Original hole closed by decomposition:
WeilConjectures.PurityFiniteSetting.diagonalAffineCounitRestriction.

Two new holes, each exactly a named theorem with source and proof in words:
- WeilConjectures.PurityFiniteSetting.diagonalDncEtaleNaturality.
- WeilConjectures.PurityFiniteSetting.diagonalDncAffineModel.

Original module: 1 hole before, 0 after. New modules: 2 theorem holes, no data holes.
This is a decomposition, not a net hole reduction (closed 1, added 2).

## No longer needed

No existing module or node is withdrawn. No original public import is removed.
The original geometric proof dependencies are used by the two new steps rather
than directly by the combining proof; they remain needed transitively. The parent
node now names only the two geometric steps, the data node and chart existence.
The downstream DiagonalDncChartNormalization/ChartDncVectorFactors cannot be
imported here: they reach this theorem through the global diagonal orientation.

## Where the brief, the DAG or earlier work was wrong

The old proof plan combined two substantial geometric comparisons in its final
calculation. Its declared dependencies do not directly state either the source
etale correspondence law for the four-factor composite or its affine model
normalization. The new lemmas isolate these separately rather than restating the
entire counit restriction under another name. The naturality lemma has no counit
or P1 datum; the model lemma has no arbitrary smooth morphism or etale chart.

Small cases checked in the mathematical statements: d=0 uses empty frames and
identity adjunctions; empty opens use the unique maps between zero objects.
Neither lemma requires nonempty schemes, a chosen frame, or global orientation.

## New nodes

- def-pur-diagonal-counit-comparison-data: actual structural maps, no hole.
- lem-pur-diagonal-dnc-etale-naturality: the etale correspondence compatibility.
- lem-pur-diagonal-dnc-affine-model: affine-projection normalization.

The model step uses lem-trf-ambient-affine-translation-trace as a generic trace
invariance tool, exactly for the change (x,y) to (x,y-x). It does not replace a
unit route. Its declaration ambientAffineTranslationTrace is proved and was read.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
