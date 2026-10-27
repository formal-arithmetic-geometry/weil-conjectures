## What changed

Proved `WeilConjectures.CommonStageFiniteHomLifting.finiteHomLifting` with its
existing signature and all seven clauses. Added proved private helpers for the
representative formula, compatibility with transport, finite common upper fields,
representative enlargement, and composition of transports. The finite-family
argument explicitly handles an empty family and prescribed extra coefficient fields.

Added the proof-only import
`Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility`. Its uniquely specified
coherent pullback family has precisely the rational functors and comparison
components needed here. Applying upstream `StageSystem.Morphism.tr_mapAt` replaces
repeating its coefficient-coherence construction. Only its coherent left family is
used; no adjunction or right-mate conclusion is used. This is a coefficient tool
from `sk-def-sf-operations`, a unit already used by `sk-def-purity-conv`; the
maintainer may record the corresponding tool approval. No target, public
construction, universe or hypothesis changes. Updated the node proof route.

## Proved and sorry left

Closed one hole:
`WeilConjectures.CommonStageFiniteHomLifting.finiteHomLifting`
(node `lem-pur-common-stage-finite-hom-lifting`).

Added zero holes. No `sorry` remains in the delivered module. The proof uses
existing declared dependencies whose own proofs remain separate project items;
this is a proof from those declarations, not an axiom-free closure claim.

Validation: the complete proof compiled without warnings through `lcompile.py`
(including runs of 55.5 and 59.2 seconds). An initial delivery compile timed out
and pushed nothing; continued performance work preserves the proof and the fixed
limit. All four existing declaration signatures and the three public definition
bodies were compared with the shared source and are unchanged. The source contains
zero `sorry` tokens and every line is at most 100 characters. Delivery preflight
checks the final packet again.

## No longer needed

The node no longer directly needs to reconstruct rational scalar naturality and
the tower calculation from `lem-pur-integral-operations-scalar-extension`,
`lem-weil-scalar-extension-composition`, and `def-weil-rationalization-karoubi`.
Withdrew their two obsolete direct tool approvals in the node.
Their required coherence is encapsulated by the existing
`lem-sf-rational-direct-image-coefficient-compatibility`; they remain dependencies
of that tool and of the operation definitions, so no module is withdrawn or
claimed globally pruned. Removed six redundant direct public imports, each still publicly reexported by
`PurityFiniteSetting` or `DerivedPullbackTensorHom`:
`Mathlib.AlgebraicGeometry.Sites.Proetale`,
`Sheaf.Paper.SfRationalizationKaroubi`,
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
`Sheaf.NumberTheory.Padics.FiniteCoefficientFields`,
`Sheaf.Paper.IntegralOperationsScalarComparisons`, and
`Sheaf.Paper.SfScalarExtensionComposition`.
Thus the importer-visible dependency interface is preserved. No module becomes
unreachable just from removing these duplicate edges.

No blueprint unit statement or realized step is bypassed. No new nodes.

## Where the brief, the DAG or earlier work was wrong

The original plan repeats coefficient coherence already exposed as a uniquely
normalized coherent stage family by
`sfRationalDirectImageCoefficientCompatibility`. The shorter route uses exactly
that existing normalization. The theorem statement is unchanged and no false
statement was found. The listed quarantine row predates the currently restored
source; the delivery starts from that present source and preserves its attachment.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
