## What changed

Restored the assigned quarantined module with its statement and public import unchanged.
Constructed the left comparison by localizing the inverse ordinary mate and the right
comparison as its derived mate. Proved four private formal lemmas: identification of the two cochain units,
the cochain mate normalization, its arbitrary-resolution consequence, and
componentwise invertibility from acyclicity. These yield both required mate equations by the categorical mates API.
Added a proved specialization of sequenceModulePullbackEvaluation_isIso and a strictly
smaller acyclicity statement for evaluated K-injective systems.

## Proved and sorry left

Original holes: one, WeilConjectures.compactSupportDirectImageDerivedEvaluation.
Its proof now contains no sorry. Added one hole:
WeilConjectures.compactSupportEvaluationDirectImage_acyclic, node
lem-trf-compact-support-evaluation-direct-image-acyclic. This is a decomposition
(one upper hole closed, one lower hole added; net zero), not a complete proof.
WeilConjectures.compactSupportEvaluationOrdinaryMate_isIso is proved without sorry.
The acyclicity lemma specifies only invertibility of one right-derived unit on
K-injective inputs. It contains neither a natural comparison, an arbitrary-resolution
formula, nor the left comparison or the two mate equations; the main proof supplies
all those constructions and identities.

## No longer needed

No original imports or declared dependencies are removed. The original definition
module remains required. The finite-prefix construction is needed only for acyclicity;
the ordinary inverse-image comparison and all formal derived normalization are
handled by proved library results. No quarantined dependency is withdrawn, and no
source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omits the needed acyclicity argument: invertibility of
an ordinary square's inverse mate does not by itself make its derived direct-image
mate invertible. The remaining lemma records that precise missing condition, without
assuming evaluation preserves K-injectives.

At session start the required public definition module
CompactSupportSystemEvaluationDiagram was quarantined and absent from lean/.
It was restored in the shared repository during this session; the delivery source
check now passes. No dependency restoration or withdrawal is part of this packet.

## New nodes

lem-trf-compact-support-evaluation-ordinary-mate: a proved specialization of the
existing sequence-module pullback evaluation theorem.

lem-trf-compact-support-evaluation-direct-image-acyclic: finite direct-image
acyclicity of the evaluation of a K-injective system, using derived finite left
extension and the inverse-image tensor comparison. This is the only new hole.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
