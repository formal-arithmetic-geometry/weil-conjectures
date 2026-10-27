## What changed

Filled `WeilConjectures.IntegralSystemRealization.integralOpenMateNormalization`
in `Sheaf.SixFunctors.IntegralOpenMateNormalization`, preserving its exact signature,
public imports and definitions. Added the private proof import
`Sheaf.SixFunctors.OpenReconstructionEffectivity`.

The existing `Good` input supplies one ordered Tor interval for every evaluated
positive coefficient level. Transporting representative isomorphisms through the
inverse `calculus.reductionEvaluation` identifies these levels with the actual
finite reductions of K, proving `finiteTorConstructibleIntegral K` together with hK.
The existing proved `GeneratorReduction.openReconstructionEffectivity`, applied to
the original o, m, j and K, then gives exactly the required pair in reverse order.
The node proof and proof dependencies now describe this route.

The first server compile checked the complete proof in 2.9 seconds; its only
warnings identified hX, hY and hj as unused. The final proof explicitly records
these domain hypotheses without changing their binders. The import-direction
check permits the added proof import, and a source comparison checks that the
theorem signature is verbatim unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.IntegralSystemRealization.integralOpenMateNormalization`
(node `lem-sf-integral-open-mate-normalization`).

Added 0 holes and 0 split statements. There are no textual sorries left in the item
or added elsewhere. This uses existing library declarations and does not claim
that all of their transitive dependencies are already free of sorry.

## No longer needed

No pre-existing import was removed and no module is withdrawn.
The direct proof dependency `lem-sf-integral-open-reduction-comparison`
(`Sheaf.SixFunctors.IntegralOpenReductionComparison`) is no longer needed by this
proof: the established effectivity theorem already proves the two specified map
properties. It remains an unchanged statement dependency in the node and may be
used by other consumers; no claim of global withdrawal is made.
The canonical bridge and reduction-evaluation calculus are still needed. The
existing public bridge import remains verbatim. No unit step is bypassed: both
routes establish the same primitive coefficient/open-adjunction normalization
inside `sk-thm-sf-compatibility`.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original planned adjoint-uniqueness transport
is unnecessary now that the existing proved effectivity theorem handles exactly
the specified realization model and its actual reconstruction unit. The original
docstring records that longer plan; the updated node records the Lean proof.
The hypotheses hX, hY and hj remain verbatim but are unnecessary for this stronger
existing theorem. The common Tor interval in hg is used with no restriction on
its endpoints, and the effectivity theorem explicitly includes the identity and
empty open immersions.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
