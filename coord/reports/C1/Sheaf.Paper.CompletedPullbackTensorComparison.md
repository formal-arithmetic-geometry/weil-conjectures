## What changed

Proved `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique` by constructing
an isomorphism at the compositum of the input coefficient stages, transporting it to
the fixed functor objects, using the existing representative-enlargement theorem at
every larger stage, and applying hom and isomorphism extensionality for uniqueness.

The new `CompletedPullbackTensorNaturality` module proves
`WeilConjectures.canonicalRationalPullbackTensor_naturality`. It composes the actual
coherent counit and integral operation realization isomorphisms, checks its components
against the prescribed integral comparison, then applies the existing bilinear scalar
localization theorem. The common-stage proof uses this natural family and the existing
rational scalar square to instantiate `restrictionTensorRepresentativeTransport`.

Extracted the existing finite/integral/rational/scalar construction layer verbatim to
`CompletedPullbackTensorConstruction`, publicly reexported by the original module.
All 32 existing public signatures are byte-identical to the shared source.
All existing definition bodies stay identical; the original private
sequence-ring equality remains available for import-all consumers. Updated both
existing DAG attachments affected by the extraction. No consumer source is changed.

Change record: `coord/changes/C1-completed-pullback-tensor-common-stage.md`.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`
(node `def-pur-completed-pullback-tensor-comparison`).

The one original hole left is
`WeilConjectures.canonicalIntegralPullbackTensor_scalar`, moved without changing its
statement or proof to `CompletedPullbackTensorConstruction`
(node `def-pur-completed-pullback-tensor-construction`). No new sorry statement is
introduced and no hole is split off. The rational naturality theorem and all private
helpers added here are fully proved. The common-stage proof imports the existing
named representative-enlargement and bilinear-localization lemmas; their existing
proof obligations are dependencies, not newly introduced statements.

## No longer needed

None. Existing proof imports move with the construction layer; no mathematical
module or node is withdrawn. The proof uses the existing representative-enlargement
lemma rather than introducing a duplicate common-stage descent obligation.

## Where the brief, the DAG or earlier work was wrong

The current source has two holes, matching the current queue row. No statement was
found false and no target or definition is weakened. The existing constructions were
sufficient, but the canonical rational components needed a naturality proof before
they could instantiate the generic representative-enlargement theorem. The new lemma
supplies this proof with no new obligation. The original DAG's mathematical statement
is unchanged; its proof and Lean attachments now describe the actual implementation.

The unit's `realized` lists impose no additional step on this node, and the prescribed
integral, rational and common-stage coefficient route is retained. The naturality
argument applies to zero objects and identity morphisms by functoriality; the
enlargement theorem includes the identity extension L=H. No flatness of a ramified
quotient is assumed.

## New nodes

`def-pur-completed-pullback-tensor-construction` attaches the existing finite,
integral, rational and scalar declarations to their extracted module, preserving
all old proof steps and the sole existing integral scalar hole. It creates no
new comparison or new choice.

`lem-pur-canonical-rational-pullback-tensor-naturality` records the fully proved
naturality of the prescribed rational comparison, from the coherent counit
construction and bilinear scalar localization. Searches with leanfinder, loogle,
grep, and local source searches found generic extensionality/localization tools and
the existing representative transport theorem, but no already stated naturality
lemma for these exact canonical components.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
