## What changed

Proved `WeilConjectures.pullbackTensorSequenceCochain_existsUnique` by applying a
proved general unit-normalized unbounded cochain tensor comparison to the existing
ordinary site-pullback tensor data. Representable flatness of the sequence base
is proved using the product equivalence of structured-arrow categories.

Proved `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique` by assembling
the full natural representative comparison and applying the existing normalized
descent theorem to the product good localization. Its components are exactly the
recorded strict-tower/Roos comparison; no finite-projection detection argument is
used. The evaluation tensor naturality calculation is a proved helper.

Extracted the already proved pullback-tower naturality calculation into a proof-only
helper module. The private componentwise K-flat detection proof and transport of
tensor-level naturality are checked in the new comparison helper as well. Existing public statements, definitions and public imports of the
item remain unchanged. The helper modules isolate reusable calculations and keep
compilation within the per-file limit after closing large tensor definitions
behind their generator API.

## Proved and sorry left

Three holes were present in the live item after the preceding M3 delivery.
Closed two, with no new holes:

- `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`
  (`lem-pur-sequence-pullback-tensor-cochain`).
- `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique`
  (`lem-pur-integral-tensor-roos-realization`).

The remaining hole is unchanged:

- `WeilConjectures.pullbackTensorTensorTower_existsUnique`
  (`lem-pur-coherent-tensor-tower`). Its outstanding step is compatibility of
  the prescribed tensor-level components with the actual completed-scalar
  quotient transitions, before assembling the tower isomorphism.

All six new helper modules have complete proofs and zero `sorry`. The
previously proved reduction-good, sequence-good, system-comparison and pullback
model results are retained; they are not counted as newly closed holes.

## No longer needed

Removed the item’s proof import of `Sheaf.Paper.SemilinearDerivedSections`: its
only remaining direct use was the private K-flat detection proof, now checked in
`CoherentTensorRoosComparison`, which imports it. The library still needs that
module there.

For the cochain proof, the separate use of
`lem-sfb-left-resolution-map-total-iso` and
`lem-weil-pbc-left-adjoint-preserves-colimits` is unnecessary: the existing
`tensorPullbackTotal`/`tensorPullbackTotal_isIso` API already totalizes the ordinary
comparison and uses the adjunction to preserve its diagonal coproducts. Removed
`lem-sfb-left-resolution-map-total-iso` from this node's `tool_uses` approval list.
The generic theorem also proves the generator normalization and uniqueness, so
the original six-step specialized argument is replaced by its application.
The direct cochain proof citations to `def-pur-sheaf-tensor-product`,
`def-weil-pbc-category-colimit`, `def-weil-pbc-module-tensor-product`, and
`def-weil-presheaf-modules-sheafification` are likewise subsumed by that generic
comparison and the pure-generator API it uses.

For the integral tensor realization, no separate resolving-representative
whiskering, K-flat resolution, multiplicative-system or localization-universal
property proof is needed. The already recorded `integralCompletedTensorDescent`
universal property and `normalizedDescentComponents_existsUnique` give precisely
the full normalized comparison. Removed the direct proof dependencies
`lem-weil-pbc-resolving-representative-whiskering`,
`lem-pc-kflat-resolution`, `lem-pc-quasi-isomorphisms-multiplicative-system`,
`def-weil-abstract-derived-category`, and
`lem-weil-pbc-localization-universal-property` from this node; removed the first
two from its `tool_uses` list. Its old separate `lem-pur-integral-operations-well-defined` citation is subsumed
by the recorded descent API. The exact-derived-factorization dependency remains in the new natural
representative constructor, which explicitly uses that factorization. These results remain in the library wherever other
consumers need them; no existing module is withdrawn.

No existing public import is removed. No blueprint unit statement or realized
unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The live item had three holes, rather than the six of the earlier version: M3 had
already closed the other three. This delivery starts from that live source and
preserves those proofs.

No mathematical statement was found false, and no definition or target statement
was changed. The old tensor realization plan used a more general localization
argument than the existing normalized descent API requires.

## New nodes

`lem-pur-unit-normalized-cochain-tensor`, in
`Sheaf.Paper.UnitNormalizedCochainTensor`: a proved general comparison and
uniqueness theorem for arbitrary unbounded complexes, with the actual adjunction
unit normalization. The proof totalizes the ordinary data and checks uniqueness
by transposing degree maps and testing pure tensor generators.

`lem-coef-evaluation-total-tensor-naturality`, in
`Sheaf.Paper.CoefficientEvaluationTensorNaturality`: a proved naturality square
for the prescribed evaluation comparison, obtained from its generator equation
and tensor-map functoriality.

`def-pur-finite-tensor-reduction-comparison`, in
`Sheaf.Paper.FiniteTensorReductionComparison`: tensor the two inverse normalized
reduction evaluations and restrict scalars, with the actual finite tensor-level
functor as target. This real construction is factored out to avoid repeating
its large definitional type conversion.

`def-pur-natural-coherent-tensor-level`, in
`Sheaf.Paper.NaturalCoherentTensorLevel`: the real natural isomorphism obtained by
composing reordering, normalized evaluation and inverse reduction evaluations. Its
explicit concrete source and target tower-evaluation functors prevent repeated unfolding of the total tensor
inside the tower-naturality proof; the main proof uses its naturality and component
equation. This construction adds no `sorry` and changes no existing definition.

`def-pur-coherent-tensor-roos-comparison`, in
`Sheaf.Paper.CoherentTensorRoosComparison`: a real natural representative
comparison from the K-flat preservation proof and the strict tower comparison.
Its proved component API gives exactly the prescribed full Roos model and avoids
repeated checking of the composite inside the item.

`lem-pur-strict-pullback-tower-naturality`, in
`Sheaf.Paper.CompletedPullbackTowerNaturality`: the existing proved component
naturality calculation, extracted from the item. It retains the chosen strict
tower components and actual finite-pullback functor.

No change record is needed: all existing public statements, definitions and
public imports are unchanged.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
