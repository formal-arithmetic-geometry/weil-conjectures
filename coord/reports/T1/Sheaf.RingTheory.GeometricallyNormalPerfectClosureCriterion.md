## What changed

Replaced the sole `sorry` in
`Sheaf.RingTheory.GeometricallyNormalPerfectClosureCriterion` with a complete Lean proof of
`Algebra.normal_tensor_perfectClosure_iff`, keeping its exact signature and visibility.
The proof follows Stacks Algebra, Tag 037Z (`lemma-geometrically-normal`): embed the finite
purely inseparable base extension into P, use the stated make-separable theorem, present the
separable finitely generated extension as a smooth algebra's fraction field, ascend normality
through smooth base change, localize, and descend along the larger scalar field.

Private proved helpers implement transport of prime-localization normality across ring
isomorphisms, localization, the tensor cancellation in field descent, and the finitely
generated case. The final helper constructs the filtered diagram indexed by finite subsets
of E. Tensor induction proves that its cocone maps jointly cover E tensor_k A; flatness of
the k-vector space A makes each map injective. The filtered-colimit criterion proves that
this cocone is a colimit, so the existing normality theorem applies. The reverse implication
uses an explicit ULift and its tensor equivalence to respect all four original universes.

Added proof-only Mathlib imports for ring filtered colimits, field ULift, finitely generated
intermediate fields, flat tensor maps, and tensor algebra equivalences. No public import,
definition, or existing signature changed. Updated the existing node's proof and proof origin
to describe these constructions. No other library module was adapted.

## Proved and sorry left

Closed 1 existing hole: `Algebra.normal_tensor_perfectClosure_iff`
(node `lem-weil-pbc-geometrically-normal-perfect-closure-criterion`).
There are 0 remaining holes in the item, 0 added holes, and 0 split-offs.
All six private helpers are proved. The proof deliberately uses the existing declared
normality-descent theorem; its pre-existing hole is outside this delivery and is not claimed
as closed. This is a proof from the stated dependencies, not a decomposition into new holes.

## No longer needed

None: every original proof-dependency module is used, and no original import was removed.
No node or module is pruned. The smooth, localization, make-separable, descent and filtered
colimit steps of the planned proof are all retained.

## Where the brief, the DAG or earlier work was wrong

No statement repair is needed. The forward argument actually works for any perfect overfield
P of k: each purely inseparable base extension embeds uniquely into P. Thus the original
`hpower` hypothesis is unnecessary for this proof; it has been retained unchanged. Mathlib
already supplies these embeddings, so the explicit Frobenius-root construction in the DAG
is replaced by that API. The tensor-colimit identification is checked using representatives
and injectivity, rather than constructing a universal ring map by hand. Both are the same
source argument. The zero algebra is covered uniformly: none of the helpers assumes it is
nonzero, and all conclusions remain the original prime-localization conditions.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
