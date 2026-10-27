## What changed

Replaced the hole in `WeilConjectures.projectionIdentity_properCounit` by a common
categorical argument for all four coefficient regimes. Its statement and its two
public imports are unchanged. Two proof imports supply the separate tensor-unit
and finite counit-transpose obligations.

The proved private categorical calculation first identifies
`e_(R M) ≫ d_M` with the supplied counit, using Mathlib's right-adjoint uniqueness
counit identity. It then precomposes by the invertible identity-unit component,
uses naturality to introduce the projection transpose, substitutes the tensor-unit
equation, and combines the two maps in the first tensor variable by functoriality.
The same calculation works for a partial tensor with a different second category.
A generic stage helper specializes this calculation before the coefficient-stage
categories are substituted, avoiding repeated expensive elaboration. Local
opacity for the finite partial tensor, proper component and new comparison keeps
their implementations closed during this proof; no exported attribute changes.
At the three higher stages the normalization to the generic counit projection is
proved by eliminating the recorded functor equalities and adjunction HEq.

Added `FinitePartialPullbackTensor`, which constructs the actual finite partial
tensor/pullback isomorphism from the published fixed-scalar comparison and the
specified realization maps. It cancels the coefficient-equivalence units explicitly
and lifts through the full bounded constructible inclusion. This definition uses
no existence choice and contains no hole.

Added `FiniteProperProjectionTranspose` and `ProjectionIdentityTensorUnit` for the
two uncompleted steps. The former applies to arbitrary proper maps, independently
of identity-unit normalization. The latter involves inverse image and tensor only,
with no direct image, projection, or counit in its conclusion. The item combines
them in Lean; neither lemma restates its conclusion.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.projectionIdentity_properCounit`
(node `lem-sf-projection-identity-proper-counit`). No hole remains in the item.

Added two holes:

- `WeilConjectures.CompactSupportFiniteProjection.properComponent_transpose`
  (`lem-sf-finite-proper-projection-transpose`). This identifies the finite
  projection's actual counit transpose in the specified realization coordinates.
- `WeilConjectures.projectionIdentity_tensorUnit`
  (`lem-sf-projection-identity-tensor-unit`). This proves compatibility of the
  normalized identity unit with the specified tensor comparison at each stage.

This is a decomposition: one original hole closed, two lower holes added. It is
not a complete axiom-free proof of the original obligation. The new comparison
construction and the categorical combination of these two obligations are proved.
All four modules compile through `lcompile.py`. The final item compiles cleanly
in 35.4 seconds with the profiler removed. The three new modules passed the
sandbox compile in import order. The item's original theorem signature was
compared textually with the repository version and is identical. Exactly the two
named split theorems contain `sorry`; the new definition contains none.

## No longer needed

No existing public import or library module was removed, and no whole module is
claimed to have left the targets' closure. In the item's direct proof plan,
`fix-prop-adjunctions` and its source module
`WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` are unnecessary: the supplied
adjunctions already contain the counits and Mathlib provides the required
right-adjoint uniqueness identity. The derived tensor-comparison dependency
`lem-pur-derived-pullback-tensor-iso` remains needed below the tensor-unit lemma,
rather than being a direct input to the final assembly.

The existing fixed-scalar `FiniteProjectionIdentityNormalization` and system-model
`ProjectionSystemCoherence` are not imported. Their identity statements are on
different presentations and do not directly give the normalized constructible
partial tensor equation. The new finite comparison retains the full first-input
domain and restricts only the second input to finite Tor.

## Where the brief, the DAG or earlier work was wrong

No statement correction, definition repair, withdrawal, or consumer adaptation was
needed. The original two-step plan hid a separate finite realization normalization:
`properComponent` is a conjugated compactification projection, whereas the higher
proper projection is explicitly a supplied adjunction mate. That finite
identification is now an independently stated proper-map lemma. The unit's route
and all target statements are preserved.

The new statements were checked on the empty scheme, zero inputs, n = 1, and an
arbitrary non-finite-Tor first input. The finite transpose is just the defining
counit mate under the specified normalizations; it asserts no invertibility of the
projection. The tensor-unit assertion is the natural unit equation and uses no
Tor bound at the higher coefficient stages.

## New nodes

`def-sf-finite-partial-pullback-tensor` records the explicit construction
`CompactSupportFiniteProjection.pullbackTensorComparison` in
`FinitePartialPullbackTensor`.

`lem-sf-finite-proper-projection-transpose` records the finite proper counit
transpose in `FiniteProperProjectionTranspose`, with the realization/counit
calculation written in its docstring and node.

`lem-sf-projection-identity-tensor-unit` records the independent identity tensor
comparison in `ProjectionIdentityTensorUnit`, including canonical-unit construction,
coefficient passage, and uniqueness from the compositor normalization.

No change record is necessary: no existing signature, definition, public import,
consumer, or other module's node was changed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
