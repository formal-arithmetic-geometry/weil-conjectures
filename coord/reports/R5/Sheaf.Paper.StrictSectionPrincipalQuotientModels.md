## What changed

Reduced `AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strictSectionPrincipalQuotientModels`
without changing its signature. The main module proves successor and augmentation compatibility from the level coordinate
formula, constructs their product map, uses exact countable products and the Roos coordinate
quasi-isomorphism lemma, constructs the signed coordinate comparison with `KFlatRoos.roos`,
and transports the localized comparison from Q(P) to K.

Two new modules state the remaining coefficient-level steps: normalized quotient tensor
models and the coordinate-normalized levelwise quasi-isomorphisms. All added imports are
private proof imports; the existing public import is retained. Existing source-library
files and public interfaces are unchanged.

## Proved and sorry left

Closed the body of
`AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strictSectionPrincipalQuotientModels`
(node `lem-sfb-strict-section-principal-quotient-models`) by a complete Lean reduction.

Added two holes, each the entire proof of one public named theorem:

- `AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strictSectionQuotientTensorModels`
  (`lem-sfb-strict-section-quotient-tensor-models`): reduction tensor models only; no completion.
- `AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strictSectionQuotientConeMaps`
  (`lem-sfb-strict-section-quotient-cone-maps`): level quasi-isomorphisms with explicit coordinates;
  no successor coherence, augmentation equation, products, Roos, localization or completion.

This is a decomposition: one original hole closed, two lower holes added, net minus one.
No sorry remains in the assigned module. Every private helper is fully proved. Validation uses server single-file compilation and
the delivery tool’s compile and preflight checks.

## No longer needed

No existing import removed and no module withdrawn. The original planned
`lem-pe-completion-triangle-comparison` is unnecessary for this proof: the supplied
`T.descent` and its normalized unit equation already give the needed localization step.
The original planned
`lem-pe-kflat-roos-representative-invariance` theorem is unnecessary: direct use of the
fixed K-flat representative and transport by `T.completion.mapIso e.symm` avoids a common
roof or replacement by another representative. Its module remains a public dependency
of the unchanged data interface and supplies the actual quotient tensor/Roos constructions.

The original `lem-sf-ringed-kflat-single-tensor-comparison` and
`lem-sfb-module-object-ringed-site-derived-comparison` are now dependencies of the
coefficient tensor subargument, not an additional completion proof. Neither is withdrawn.
No global pruning claim is made for a module that other declarations still use.

## Where the brief, the DAG or earlier work was wrong

The existing internal completion comparison does not directly specialize to the actual
section-ring quotient tensor tower. The section coefficient comparison and normalized
tensor model have to be supplied separately. The proof now records that distinction.

The lower cone-map coordinate formula determines its successor and augmentation equations;
these are proved in the assigned module rather than left as extra obligations. The
comparison applies to arbitrary K-flat representatives without flat-term assumptions.
The empty site, zero quotient and positive exponent cases are included in each new proof plan.

## New nodes

`lem-sfb-strict-section-quotient-tensor-models`, in
`lean/Sheaf/Paper/StrictSectionQuotientTensorModels.lean`, isolates the normalized derived
reduction tensor models from the completion assertion. Its source and full proof plan
are in the declaration docstring and node.

`lem-sfb-strict-section-quotient-cone-maps`, in
`lean/Sheaf/Paper/StrictSectionQuotientConeMaps.lean`, isolates the coefficient resolution
and K-flat level comparison with the explicit first-projection formula. All product and
completion assembly is proved in the parent. Neither new statement restates the parent.
No change record is required: existing signatures, definitions and public imports stay unchanged.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
