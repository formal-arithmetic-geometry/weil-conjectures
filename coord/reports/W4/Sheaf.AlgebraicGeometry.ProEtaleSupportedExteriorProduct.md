## What changed

In `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct`, proved
`supportedComplexTensorGeneric_eq` by reflexivity. Proved `supportedCoefficients_exact`
from the existing stated `supportedCoefficientAdjunction`: its left adjoint preserves
colimits, while constant sheaf and closed direct image preserve finite limits. Moved
exactness and its two instances after the ordinary adjunction, giving an acyclic order.
The ordinary adjunction theorem itself remains open; its statement and construction do
not depend on the exactness theorem. No new proof import is needed.

Added fully proved `supportedSheaf_smallColimitsGeneric` and
`supportedSheaf_intColimitsGeneric`, registered only as local instances. Both use the
direct Mathlib sheaf-colimit construction, avoiding repeated generic colimit-shrinking
searches in the tensor and derived-functor instance arguments. Synchronous elaboration
(`Elab.async false`) checks proofs before the final axiom probe. No checks are disabled
and no time or heartbeat limit is raised.

Every existing declaration signature, definition body, attribute and public import is
preserved. The complex identity retains its existing unused flat-resolution parameter;
only that theorem's unused-section-variable lint is suppressed. Updated the existing
node's proof fields and attached the two proved helpers. The unit route is preserved. The required interface/command record is
`coord/changes/W4-supported-exterior-product-proof-settings.md`; it lists all 62 downstream
modules and their current holders. No existing consumer mentions either new helper and no
consumer adaptation is needed.

Validation: `lcompile.py --all` compiled the complete module and emitted its artifacts
without errors or warnings in 36.5 seconds. The complex identity's separate axiom check
reported only propext, Classical.choice and Quot.sound. Exactness now uses the original
open ordinary-adjunction theorem, as permitted by the stage-3 dependency policy.

## Proved and sorry left

Closed 2 of the original 7 holes; added 0 holes; split off 0 statements. This is a partial
proof delivery. All declarations below have namespace `AlgebraicGeometry.ProEtale` and
are attached to `def-pur-proetale-supported-exterior-product`.

Closed:

- `AlgebraicGeometry.ProEtale.supportedComplexTensorGeneric_eq`.
- `AlgebraicGeometry.ProEtale.supportedCoefficients_exact` (from the existing stated
  ordinary adjunction, whose proof remains open).

Additional fully proved helpers:

- `AlgebraicGeometry.ProEtale.supportedSheaf_smallColimitsGeneric`.
- `AlgebraicGeometry.ProEtale.supportedSheaf_intColimitsGeneric`.

The five original named theorem holes remain unchanged:

- `AlgebraicGeometry.ProEtale.exists_unique_supportedCoefficientAdjunction`.
- `AlgebraicGeometry.ProEtale.exists_unique_supportedCoefficientTensor`.
- `AlgebraicGeometry.ProEtale.exists_unique_supportedCoefficientTensorComplex`.
- `AlgebraicGeometry.ProEtale.exists_unique_supportedCoefficientTensorDerived`.
- `AlgebraicGeometry.ProEtale.supportedExternalProduct_eq`.

No sorry was moved into a definition, private helper or anonymous declaration. No module
outside the item is adapted. The ordinary-adjunction dependency is the original stronger
statement used for its colimit-preservation consequence, rather than a newly introduced
restatement or split-off hole.

## No longer needed

No baseline import, declaration, node, module or unit realization is withdrawn. The node
originally had no proof dependencies. The exactness proof needs no separate closed-direct-
image exactness dependency: it follows from the ordinary supported-coefficient adjunction
already required by the construction. All existing public imports remain in place.

## Where the brief, the DAG or earlier work was wrong

The item node had empty proof and proof_deps fields despite seven helper theorem holes;
there was no numbered dependency plan for these holes to turn into Lean. Its own ordinary
adjunction supplies the shortest route to finite-colimit preservation, independently of
exactness. The original declaration order hid this route.

The external-product identity is definitionally true, but direct reflexivity, equation
rewrites, congruence, proof generalization and separated generic tensor evaluation exceeded
the kernel-checking limit. The remaining hole is retained honestly. No definition or
statement is changed to claim it closed.

For ordinary adjunction normalization, a diagnostic proved that the coefficient quotient
is epic using exact_openClosedSequence. The missing construction also needs a natural
identification of Hom into a sheaf with the kernel of restriction on sections. The existing
SupportedSectionsHom specializes to lifted rank-one coefficients rather than arbitrary
modules; SupportedProductQuotientModel imports this item, so importing it here would cycle.
These diagnostic lemmas and imports are not included without a completed proof using them.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
