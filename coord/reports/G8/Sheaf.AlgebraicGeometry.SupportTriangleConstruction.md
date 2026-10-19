## What changed

Filled the three theorem proofs in
`lean/Sheaf/AlgebraicGeometry/SupportTriangleConstruction.lean` without changing any
signature, definition, instance attribute, import, or triangle map.

`supportKernelAdditive` cancels the component of the kernel inclusion, which is monic
because evaluation preserves monomorphisms. Naturality changes the composite of the
image of a sum into composition with that sum; bilinearity and naturality identify
this with the sum of the two composites.

`supportShriekAdditive` unfolds only the composite defining the closed supported
inverse image and uses additivity of the supported kernel and the existing additive
inverse-image instance.

`supportModelInclusion_unit_zero` evaluates the natural-transformation kernel
condition at the sheaf and reassociates composition with the inverse comparison.

## Proved and sorry left

Closed the original three holes (node `def-pur-support-triangle`):

- `AlgebraicGeometry.ProEtale.supportKernelAdditive`.
- `AlgebraicGeometry.ProEtale.supportShriekAdditive`.
- `AlgebraicGeometry.ProEtale.supportModelInclusion_unit_zero`.

There are no remaining holes in the item and no holes added elsewhere. No split-offs.
The construction still uses the existing comparison-isomorphism theorem from
`ProEtalePairFlasque`; this delivery makes no claim that its dependencies are sorry-free.

## No longer needed

None. No imports were added or removed. The node is a definition with no proof steps
or proof dependencies; the construction and the unit's route are unchanged. The new
proofs use the existing kernel construction, naturality, preadditivity, evaluation's
preservation of monomorphisms, and additivity of the already defined inverse image.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The module's helper docstrings already give
short kernel arguments, and these suffice without new theory or new nodes.
The first remote compile attempt received no server answer within the launcher's
retry budget; the interrupted attempt's process result was unavailable after the
provider interruption, so the compile was retried.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
