## What changed

Proved `WeilConjectures.PurStrictScalar.scalarLimitTensor_restriction` with its original
signature. Private helpers establish the ordinary cone-projection square, the unit normalization
of the canonical comparison, and its compatibility with a morphism of exact squares.
The ordinary calculation is proved for abstract categories to avoid unfolding concrete
module-sheaf categories during its specialization. Applying them to the ordinary
`limit.pre_post` square (checked by its cone projections) proves the required equation for every derived tower.

Added proof imports of `WeilConjectures.CategoryTheory.DerivedExactCompositionComparison`
and `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
The existing public import and all public declarations are preserved. Updated the item's
node to describe the direct derived-unit argument.

Validation: single-file `lcompile.py` succeeded in 13.8 seconds. The generic
derived-unit argument and the abstract cone calculation were also compiled separately;
the temporary scratch sources were removed before delivery.

## Proved and sorry left

Closed the sole hole: `WeilConjectures.PurStrictScalar.scalarLimitTensor_restriction`
(node `lem-pur-scalar-limit-tensor-restriction`). No holes added; no `sorry` remains
in the delivered module. The theorem uses the existing finite-free exactness and
K-injective-preservation assertion `scalarLimitTensor_exact`; this delivery does not
claim to close that dependency's hole.

## No longer needed

The node no longer needs `lem-pur-compact-support-roos-cofinality` as a proof dependency.
Neither `compactSupportRoosCofinality`, `compactSupportRoosFiniteFree`,
`scalarRoosNormalization`, nor `scalarRoosTensorNormalization` is used. No Lean import
was removed: the defining module is still needed and publicly imports the Roos module.
Consequently this delivery does not claim that the Roos module leaves the targets' import
closure. No module is withdrawn. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned Roos-coordinate argument is unnecessary: the maps are defined by canonical
right derivation of ordinary limit maps, so the universal derived units lift the ordinary
`limit.pre_post` equation directly. Positivity of e is unnecessary for this compatibility
itself; its original binder is retained. The generic proof permits arbitrary natural
transformations r and s, including noninvertible maps, and uses no cofinality assertion.
The identity index, identity coefficients, zero towers and empty schemes obey the same
unit and naturality equations without additional assumptions.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
