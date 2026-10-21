## What changed

The proof of `AlgebraicGeometry.Etale.supportedCoefficientTensor_openFirst` follows the
existing signed complex square and normalization of the derived support mates. The four
public coefficient/projection definitions and the theorem statement are preserved.

Private categorical lemmas transfer the normalization from homotopy models to cochain
models and identify the two projection coefficient maps. After localization, a functorial
flat resolution in the second coefficient variable makes the target tensor comparison
invertible. Cancellation proves equality on these models. Naturality and the localization
extensionality theorem then give equality for all derived objects. The flatness of closed
supported coefficients is the existing stalk calculation in `SupportedExteriorProduct`.

The normalization steps are combined before specialization. Transparent private comparison
abbreviations retain the canonical instance proofs.
The final version uses the canonical sheaf instances directly and removes the temporary
instance caches. Complete-file compilation succeeded in 51.3 seconds without warnings.

All auxiliary definitions construct their data explicitly, and all auxiliary theorem
proofs are complete. No new statement module or DAG node is introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.supportedCoefficientTensor_openFirst`
(node `lem-pur-supported-coefficient-open-tensor`).

There are zero `sorry`s left in the item module, zero holes added, and zero split-offs.
All private helpers are proved. The complete file compiled without errors or warnings.

## No longer needed

None. The ordinary square and signed totalization theorem are used through
`Sheaf.AlgebraicGeometry.SupportedCoefficientComplexOpenTensor`; the derived mate,
exterior product construction, and localization comparisons are used directly.
No module is withdrawn and no public import is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The proof follows the node's planned route and uses
its existing dependencies. The earlier missing-publication problem has been resolved:
the required project imports now compile. The expensive concrete derived-monoidal
instance comparisons were avoided by generic helper lemmas and explicit normalizations.

The first final preflight required a change record for the added local proof context
commands. This is documented in
`coord/changes/V4-supported-coefficient-open-tensor-proof-context.md`.
All three downstream consumers retain their original interface and require no adaptation.
The file also compiled under its actual module path in 39.8 seconds without warnings.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
