## What changed

Removed one redundant proof import. Filled `CategoryTheory.CompletedTensorComparison.naturality_and_rationalization` without changing its signature or any definitions. Added three proved private helpers: fraction representation for a localized tensor module, transport of functor maps across heterogeneous equality, and transport of product morphisms. The proof first cancels the unit only against objects of the full subcategory, obtains naturality of `c`, and applies the naturality of `τ` to obtain naturality of the completed comparison. It then constructs localized component isomorphisms with explicit object transports and proves naturality on arbitrary fractions. Extensionality gives uniqueness.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.CompletedTensorComparison.naturality_and_rationalization` (node `lem-sf-completed-tensor-rational-naturality`). No holes added; no `sorry` remains in the delivered module. This is a proof, not a decomposition. The single-file remote compile passed in 4.5 seconds before removing the redundant import; delivery checks validate the final file and its axioms.

## No longer needed

Removed the redundant proof import `Mathlib.Algebra.Module.LocalizedModule.Basic`: the retained `Mathlib.RingTheory.Localization.BaseChange` imports its API transitively. All three declared proof dependencies remain used; the unit route is unchanged. No modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The fraction representation uses Mathlib's `IsLocalization.tensorProduct_isLocalizedModule` and `IsLocalizedModule.surj` directly, the tensor-module localization API in the stated dependency. This avoids constructing the intermediate equivalence explicitly. The specified localized object maps require transports; the proof retains the heterogeneous component formulas exactly as stated. The bilinearity hypothesis and the equivalence of the restricted functor are stronger than needed once the localized functors and their fraction formulas are supplied; both hypotheses remain unchanged.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
