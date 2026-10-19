# Sheaf.Paper.PbcRationalTransport proof imports and private helpers

## Reason
The completed proof uses the already proved semilinear localization extension exactness
theorem, specialized to the identity coefficient homomorphism. Its import is proof-only.
Four private, proved helpers handle scalar formulas, composition and the equality of two
localization module instances. Public signatures, definitions, instances, visibility,
public imports and existing section commands are unchanged.

## Old
The proof-only imports were:
```lean
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
```
The three theorem bodies `transport_exact`, `pbcRationalTransport` and
`pbcRationalExchange` were `by sorry`.

## New
The proof-only import is:
```lean
import Sheaf.CategoryTheory.SemilinearScalarLocalization
```
All three theorem bodies are complete. The private proved helpers are
`transport_map_smul_localization`, `transport_comp`, `ulift_localization_module` and
`ulift_tmul_heq`. There is no change to any existing signature or definition.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PbcRationalTransport | A3 | Three completed proofs and four private helpers. |

`tools/downstream.py Sheaf.Paper.PbcRationalTransport --uses pbcRationalTransport`
reported no direct declaration users. All importers retain exactly the existing public
interface, so no consumer needs adaptation and no target's meaning changes.

## Status
landed 20261019T192644-L-1851505 2026-10-19 (merge of deliver/A3/Sheaf.Paper.PbcRationalTransport)
