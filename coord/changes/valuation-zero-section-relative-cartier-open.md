# valuation_zero_section_relative_cartier proof commands

## Reason

The proof uses ideal-sheaf, limit and topology declarations. The namespace openings resolve
these names; the backward elaboration options allow the adjunction comparison to elaborate.
The stage-3 preflight classifies changed top-level commands as visible changes and requires
this record. No declaration signature, definition, public import or target meaning changes.

## Old

```lean
open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
```

## New

```lean
open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
namespace Scheme
namespace Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | W3 | Proof elaboration only; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | not queried; no adaptation | Importer; exported declaration and meaning unchanged. |

Namespace openings and elaboration options are local elaboration commands, not new exported
declarations. Therefore no downstream adaptation or target statement review is needed.

## Status

landed 20261013T003204-L-2431176 2026-10-13 (merge of deliver/W3/Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier)
