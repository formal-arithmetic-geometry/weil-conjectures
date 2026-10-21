# AlgebraicGeometry.Etale.ordinary_supported_kummer

## Reason

The proof and its Ext/derived-category statement compare recorded derived module
objects with single-complex realizations. Locally selecting the existing instance
proofs stored in `DerivedCategoryModule` avoids expanding the sheafification
construction during these conversions. The two backward elaboration options allow
Lean to use the existing irreducible definitions while elaborating these proofs.
No definition body, written theorem signature, hypothesis, or conclusion changes.

The instance selection is inside a section containing only
`ordinary_supported_kummer`; the section ends before the existing unique-boundary
projection. The selected constants prove properties of the existing categories;
no new category, sheafification, or data instance is installed. The attribute is
local and exports no instance. The auxiliary source proof names are an implementation
dependency, so a future source refactor may require updating them. The linter override
is scoped to the attribute command. The options are local to this module's elaboration.

## Old

Original elaboration options:

```lean
set_option autoImplicit false
```

There is no section or local instance override enclosing the main theorem.
Both original public theorem signatures are preserved verbatim by this delivery.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
```

The main theorem is enclosed by these commands:

```lean
section

-- Use the same category-instance proofs as the recorded derived module category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
```

The corresponding `end` occurs before `ordinary_supported_kummer_uniqueBoundary`.
Only the main theorem's proof is replaced; the unique-boundary proof is retained.
All public imports remain identical. New proof imports are private.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
--uses ordinary_supported_kummer ordinary_supported_kummer_uniqueBoundary` lists
these thirteen downstream modules. Only `FiniteP1DiagonalChernComponents` mentions
one of the two declarations directly, namely the unchanged unique-boundary projection.
No consumer is adapted. The unchanged diagonal-integral and diagonal-alpha sources
were compiled against the packet, along with an additional finite-class consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | C3 | Local proof context; existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | Same public interface; no exported instance change. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | unclaimed | Same public interface; no exported instance change. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | unclaimed | Unchanged source compiled against the packet. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents | unclaimed | Uses the unchanged unique-boundary theorem, outside the local override. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula | unclaimed | Same public interface; no exported instance change. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | Same public interface; no exported instance change. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | Same public interface; no exported instance change. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | P4 | Same public interface; no exported instance change. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | Same public interface; no exported instance change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | G4 | Unchanged source compiled against the packet. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Same public interface; no exported instance change. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Same public interface; no exported instance change. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Same public interface; no exported instance change. |

No target or target-used definition changes. The independent reader reviews this
local command change, the unchanged signatures, and the restored proof modules.

## Status

landed 20261021T002927-L-1578869 2026-10-21 (merge of deliver/C3/Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer)
