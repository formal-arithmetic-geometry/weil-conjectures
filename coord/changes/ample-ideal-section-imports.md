# Proof imports and public scope in Sheaf.AlgebraicGeometry.AmpleIdealSection
## Reason
The proof uses a smaller and more direct dependency set, adds the proved nonvanishing bridge,
and opens the module namespace needed by the theorem body.
## Old
No declaration signature or definition changed; the static preflight classifies added `open` and
`set_option` commands as a public-scope change. The precise command difference is below.

```lean
open CategoryTheory AlgebraicGeometry MonoidalCategory
```

The module imported `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`,
`Sheaf.Paper.NonvanishingSectionTrivializes`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`; its theorem body was `by sorry`.
## New
```lean
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The module imports `Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus` and
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion` and
`WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance`, and uses the source denominator,
free-generator, support, and tensor-power APIs to prove the theorem.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AmpleIdealSection | G2 | proof imports and namespace scope adapted |

`tools/downstream.py ... --uses exists_section_of_ample_ideal` lists only the item's own module
as a textual user. Its 142 import descendants retain exactly the same public signatures and
public imports; the additional proof imports are private. There is no statement or definition
adaptation to perform and no target meaning changes.
## Status
landed 20261012T112839-L-767504 2026-10-12 (merge of deliver/G2/Sheaf.AlgebraicGeometry.AmpleIdealSection)
