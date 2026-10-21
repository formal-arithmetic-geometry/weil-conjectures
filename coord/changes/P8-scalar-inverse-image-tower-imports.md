# Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram public imports

## Reason

The completed scalar-tower proof needs the specialized algebraic inverse-image
presentation and evaluation of cochain complexes at each degree. It does not need
the universe-generalized presentation, tensors on complexes, or a derived category.
Remove unused public imports and replace two broad imports with their precise
prerequisites. This record also covers the new scoped commands in the private
proof-helper section, which the static delivery check flags conservatively.

## Old

The original import block, verbatim:

```lean
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Paper.RingedTopoiTensorSections
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
```

The original module opens `CategoryTheory`, `CategoryTheory.Limits` and the
`ChangeOfRings` scope, sets `autoImplicit` to false and
`backward.isDefEq.respectTransparency` to false, and has no private proof-helper
section.

## New

The new import block, verbatim:

```lean
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.Paper.RingedTopoiTensorSections
public import Mathlib.Algebra.Homology.HomologicalComplex
import all Sheaf.CategoryTheory.GeometricModuleTransport
import all Sheaf.CategoryTheory.GeometricModuleConstruction
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Limits
```

The existing three public definitions and the public theorem signature are
byte-for-byte unchanged. Every added declaration is private and fully proved.
The original namespace opens, scope opening and options remain. The additional
`open SheafOfModules.GeometricConstruction`, section variables, cached instances,
local reducibility attributes and elaboration options are inside the
`ProofHelpers` section, which closes before the public theorem. All new attributes
are explicitly local. They export no new instance, notation, open namespace or
attribute, and do not enter any of the existing public definitions. In particular,
no existing target statement or definition changes meaning.

## Users

`tools/downstream.py Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram --uses
scalarPure IsScalarReassociation IsScalarInverseImageComparison
scalar_inverseImage_tower_diagram` checks the current source importers and users.
There are no downstream Lean modules. The unfinished DAG parent still uses this
node; the module and node are retained, and their statements are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram` | P8 | Same public statements and definitions, smaller public import set, completed proof; compiles. |

No consumer module is adapted. The item's node copy updates only the proof route,
proof dependencies, proof origin and removal of the obsolete approved tool use.
The independent delivery reader can review the import narrowing and private scope
alongside the unchanged public declarations.

## Status

landed 20261021T111421-L-120232 2026-10-21 (merge of deliver/P8/Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram)
