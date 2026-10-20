# compactSupportRoosCofinality: local proof context

## Reason

The static interface checker treats the additional universe, section variables,
local elaboration options and local irreducibility attributes as command changes.
This record documents them. Both existing public theorem signatures, all public
abbreviations and all public imports are preserved. The added helper declarations
in the item module are private. No downstream adaptation is required.

## Old

```lean
universe u v uC vC r vA vB
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
namespace CategoryTheory
```

There was no `CofinalityConstruction` section or local irreducibility attribute.
Both public theorems had proof `by sorry`.

## New

```lean
universe u v uC vC r vA vB w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
namespace CategoryTheory
section CofinalityConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : Type u} [Category.{v} D] [Abelian D] [HasCountableProducts D]
```

The section contains the private construction and its proved coordinate,
naturality, arithmetic-composition and quasi-isomorphism lemmas, then ends.
`attribute [local irreducible] strictRoosMapOfSquare rho mu` within that section and
`attribute [local irreducible] strictRoosComplex strictRoosCoordinates` afterwards
prevent accidental expansion of shifted cone data. The private scalar-extension
functor similarly has local irreducibility for `compactRoosScalarFunctor`,
`SheafOfModules.changeOfRingsOfUniverses` and
`SheafOfModules.changeOfRingsHomOfUniverses`. Proved private object/map equations
supply its API before those definitions are folded.
Selected private declarations and the finite-free theorem are checked with
`set_option backward.isDefEq.respectTransparency false in`. These commands
control proof elaboration in this file; their local scope exports no attribute.
The extra universe `w` is unused and does not enter an existing signature.
Both assigned public theorems now have complete proofs. The private `augment`
wrapper fixes the codomain of `roosAugment` explicitly; its coordinate API
then avoids accidental expansion during augmentation assembly. A private
`HasCountableProducts (CochainComplex D ℤ)` instance constructs products from
those in D. Private generic composition, scalar-augmentation and degreewise
product-preservation lemmas keep concrete sheaf instances out of the coordinate
calculations. The final main file compiles cleanly in 34.5 seconds.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CompactSupportRoosCofinality | M8 | Local proof context and private helpers; existing public interfaces preserved. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | not adapted | Direct importer; the same public declarations and imports remain available. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | not adapted | Direct importer; both theorem statements are identical. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | not adapted | Direct importer; no public definition or statement changes. |

`tools/downstream.py Sheaf.CategoryTheory.CompactSupportRoosCofinality` lists
573 transitive importers at this continuation. None is affected: the checker
names command context rather than an altered public declaration. The three
direct importers above were found by searching their import commands. No target
statement or definition used in a target statement changes, so target statement
review does not reopen.

## Status

landed 20261020T122113-L-477514 2026-10-20 (merge of deliver/M8/Sheaf.CategoryTheory.CompactSupportRoosCofinality)
