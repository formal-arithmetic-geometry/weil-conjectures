# AlgebraicGeometry.Etale.abelianHigherExchange_coefficient_cube

## Reason

The completed proof uses horizontal pasting directly and establishes its own private
cohomology and single-complex comparisons. It does not use the bundled
`derivedInverseImageComposition` theorem. Remove its public import so this proof does
not retain that unnecessary dependency. The new private helpers use explicit category
instances and the same elaboration options as the source cube-comparison proof.

This is an import and command-context change only. The theorem's complete signature
and the complete definition `abelianHigherExchange` remain verbatim. No target,
mathematical statement, or definition changes meaning.

## Old

The removed public import, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
```

The original top-level context, verbatim:

```lean
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale
```

## New

The unused public import above is removed. New proof imports are private:

```lean
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
```

The added proof context, verbatim:

```lean
open CategoryTheory Limits
-- Avoid costly conversion between the two category instances on derived categories.
attribute [-instance] CategoryTheory.catToReflQuiver
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
```

The generic private helpers are in `Comparisons`; the remaining private helpers are
in `AlgebraicGeometry.Etale`. Their local composition-preservation instances, scoped
functor notation, namespaces, and variables supply their proof context. Every helper
is proved. The category instance command changes elaboration context, not a declared
mathematical object or theorem type. Removing the public import removes its reexports;
there are no existing importers to adapt.

## Users

`python3 tools/downstream.py Sheaf.Paper.KunHigherExchangeCoefficientCube --uses
abelianHigherExchange abelianHigherExchange_coefficient_cube` reports zero downstream
modules. The only textual uses of either declaration are in the assigned module.
The stage-3 brief permits such an item below a parent whose proof is still a hole.
No consumer signatures or proofs need adaptation. No other module is delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.KunHigherExchangeCoefficientCube | E2 | One hole closed; unused import removed; proved private helpers and proof context added. |

## Status

landed 20261020T122106-L-476130 2026-10-20 (merge of deliver/E2/Sheaf.Paper.KunHigherExchangeCoefficientCube)
