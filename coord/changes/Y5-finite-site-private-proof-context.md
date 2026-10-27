# AlgebraicGeometry.ProEtale.finiteSiteWordRefinement

## Reason

The complete proof needs private generic lemmas about localization, inverses and unit
comparisons. The preflight's conservative command check detects their local
`attribute` commands and explicit universe parameters, so this record documents
those changes for independent review. No existing public declaration changes its signature or construction.

## Old

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale
```

The original module had no `DerivedTools` section or private localization helpers;
`finiteSiteWordRefinement` had proof `by sorry`.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u uC uD uE uF vC vD vE vF

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

section DerivedTools

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derivedNatIso_symm
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    -- remaining functor binders, equality and complete proof as in the Lean file
```

The section ends after its private lemmas. The local composition-preservation attributes
are then enabled in this file for the remaining private lemmas and the main proof:

```lean
end DerivedTools

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The category binders occur directly in each of the five private generic helper
signatures; there is no section `variable` command. In particular, the three helpers
reported by the return (`derivedNatIso_symm`, `derivedId_fac`, `square_identity`) now
explicitly distinguish the category's object universe `uC` from its morphism universe
`vC`. The related square and compositor inverse helpers do likewise. The existing
private helpers in `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange` instead
use `[Category C]`, tying these universes together. The site sheaf categories have
object universe `u + 2` and morphism universe `u + 1`, so that specialization cannot be
used here. This follows the return's explicit-binder remedy and preserves the public API.
The attributes are local; the backward elaboration options govern checking in this file. None exports a new
instance, notation or variable. All seven pre-existing definitions, the main theorem's
statement and every public import are byte-identical to the original. The eight added
helpers are private, completely proved theorems. `finiteSiteWordRefinement` has a complete
proof of all ten original conjuncts. The only added import is private:
`import Sheaf.CategoryTheory.DerivedExactSquare`. Unused private imports are removed as
listed in the report.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteSiteWordRefinement | Y5 | Its private proofs use explicit category binders and local instances; original public API unchanged. |

`tools/downstream.py Sheaf.Paper.FiniteSiteWordRefinement --uses finiteSiteWordRefinement`
reports zero downstream modules and only the theorem's own declaration as a use.
A direct source search finds no current Lean importer. This is not a withdrawal:
DAG parents and the unit route are retained, and their future proofs see the same API.
There are no consumer adaptations and no effect on target statements or definitions.

## Status

landed 20261024T022433-L-2991287 2026-10-24 (merge of deliver/Y5/Sheaf.Paper.FiniteSiteWordRefinement)
