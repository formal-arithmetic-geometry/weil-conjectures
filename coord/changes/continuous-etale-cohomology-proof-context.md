# AlgebraicGeometry.ProEtale.continuousEtaleCohomology

## Reason

The delivery preserves both public signatures, the continuous-section functor's data,
the public imports, and the existing docstrings. Preflight detects the additional
nondeclaration commands needed for private generic proof helpers. This record makes
that proof context explicit for independent review. No target or consumer changes
meaning, and no consumer needs adaptation.

The extra universes parameterize abstract categories in proved private helpers.
The two transparency options permit existing comparison functors to elaborate in
the generic helpers; their defaults are restored before the public theorem.
The local irreducibility attribute prevents expensive repeated unfolding of the
continuous-section complex functor; its construction is unchanged and the attribute
is local. The style warning for `letI` is disabled for the final assembly: the three local
derived-category instances are deliberately inlined to keep their data identical
to those in the original signature and avoid expensive model comparisons. The
derived-model existential is eliminated by choice; its right-derived universal
property determines the data up to the isomorphism used downstream. The existing
derived-category construction instances are locally irreducible during the final
assembly, so Lean compares their names rather than unfolding their localization
models. This does not change the instances or their data.
The invertibility of the derived unit on K-injective complexes and additivity of
inverse limit are private proved theorems, installed as local facts only where
needed. No additional global instance declaration is introduced.

## Old

The original nondeclaration command context, excluding comments:

```lean
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
end AlgebraicGeometry.ProEtale
```

## New

The delivered nondeclaration command context, excluding comments:

```lean
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe u w u₁ u₂ v₁ v₂ w₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] continuousEtaleSectionComplexes
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
end AlgebraicGeometry.ProEtale
```

## Users

The refreshed `tools/downstream.py
Sheaf.AlgebraicGeometry.ContinuousEtaleCohomology --uses
continuousEtaleSectionComplexes continuousEtaleCohomology` check on 2026-10-20
reports zero downstream modules; both names occur only in this module.
An earlier check found `Sheaf.Paper.QbarCohomologyFiniteLevelComparison`, which has
since disappeared from the shared source tree. There are no current consumers to
adapt. The original public signatures, public imports and functor data remain
unchanged; all proof helpers are private.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ContinuousEtaleCohomology | V7 | Original public signatures and definition data preserved; theorem proved. |

## Status

landed 20261020T135432-L-1823269 2026-10-20 (merge of deliver/V7/Sheaf.AlgebraicGeometry.ContinuousEtaleCohomology)
