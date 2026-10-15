# Local proof context for unbounded_abelian_exchange_comparison

## Reason

The stage-3 scanner classifies the added section variables and local instance registration
as a command-level interface change. This record makes that conservative classification
reviewable. Every existing public declaration signature and both public definition bodies
are preserved. The new derivedSquare_absolute fact is private and registered only locally
within the existing namespace. It supplies absolute right derivability inside the proof.
No existing statement or definition is changed, and no target changes meaning.

## Old

The existing module context was:

```lean
@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
```

There was no derivedSquare_absolute declaration or local registration, and no auxiliary
DerivedSquare section. The comparison theorem body was `:= by sorry`.

## New

The existing context is retained. These elaborator settings and proved helper are added:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private lemma derivedSquare_absolute
    {B C E : Type*} [Category* B] [Category* C] [Category* E]
    [Abelian B] [Abelian C] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions B] (F : B ⥤ C) [F.Additive]
    (T : DerivedCategory C ⥤ E) :
    (F.rightDerivedFunctor ⋙ T).IsRightDerivedFunctor
      (Functor.whiskerRight F.rightDerivedFunctorUnit T ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso B (.up ℤ)) :=
  (HomotopyCategory.KInjectives.localizerMorphism B)
    |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
      (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
        _).isIso_of_isRightDerivedFunctor _ I) _

attribute [local instance] derivedSquare_absolute
```

The new DerivedSquare, DerivedCube, and DerivedMates sections bind only variables for
the private descent helpers and end before the original public definitions. Additional proved private helpers use their
own explicit binders. The original namespace ends as before. No notation or public import
is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison` | F4 | Uses the proved private helper locally; original public signatures and definition bodies are unchanged. |

The read-only downstream scan found 478 transitive module importers and zero external
mentions of derivedSquare_absolute. The command-level scanner reports no changed public
declaration name, so there are no declaration users to adapt. All importers retain the
same public definitions and statements; no forced adaptation is made. The independent
reader should check the local registration and closed auxiliary section scopes.

## Status

landed 20261015T224820-L-2950168 2026-10-15 (merge of deliver/F4/Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison)
