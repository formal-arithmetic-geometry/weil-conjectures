# AlgebraicGeometry.Etale.supportedCoefficientTensor_openFirst

## Reason

The one missing proof needs private generic categorical helpers and local elaboration
settings. Server preflight classified the additional `variable`, `open`, `attribute`,
section, universe, and option commands as a potential change to what importers see.
This record documents that syntactic change. Every existing public signature and all
four public definition bodies remain verbatim. All added declarations are private.
All added instance and reducibility attributes are local; they select existing canonical
structures and control unfolding while proving the theorem. No exported instance,
notation, simp attribute, public import, or mathematical interface changes.

## Old

The public theorem signature, unchanged:

```lean
theorem supportedCoefficientTensor_openFirst (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens)
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportCoefficientOpenMate A (supportedFirstOpenMap f g U)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
      (supportedFirstOpenSupport_complement f g b d U)).app (M ⊗ N) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
        (supportedCoefficientTensorDerived A f g b d M N) ≫
      (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M)
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N)).hom =
    supportedCoefficientTensorDerived A (U.ι ≫ f) g (supportOnOpen b U) d M N ≫
      supportedDerivedTensorMap A (pullback (U.ι ≫ f) g)
        (supportFirstOpenCoefficientMap A f g b U M)
        (supportFirstOpenSecondCoefficientMap A f g d U N)
```

Original section context:

```lean
universe u v v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
```

## New

The public theorem has exactly the same signature above and a complete proof in place
of `by sorry`. Its four public coefficient/projection definitions are identical to the
original definitions. The additional commands used around private helper sections are:

```lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
attribute [local irreducible] AlgebraicGeometry.Etale.upperStar
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The two backward elaboration settings are scoped to `false` for several generic
normalization helpers when their concrete cochain presentations must be compared.
Generic `variable` contexts add categories, exact functors, monoidal structures, and
derived-category instances only to private helpers. The local attributes expire at
section or namespace boundaries and are not installed in importing modules.
The named `CachedSheafProofs` section is a scope name only; no cached instance is
introduced in the final file.

## Users

The downstream scan lists the three modules below. No consumer needs adaptation:
the theorem signature and every public definition are unchanged, and all added helpers
are private. Current claim records are recorded for reviewer context.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor | V4 | Fill the original proof; private helpers and local settings |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | H3 | Uses the theorem and original coefficient maps unchanged |
| Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor | W2 | Uses the original projection definitions unchanged |
| Sheaf.AlgebraicGeometry.KunnethSupported | P9 | Transitive importer; no interface change |

No adopted `WeilConjectures` source module is changed. No target statement or definition
changes meaning.

## Status

landed 20261021T120821-L-3952031 2026-10-21 (merge of deliver/V4/Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor)
