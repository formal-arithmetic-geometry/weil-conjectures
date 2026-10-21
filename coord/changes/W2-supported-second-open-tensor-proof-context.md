# AlgebraicGeometry.Etale.supportedCoefficientTensor_openSecond

## Reason

Complete the single proof in
`Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor`. Preflight conservatively
classifies the private-helper section parameters and local attribute commands as a
context change and requests this record. No existing definition body, declaration
signature, visibility, public import, or target meaning changes. All helpers are private
and fully proved. There are no new holes or modules and no consumer adaptation.

## Old

The module had only the following import:

```lean
public import Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor
```

Its two coefficient-map definitions were already complete and remain verbatim unchanged.
Its theorem had this exact signature followed by `:= by sorry`:

```lean
theorem supportedCoefficientTensor_openSecond (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (V : Y.Opens)
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportCoefficientOpenMate A (supportedSecondOpenMap f g V)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))
      (supportedSecondOpenSupport_complement f g b d V)).app (M ⊗ N) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
        (supportedCoefficientTensorDerived A f g b d M N) ≫
      (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M)
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N)).hom =
    supportedCoefficientTensorDerived A f (V.ι ≫ g) b (supportOnOpen d V) M N ≫
      supportedDerivedTensorMap A (pullback f (V.ι ≫ g))
        (supportSecondOpenFirstCoefficientMap A f g b V M)
        (supportSecondOpenCoefficientMap A f g d V N)
```

There were no private helper sections or local instance/transparency attributes.

## New

The same theorem signature above now has a complete proof. The two existing definitions
remain verbatim unchanged. The import block is:

```lean
public import Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor
import Sheaf.AlgebraicGeometry.SupportedCoefficientOrdinarySecondOpenTensor
import Sheaf.AlgebraicGeometry.SupportedTensorComplexSquare
import Sheaf.CategoryTheory.DerivedExactMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
```

The extra imports are proof-only. The following local attributes control elaboration:

```lean
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance high] sheafBraidedCategory

attribute [local irreducible] supportCoefficientOpenMate supportCoefficientMate
  Functor.exactDerivedMap

attribute [local irreducible] supportSecondOpenFirstCoefficientMap
  supportSecondOpenCoefficientMap supportCoefficientOpenMate supportExactPullbackTensorIso
  exactTensorNatIso supportedDerivedComparisonCondition supportedComplexComparisonNatTrans
```

All these attributes are explicitly local to this module or a nested section. In
particular, the high-priority braided instances do not become instances in any importer.
They align the symmetry projection used by the generic derived-comparison API, avoiding
large definitional reductions. The irreducibility attributes keep constructions folded
while the proved normalization lemmas provide their equations.

The added named sections are `ExactFactors`, `TensorFactors`, `CochainTensorFactor`,
`ModelSquare`, `ExactNaturality`, `TensorPullback`, and `ExactSquare`; each closes before
the final public theorem. Their `variable` contexts parameterize only private helpers
by categories, monoidal structures, exact functors, and comparison transformations.
Fresh universes inside these sections occur only in private declarations. One anonymous
section scopes the exact-derived mate comparison. Declaration-local `omit ... in`
commands remove unused assumptions from these private helpers. The module sets
`backward.isDefEq.respectTransparency false`, with declaration-local `true` for two
triangle-coherence lemmas. These are elaboration options, not exported mathematical data.
The original namespace, universe command, and public-section setting are retained.

Private construction helpers build actual natural transformations or transport existing
isomorphisms. The final canonical tensor comparison uses its specified isomorphism
components directly, with proved naturality and normalization. No arbitrary witness of
an unproved existence theorem is introduced. The only chosen tensor-comparison families
come from the existing unique-existence theorems used by the public definitions.

Validation: `lcompile.py` compiled the complete item in 47.5 seconds with default limits,
no errors and no warnings. A textual comparison verifies both public definition bodies
and the public theorem signature are unchanged. No definition used by a target changes
meaning, so target-statement review is not reopened.

## Users

`tools/downstream.py` lists two transitive downstream modules. Both keep the same
statements and definitions because this packet preserves the public interface and all
added attributes are local. No downstream file is edited or delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor | W2 | Complete theorem proof and private proof context; public signatures and definition bodies unchanged. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | H3 | Direct consumer of all three existing declarations; unchanged interface, no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Transitive consumer; unchanged interface, no adaptation. |

## Status

landed 20261021T120834-L-3959597 2026-10-21 (merge of deliver/W2/Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor)
