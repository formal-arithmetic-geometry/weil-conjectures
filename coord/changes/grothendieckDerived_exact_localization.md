# grothendieckDerived_exact_localization

## Reason

Repair E2 (reviewer X-bc67d). The old theorem asserts a localization from every
triangulated source with coproducts, including the zero category. An invertible
counit would make its right adjoint faithful and force all derived Hom sets to be
subsingletons. Taking a nonzero Grothendieck abelian A disproves this assertion.
The corrected statement fixes the source to D(ModuleCat S), fixes the left functor
to F.mapDerivedCategory and the right functor to U.rightDerivedFunctor, and fixes
the adjunction to adj₀.mapDerivedCategoryRightDerivedAdjunction. Its input is an
exact abelian localization F ⊣ U with invertible counit, supplied by the common
Gabriel–Popescu presentation. The corrected theorem has a complete proof using
existing source-library results, not a sorry.

## Old

```lean
theorem grothendieckDerived_exact_localization
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B)
    (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B)
    (aB : ∀ n : ℤ, (shiftFunctor B n).Additive) (tB : Pretriangulated B)
    (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B) :
    letI := cB
    letI := zB
    letI := sB
    letI := pB
    letI := aB
    letI := tB
    letI := iB
    letI := sumsB
    ∃ (L : B ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ B)
      (adj : L ⊣ R) (sL : L.CommShift ℤ),
    letI := sL
    L.IsTriangulated ∧ IsIso adj.counit
```

## New

```lean
theorem grothendieckDerived_exact_localization
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    {S : Type w} [Ring S] [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
    (adj₀ : F ⊣ U) [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hc₀ : IsIso adj₀.counit) :
    F.mapDerivedCategory.IsTriangulated ∧
      IsIso adj₀.mapDerivedCategoryRightDerivedAdjunction.counit
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.GrothendieckDerivedExactLocalization | C3 | Replace false signature and prove the corrected theorem. |
| Sheaf.CategoryTheory.GrothendieckDerivedCompactLocalizationModel | unclaimed | Forced proof/import adaptation; signature and visibility unchanged. |

The downstream --uses search finds only the item and this parent as textual users.
All 261 transitive importers retain the same parent interface. In particular,
GrothendieckDerivedBrownRetractData compiles unchanged against the repair and is
not delivered. No definition appearing in Challenge.lean changes; all five target
signatures and the parent interface stay identical.

The parent's original line 97 fails against the corrected dependency:

```
Application type mismatch: The argument B has type Type (max uA vA ((max w vH) + 1))
but is expected to have type ModuleCat ?m ⥤ A
in the application grothendieckDerived_exact_localization B
```

The original CompactSource interface supplies no ring, no abelian localization,
and no equivalence identifying its B with the correct module category. Merely
changing that application cannot repair it. Replace that one proof import with
GrothendieckDerivedGabrielPopescuPresentation and import Adjunction.Additive.
The new theorem supplies the missing common data, leaving the derived localization
to the completely proved item. The proof installs the same structural witnesses,
derives U additivity, applies the corrected item, and composes the specific
adjunction with the source equivalence. The composite counit is checked pointwise
using Adjunction.comp_counit_app. Changes are confined to imports and the proof
body; every existing signature and visibility in this unheld module is identical.
The original compact-source theorem, held by C3, is not changed.

## Status

landed 20261013T201741-L-3966291 2026-10-13 (merge of deliver/C3/Sheaf.CategoryTheory.GrothendieckDerivedExactLocalization)
