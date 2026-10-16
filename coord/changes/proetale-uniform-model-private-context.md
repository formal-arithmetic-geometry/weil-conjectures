# AlgebraicGeometry.Scheme.etale_cover_of_proetale_uniform_model

## Reason

The new proof introduces private helpers for the finite-model isomorphism sheaf.
Their local contexts add universe, variable, open and omit commands. The preflight
conservatively classifies changes to such commands as interface changes and requires
this record. These commands only elaborate declarations inside this module; all added
helpers are private. The public theorem signature and original public imports are
unchanged, and no public definition is added or modified. In particular no definition
used by a target changes and no target statement requires reopening.

## Old

The original module context was:

```lean
universe u
open CategoryTheory
```

Its public declaration had the signature:

```lean
theorem etale_cover_of_proetale_uniform_model
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hF : ∃ (I : Type (u + 1)) (W : I → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ proetalePrecoverage X ∧
        ∀ i, Nonempty ((AlgebraicGeometry.ProEtale.upperStar
          (ModuleCat.{u + 1} Λ) (g i)).obj F ≅
            (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty ((AlgebraicGeometry.ProEtale.upperStar
        (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F ≅
          (constantSheaf (ProEt.topology (𝒰.X i)) (ModuleCat.{u + 1} Λ)).obj M)
```

## New

The generic private helpers use `universe u v w t`, `open CategoryTheory Opposite`,
explicit variables for a site and coefficient category, and a separate section of
variables for module-valued sheaves. The scheme proof uses `open CategoryTheory Limits
Opposite`. Local `omit` commands remove unused helper hypotheses. These contexts introduce
no exported declaration or global instance. The only public declaration still has exactly
this signature:

```lean
theorem etale_cover_of_proetale_uniform_model
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hF : ∃ (I : Type (u + 1)) (W : I → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ proetalePrecoverage X ∧
        ∀ i, Nonempty ((AlgebraicGeometry.ProEtale.upperStar
          (ModuleCat.{u + 1} Λ) (g i)).obj F ≅
            (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty ((AlgebraicGeometry.ProEtale.upperStar
        (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F ≅
          (constantSheaf (ProEt.topology (𝒰.X i)) (ModuleCat.{u + 1} Λ)).obj M)
```

Its former proof hole is replaced by the complete proof in the delivered module.

## Users

Read-only `tools/downstream.py Sheaf.Paper.ProEtaleUniformModelEtaleCover --uses
etale_cover_of_proetale_uniform_model` on the current repository found the following
21 downstream modules. Only `Sheaf.Paper.ProEtaleEtaleFiniteModels` mentions the theorem
itself. No consumer requires adaptation: its public type, available public imports and
all public definitions are identical. All rows below therefore have no statement or
proof change. Holders were read from the current claim files; no adaptation claims
were acquired.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | D2 | None; public signature unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.ProEtaleEtaleFiniteModels | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.ProEtaleOriginFromFiniteModels | unclaimed | None; public signature unchanged. |
| Sheaf.Paper.ProEtaleStratifiedCounit | unclaimed | None; public signature unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | None; public signature unchanged. |
| TargetsCheck | unclaimed | None; public signature unchanged. |
| WeilConjectures | unclaimed | None; public signature unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | None; public signature unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | None; public signature unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | None; public signature unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | None; public signature unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | None; public signature unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | None; public signature unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | None; public signature unchanged. |

## Status

landed 20261016T145216-L-3935102 2026-10-16 (merge of deliver/D3/Sheaf.Paper.ProEtaleUniformModelEtaleCover)
