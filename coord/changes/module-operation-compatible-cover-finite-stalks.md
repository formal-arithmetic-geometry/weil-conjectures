# AlgebraicGeometry.Scheme.module_operationCompatibleCover

## Reason

The previously reviewed STATEMENT-DISPUTED theorem omits finite underlying geometric
stalks. Tag 093S (1) requires a finite source. A finite ring supplies finitely many
scalar maps but does not make their domains finite. The earlier counterexample on
the spectrum of eventually constant F₂ sequences distinguishes pointwise from
uniform vanishing of tail projections. Retain the hypothesis already available
in the parent theorem, and prove the repaired interface by finite label sections.
Sources: https://stacks.math.columbia.edu/tag/093S and
https://stacks.math.columbia.edu/tag/0DV5.

## Old

```lean
theorem module_operationCompatibleCover
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hG : G = (sheafForget Y.smallEtaleTopology).obj F)
    (𝒰 : Cover.{u} etalePrecoverage Y)
    (h𝒰 : ∀ i : 𝒰.I₀,
      (G.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) :
    IsLocallyConstantSheaf F
```

## New

```lean
theorem module_operationCompatibleCover
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hG : G = (sheafForget Y.smallEtaleTopology).obj F)
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj G))
    (𝒰 : Cover.{u} etalePrecoverage Y)
    (h𝒰 : ∀ i : 𝒰.I₀,
      (G.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) :
    IsLocallyConstantSheaf F
```

## Users

`tools/downstream.py` with `--uses module_operationCompatibleCover` found only
these two textual users among 106 transitive importers. The remaining importers
use the unchanged parent interface and need no adaptation. The parent has no
claim file in the current repository, so it is unclaimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleLocalConstancyOfFiniteUnderlyingOperationCompatibleCover | B2 | Repair its false intermediate signature and prove it completely. |
| Sheaf.Paper.ModuleLocalConstancyOfFiniteUnderlying | unclaimed | Forced one-line proof adaptation: pass hF.2 after rfl. Its signature and visibility remain identical. |

No target signature or definition changes. The new assumption is supplied by the
unchanged parent hypothesis, so every downstream target keeps its meaning.
The declaration docstring is corrected to explain where finiteness is used.

## Status

landed 20261012T202230-L-701163 2026-10-12 (merge of deliver/B2/Sheaf.Paper.ModuleLocalConstancyOfFiniteUnderlyingOperationCompatibleCover)
