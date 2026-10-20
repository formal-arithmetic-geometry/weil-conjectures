# AlgebraicGeometry.Scheme.Modules.determinant_split_chart_comparison

## Reason

Retire the duplicate Sheaf module assigned in coord/retire-items.tsv:274. The official
upstream module already proves the common-chart comparison with exactly the same scheme,
short complex, rank, splitting and point hypotheses. It uses canonical exteriorPower and
PresheafOfModules.exteriorPower instead of the legacy exteriorSheaf constructions.
The proved exteriorSheafPresheaf_eq_exteriorPower identifies the presheaves, and hence
also their sheafifications and units. No hypothesis or conclusion changes mathematically.
The upstream file, including all its declarations and public imports, is unchanged.

## Old

In Sheaf.AlgebraicGeometry.Modules.DeterminantSplitChartComparison:

```lean
theorem determinant_split_chart_comparison {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r s : ℕ)
    [S.X₁.IsFiniteLocallyFreeOfRank r] [S.X₃.IsFiniteLocallyFreeOfRank s]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : X.Opens), W ≤ V →
        ∃ (a : Module.Basis (Fin r) (X.presheaf.obj (op W)) (S.X₁.val.obj (op W)))
          (c : Module.Basis (Fin s) (X.presheaf.obj (op W)) (S.X₃.val.obj (op W)))
          (eW : S.X₂.val.obj (op W) ≃ₗ[X.presheaf.obj (op W)]
            (S.X₁.val.obj (op W) × S.X₃.val.obj (op W))),
          (∀ z, eW (S.f.val.app (op W) z) = (z, 0)) ∧
          (∀ z, (eW z).2 = S.g.val.app (op W) z) ∧
          Function.Bijective
            (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (exteriorSheafPresheaf S.X₂ (r + s))).app (op W)) ∧
          Function.Bijective
            ((tensorSectionsMap (exteriorSheaf S.X₁ r) (exteriorSheaf S.X₃ s) W).comp
              (TensorProduct.map (R := X.presheaf.obj (op W))
                (R₂ := X.presheaf.obj (op W)) (σ₁₂ := RingHom.id _)
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 X.ringCatSheaf.obj)).unit.app
                  (exteriorSheafPresheaf S.X₁ r)).app (op W)).hom
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 X.ringCatSheaf.obj)).unit.app
                  (exteriorSheafPresheaf S.X₃ s)).app (op W)).hom))
```

## New

The duplicate module is withdrawn in deleted.txt. The node attaches to the existing,
sorry-free declaration in WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitChartComparison:

```lean
theorem determinant_split_chart_comparison {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r s : ℕ)
    [S.X₁.IsFiniteLocallyFreeOfRank r] [S.X₃.IsFiniteLocallyFreeOfRank s]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : X.Opens), W ≤ V →
        ∃ (a : Module.Basis (Fin r) (X.presheaf.obj (op W)) (S.X₁.val.obj (op W)))
          (c : Module.Basis (Fin s) (X.presheaf.obj (op W)) (S.X₃.val.obj (op W)))
          (eW : S.X₂.val.obj (op W) ≃ₗ[X.presheaf.obj (op W)]
            (S.X₁.val.obj (op W) × S.X₃.val.obj (op W))),
          (∀ z, eW (S.f.val.app (op W) z) = (z, 0)) ∧
          (∀ z, (eW z).2 = S.g.val.app (op W) z) ∧
          Function.Bijective
            (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              ((S.X₂.val.exteriorPower (R := X.presheaf) (r + s)))).app (op W)) ∧
          Function.Bijective
            ((tensorSectionsMap (exteriorPower S.X₁ r) (exteriorPower S.X₃ s) W).comp
              (TensorProduct.map (R := X.presheaf.obj (op W))
                (R₂ := X.presheaf.obj (op W)) (σ₁₂ := RingHom.id _)
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 X.ringCatSheaf.obj)).unit.app
                  (S.X₁.val.exteriorPower (R := X.presheaf) r)).app (op W)).hom
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 X.ringCatSheaf.obj)).unit.app
                  (S.X₃.val.exteriorPower (R := X.presheaf) s)).app (op W)).hom))
```

The sole direct consumer imports the official module privately. After obtaining its
sectionwise comparison, it rewrites the middle unit by
exteriorSheafPresheaf_eq_exteriorPower. For the tensor comparison, it first unfolds
Scheme.Modules.exteriorPower and then rewrites both exterior presheaves, transporting
unit codomains and tensor sheaves together. This yields exactly the previous legacy
comparison. Every declaration signature, attribute and public import of the consumer
remains unchanged; its existing proof after this transport remains unchanged.
The equalities require no positive-rank or nonzero-ring hypothesis, and include
rank zero, zero rings and empty opens. This is a theorem-module retirement, with no
construction or target statement changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective | unclaimed | Sole direct importer and external user of the theorem; replace the private import and transport comparison types in its proof. Its signature is unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | Transitive importer; unchanged consumer theorem signature. No edit. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit | unclaimed | Transitive importer; unchanged consumer theorem signature. No edit. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Transitive importer; unchanged consumer theorem signature. No edit. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive importer; unchanged consumer theorem signature. No edit. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive importer; unchanged consumer theorem signature. No edit. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive importer; unchanged consumer theorem signature. No edit. |

The chart node is retained and points to its upstream realization. Its parent node
continues citing it, and now records the presheaf compatibility used in the consumer.
There are no other direct importers or theorem users in lean/ or quarantine/.
The unit sk-thm-picard-rr and its route are unchanged. Upstream modules already use
the upstream comparison and require no adaptations. No target review is reopened:
no definition or target statement changes.

## Status

landed 20261020T155631-L-3269315 2026-10-20 (merge of deliver/V1/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitChartComparison)
