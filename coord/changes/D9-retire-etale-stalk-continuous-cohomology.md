# AlgebraicGeometry.Scheme.nonempty_equiv_etale_cohomology_continuous_stalk

## Reason

Retire the assigned zero-hole duplicate. The adopted source already provides the
stronger additive comparison `sheafHAddEquivContinuousCohomology` in the exact
specialization needed by the only remaining consumer, so the duplicate stalk
theorem and its proof dependencies are no longer needed.

## Old

```lean
theorem nonempty_equiv_etale_cohomology_continuous_stalk ... :
    Nonempty (Sheaf.H.{u + 1} F n ≃ continuousCohomology n M)
```

## New

Delete `Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology.lean`. Use the
source construction:

```lean
noncomputable def sheafHAddEquivContinuousCohomology
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (M : TopRep.{u} ℤ Gal(Ks/K)) [DiscreteTopology M.V]
    (c : ((galoisPoint K Ks).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F ≃+ M.V)
    (hc : ∀ (σ : Gal(Ks/K))
      (v : ((galoisPoint K Ks).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
      c ((galoisPoint K Ks).presheafFiberAct (galoisPointAct K Ks) F.obj σ v) =
        M.ρ σ (c v)) (n : ℕ) :
    Sheaf.H F n ≃+ continuousCohomology n M
```

The adapted forward consumer specializes `sheafHAddEquivContinuousCohomology` at the
separable closure, the units sheaf, and degree two, then uses `.symm.toEmbedding`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | D9 | duplicate deleted |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | imports the adopted source comparison and uses its inverse embedding |

## Status

landed 20261021T004825-L-1791435 2026-10-21 (merge of deliver/D9/Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology)
