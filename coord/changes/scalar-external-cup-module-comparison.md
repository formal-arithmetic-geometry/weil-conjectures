# scalarExternalCup_moduleComparison restoration

## Reason

Restore the three modules withdrawn after the duplicate-instance import error recorded
in the dedicated repair handoff. All three compile together against the current
published build, using the canonical IsModuleCupProduct import. No shared definition
is duplicated, and no signature is changed from the existing DAG interface.

## Old

All three source files are absent from the current base after the failed landing.
Their declaration interfaces remain recorded in the existing three DAG nodes.

## New

```lean
theorem scalar_moduleCohomologyPullback_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : X.Modules) (n : ℕ)
    (x : scalarCohomology f F n) :
    scalarCohomologyPullback f g a h F n x = moduleCohomologyPullback a F n x
```

```lean
theorem scalarCup_moduleCup_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
        (@id X.Modules (F ⊗ G)))
    (hcup : IsModuleCupProduct F G p q cup)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyCup f F G p q a b = cup a b
```

```lean
theorem scalarExternalCup_moduleComparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace p).obj
        ((tensorPullback (pullback.fst f g)).obj F) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace q).obj
        ((tensorPullback (pullback.snd f g)).obj G) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcup : IsModuleCupProduct ((tensorPullback (pullback.fst f g)).obj F)
      ((tensorPullback (pullback.snd f g)).obj G) p q cup)
    (x : scalarCohomology f F p) (y : scalarCohomology g G q) :
    externalCup f g F G p q x y =
      cup (moduleCohomologyPullback (pullback.fst f g) F p x)
        (moduleCohomologyPullback (pullback.snd f g) G q y)
```

The external comparison is proved by the two existing prerequisite statements;
the two prerequisite statements retain their named sorry proofs.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | G3 | restored complete reduction |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | unclaimed | restored prerequisite |
| Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison | unclaimed | restored prerequisite |

## Status

landed 20261014T022543-L-4044956 2026-10-14 (merge of deliver/G3/Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison)
