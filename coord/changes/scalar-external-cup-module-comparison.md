# scalarExternalCup_moduleComparison transparent cup hypothesis repair

## Reason

The returned scalar comparison imports failed in non-module batch probes because
ModuleCohomologyCupProduct privately imports two proof branches containing colliding
anonymous local instances. Its definition IsModuleCupProduct needs only
ModuleCupResolutionData, but importing the definition's current module also imports
its unrelated existence/uniqueness proof. Removing an unheld upstream dependency
would not be a forced adaptation, so this repair avoids that edit altogether.

Expand IsModuleCupProduct in the two scalar theorem hypotheses into its exact
transparent defining formula. Both old theorem signatures remain usable by callers:
scratchpad/repair-verification/lean/OldSignatureProbe.lean compiles applications
with the old named-predicate hypotheses. This is definitional unfolding, with no
change in quantification, assumptions, conclusions, coefficient objects, or degrees.
There is no duplicated definition and no new predicate. All definitions and target
statements stay unchanged. The scalar pullback comparison is restored unchanged.

## Old

The three Lean files were removed from the current library after the returned
landing, while their DAG records remain. The returned sandbox signatures were:

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

Both cup signatures publicly imported Sheaf.Paper.ModuleCohomologyCupProduct.

## New

```lean
theorem scalarCup_moduleCup_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
        (@id X.Modules (F ⊗ G)))
    (hcup :
      ∀ (D : CupResolutionPairing F G)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
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
    (hcup :
      ∀ (D : CupResolutionPairing
            ((tensorPullback (pullback.fst f g)).obj F)
            ((tensorPullback (pullback.snd f g)).obj G))
        (a : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (x : scalarCohomology f F p) (y : scalarCohomology g G q) :
    externalCup f g F G p q x y =
      cup (moduleCohomologyPullback (pullback.fst f g) F p x)
        (moduleCohomologyPullback (pullback.snd f g) G q y)
```

Both cup signatures now publicly import Sheaf.Paper.ModuleCupResolutionData.
The external comparison keeps its complete proof from the two existing scalar
comparison prerequisites. The pullback theorem and its signature stay unchanged.
No new theorem or definition is introduced beyond restoring the three withdrawn
modules. The two prerequisite theorem holes were already in the returned delivery.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | R1 | restored complete reduction; transparent cup hypothesis expanded |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | unclaimed | restored prerequisite; transparent cup hypothesis expanded |
| Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison | unclaimed | restored unchanged prerequisite |

There are no other current Lean source users of these withdrawn declarations.
The two prerequisite modules are absent on the delivery base, so they are restored
modules associated with their existing nodes, not edits to other holders' modules.
No upstream module is adapted.

## Status

landed 20261014T034911-L-815187 2026-10-14 (merge of deliver/R1/Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison)
