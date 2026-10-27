# WeilConjectures.IntegralSystemRealization.projectionSystemGeneratingEquations

## Reason

The common-refinement theorem has no assumption that the coefficient prime differs
from the residue characteristic. The existing generating-equations theorem imposed
that unused assumption even though its conclusions assert only equality of intrinsic
unbounded system maps. Its proof is tensor naturality, adjunction transposition and
mate pasting on ringed diagram sites for arbitrary coefficient rings. It neither
inverts the projection formula nor uses finite constructible realization. In particular,
all four identities remain true when the two primes agree. Remove this restriction
from this unclaimed Sheaf theorem; this strengthens its conclusion's domain without
changing any map or geometric assumption. The remaining named hole is preserved.
The node statement and Lean attachment are updated with a complete citer audit.

## Old

```lean
theorem projectionSystemGeneratingEquations
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (ρ : Realizations l E D o) :
    (∀ {U V W : Over (Spec (CommRingCat.of D.k))}
      (f : U ⟶ V) (g : V ⟶ W)
      (cf : Compactification f.left) (cg : Compactification g.left)
      (d : Compactification (cf.overG ≫ cg.overI).left)
      [QuasiCompact cf.i] [QuasiCompact cg.i] [QuasiCompact d.i]
      (_sq : IsPullback cf.g d.i cg.i d.g)
      (M : System l E U.left) (N : System l E W.left),
      (compactificationProjection l E o ρ.compositors ρ.openComparisons cg
          ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).obj M) N ≫
        (Operations.shriek l E o cg.i ⋙ Operations.push l E o cg.g).map
          (compactificationProjection l E o ρ.compositors ρ.openComparisons cf M
            ((pull l E g.left).obj N)) ≫
        projectionSystemCompositor l E o ρ.compositors ρ.openComparisons
          ρ.canonicalBridge ρ.properOpen cf cg d
          ((calculus l E U.left).systemClosed.tensor.obj
            (M, (pull l E f.left).obj ((pull l E g.left).obj N))) ≫
        (Operations.shriek l E o (Compactification.overComp cf cg d).i ⋙
          Operations.push l E o (Compactification.overComp cf cg d).g).map
          ((calculus l E U.left).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((ρ.compositors.pullComp f.left g.left).inv.app N)))) =
      ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom (projectionSystemCompositor l E o ρ.compositors ρ.openComparisons
            ρ.canonicalBridge ρ.properOpen cf cg d M) (𝟙 N)) ≫
        compactificationProjection l E o ρ.compositors ρ.openComparisons
          (Compactification.overComp cf cg d) M N)) ∧
    (∀ {U V W Z : Over (Spec (CommRingCat.of D.k))}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k.left] [IsOpenImmersion i.left]
      [QuasiCompact k.left] [QuasiCompact i.left]
      [IsProper r.left] [IsProper p.left]
      (h : k.left ≫ p.left = r.left ≫ i.left)
      (M : System l E U.left) (N : System l E Z.left),
      ((ρ.openComparisons.projection i.left).hom.app
          ((Operations.push l E o r.left).obj M, N) ≫
        (Operations.shriek l E o i.left).map
          (((properProjection l E o r.left).app M).app ((pull l E i.left).obj N)) ≫
        (Operations.shriek l E o i.left).map ((Operations.push l E o r.left).map
          ((calculus l E U.left).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((ρ.compositors.square l E k.left r.left p.left i.left h).hom.app
              N)))) ≫
        (ρ.properOpen.gamma k.left r.left p.left i.left h).app
          ((calculus l E U.left).systemClosed.tensor.obj
            (M, (pull l E k.left).obj ((pull l E p.left).obj N)))) =
      ((calculus l E Z.left).systemClosed.tensor.map
          (Prod.mkHom ((ρ.properOpen.gamma k.left r.left p.left i.left h).app M) (𝟙 N)) ≫
        ((properProjection l E o p.left).app
          ((Operations.shriek l E o k.left).obj M)).app N ≫
        (Operations.push l E o p.left).map
          ((ρ.openComparisons.projection k.left).hom.app (M, (pull l E p.left).obj N)))) ∧
    (∀ {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
      (c₁ c₂ : Compactification f.left) (v : c₁.Refinement c₂)
      [QuasiCompact c₁.i] [QuasiCompact c₂.i]
      (w : c₁.i ≫ v.hom = (𝟙 U.left) ≫ c₂.i)
      (M : System l E U.left) (N : System l E V.left)
      (hM : IsIso ((ρ.properOpen.gamma c₁.i (𝟙 U.left) v.hom c₂.i w).app M))
      (hT : IsIso ((ρ.properOpen.gamma c₁.i (𝟙 U.left) v.hom c₂.i w).app
        ((calculus l E U.left).systemClosed.tensor.obj (M, (pull l E f.left).obj N)))),
      (compactificationProjection l E o ρ.compositors ρ.openComparisons c₁ M N ≫
        projectionSystemRefinement l E o ρ.compositors ρ.openComparisons
          ρ.canonicalBridge ρ.properOpen c₁ c₂ v w
          ((calculus l E U.left).systemClosed.tensor.obj (M, (pull l E f.left).obj N)) hT) =
      ((calculus l E V.left).systemClosed.tensor.map
          (Prod.mkHom (projectionSystemRefinement l E o ρ.compositors ρ.openComparisons
            ρ.canonicalBridge ρ.properOpen c₁ c₂ v w M hM) (𝟙 N)) ≫
        compactificationProjection l E o ρ.compositors ρ.openComparisons c₂ M N)) ∧
    (∀ (W : Over (Spec (CommRingCat.of D.k)))
      (M N : System l E W.left),
      (compactificationProjection l E o ρ.compositors ρ.openComparisons
        (Compactification.ofIsProper (𝟙 W.left)) M N) =
      ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom ((projectionSystemSupportIdentity l E o ρ.canonicalBridge W.left).hom.app
            M) (𝟙 N)) ≫
        (calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 M)
            ((projectionSystemPullIdentity l E o ρ.canonicalBridge W.left).inv.app N)) ≫
        (projectionSystemSupportIdentity l E o ρ.canonicalBridge W.left).inv.app
          ((calculus l E W.left).systemClosed.tensor.obj
            (M, (pull l E (𝟙 W.left)).obj N))))
```

## New

```lean
theorem projectionSystemGeneratingEquations
    (D : FiniteFieldDatum.{u})
    (o : Operations l E) (ρ : Realizations l E D o) :
    (∀ {U V W : Over (Spec (CommRingCat.of D.k))}
      (f : U ⟶ V) (g : V ⟶ W)
      (cf : Compactification f.left) (cg : Compactification g.left)
      (d : Compactification (cf.overG ≫ cg.overI).left)
      [QuasiCompact cf.i] [QuasiCompact cg.i] [QuasiCompact d.i]
      (_sq : IsPullback cf.g d.i cg.i d.g)
      (M : System l E U.left) (N : System l E W.left),
      (compactificationProjection l E o ρ.compositors ρ.openComparisons cg
          ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).obj M) N ≫
        (Operations.shriek l E o cg.i ⋙ Operations.push l E o cg.g).map
          (compactificationProjection l E o ρ.compositors ρ.openComparisons cf M
            ((pull l E g.left).obj N)) ≫
        projectionSystemCompositor l E o ρ.compositors ρ.openComparisons
          ρ.canonicalBridge ρ.properOpen cf cg d
          ((calculus l E U.left).systemClosed.tensor.obj
            (M, (pull l E f.left).obj ((pull l E g.left).obj N))) ≫
        (Operations.shriek l E o (Compactification.overComp cf cg d).i ⋙
          Operations.push l E o (Compactification.overComp cf cg d).g).map
          ((calculus l E U.left).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((ρ.compositors.pullComp f.left g.left).inv.app N)))) =
      ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom (projectionSystemCompositor l E o ρ.compositors ρ.openComparisons
            ρ.canonicalBridge ρ.properOpen cf cg d M) (𝟙 N)) ≫
        compactificationProjection l E o ρ.compositors ρ.openComparisons
          (Compactification.overComp cf cg d) M N)) ∧
    (∀ {U V W Z : Over (Spec (CommRingCat.of D.k))}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k.left] [IsOpenImmersion i.left]
      [QuasiCompact k.left] [QuasiCompact i.left]
      [IsProper r.left] [IsProper p.left]
      (h : k.left ≫ p.left = r.left ≫ i.left)
      (M : System l E U.left) (N : System l E Z.left),
      ((ρ.openComparisons.projection i.left).hom.app
          ((Operations.push l E o r.left).obj M, N) ≫
        (Operations.shriek l E o i.left).map
          (((properProjection l E o r.left).app M).app ((pull l E i.left).obj N)) ≫
        (Operations.shriek l E o i.left).map ((Operations.push l E o r.left).map
          ((calculus l E U.left).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((ρ.compositors.square l E k.left r.left p.left i.left h).hom.app
              N)))) ≫
        (ρ.properOpen.gamma k.left r.left p.left i.left h).app
          ((calculus l E U.left).systemClosed.tensor.obj
            (M, (pull l E k.left).obj ((pull l E p.left).obj N)))) =
      ((calculus l E Z.left).systemClosed.tensor.map
          (Prod.mkHom ((ρ.properOpen.gamma k.left r.left p.left i.left h).app M) (𝟙 N)) ≫
        ((properProjection l E o p.left).app
          ((Operations.shriek l E o k.left).obj M)).app N ≫
        (Operations.push l E o p.left).map
          ((ρ.openComparisons.projection k.left).hom.app (M, (pull l E p.left).obj N)))) ∧
    (∀ {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
      (c₁ c₂ : Compactification f.left) (v : c₁.Refinement c₂)
      [QuasiCompact c₁.i] [QuasiCompact c₂.i]
      (w : c₁.i ≫ v.hom = (𝟙 U.left) ≫ c₂.i)
      (M : System l E U.left) (N : System l E V.left)
      (hM : IsIso ((ρ.properOpen.gamma c₁.i (𝟙 U.left) v.hom c₂.i w).app M))
      (hT : IsIso ((ρ.properOpen.gamma c₁.i (𝟙 U.left) v.hom c₂.i w).app
        ((calculus l E U.left).systemClosed.tensor.obj (M, (pull l E f.left).obj N)))),
      (compactificationProjection l E o ρ.compositors ρ.openComparisons c₁ M N ≫
        projectionSystemRefinement l E o ρ.compositors ρ.openComparisons
          ρ.canonicalBridge ρ.properOpen c₁ c₂ v w
          ((calculus l E U.left).systemClosed.tensor.obj (M, (pull l E f.left).obj N)) hT) =
      ((calculus l E V.left).systemClosed.tensor.map
          (Prod.mkHom (projectionSystemRefinement l E o ρ.compositors ρ.openComparisons
            ρ.canonicalBridge ρ.properOpen c₁ c₂ v w M hM) (𝟙 N)) ≫
        compactificationProjection l E o ρ.compositors ρ.openComparisons c₂ M N)) ∧
    (∀ (W : Over (Spec (CommRingCat.of D.k)))
      (M N : System l E W.left),
      (compactificationProjection l E o ρ.compositors ρ.openComparisons
        (Compactification.ofIsProper (𝟙 W.left)) M N) =
      ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom ((projectionSystemSupportIdentity l E o ρ.canonicalBridge W.left).hom.app
            M) (𝟙 N)) ≫
        (calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 M)
            ((projectionSystemPullIdentity l E o ρ.canonicalBridge W.left).inv.app N)) ≫
        (projectionSystemSupportIdentity l E o ρ.canonicalBridge W.left).inv.app
          ((calculus l E W.left).systemClosed.tensor.obj
            (M, (pull l E (𝟙 W.left)).obj N))))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed | Remove only the unused characteristic hypothesis on the generating theorem; existing hole retained. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Its unique call drops the now-removed explicit argument; all its own signatures remain identical. |
| Sheaf.Paper.SystemProjectionChangeCompatibility | X7 | New private proof import and refinement specialization establish the unchanged theorem. |

The read-only downstream.py --uses audit found the first two textual users; the third
is introduced in this delivery. No target statement or definition changes meaning.

## Status

landed 20261026T003232-L-155711 2026-10-26 (merge of deliver/X7/Sheaf.Paper.SystemProjectionChangeCompatibility)
