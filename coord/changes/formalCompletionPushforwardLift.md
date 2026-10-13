# AlgebraicGeometry.formalCompletion_pushforward_lift

## Reason

Split the formal-functions lifting and gluing argument from the explicit construction of
kappa and gamma in the push-pull comparison. The new lemma supplies only alpha, for a
supplied canonical kappa and an arbitrary compatible gamma. It does not construct the
quotient comparison or the adjunction map. No existing declaration changes its signature,
visibility, or mathematical meaning.

## Old

Absent: this is a new theorem in a new module. The item previously had one whole-proof sorry.

## New

```lean
theorem formalCompletion_pushforward_lift {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward f).map
          (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (γ : G.obj ⟶ formalCompletionSystem (J.comap f) F.obj ⋙
      Scheme.Modules.pushforward f) :
    ∃ α : G ⟶ (completion Y J).obj
        ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
      α.hom ≫ κ = γ
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullComparison | G4 | Proof-only import; construct kappa and gamma, then obtain alpha. |

No existing importer sees a signature or definition change. There are no forced adaptations.

## Status

landed 20261013T000045-L-2231647 2026-10-13 (merge of deliver/G4/Sheaf.AlgebraicGeometry.FormalSystemsPushPullComparison)
