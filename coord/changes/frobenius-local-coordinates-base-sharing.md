# AlgebraicGeometry.Scheme.frobenius_vectorBundle_local_coordinates

## Reason

The local-frame proof now shares its scalar action in transparent local lets.
The original consumer unpacked all these lets at once; its kernel conversion
unfolded tensor pullback and failed at the normal heartbeat limit. Preserve the
frame's lets in a proved private helper, and perform scalar-coordinate and
matrix-coordinate calculations through private APIs. All helpers are proved.

Make the localization's base `S` explicit in the result, rather than inferring
an unreduced constant-functor expression definitionally equal to `S`. Local
category and section-module instance priorities keep the definitional paths
consistent with the frame theorem. These changes preserve the hypotheses,
witnesses, equations and mathematical strength. No Challenge target or adopted
source-library signature, definition, attribute or public import changes.

## Old

```lean
theorem frobenius_vectorBundle_local_coordinates
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree]
    (F : (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E) ⟶
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E))
    (hF : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)),
      F.hom.app U (ULift.up (a.down • e.down)) =
        ULift.up (a.down ^ p • (@id Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)
          (F.hom.app U e).down))) :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ (n : ℕ) (c : Fin n → Fin n → Γ(A.toScheme, ⊤)),
      let L := Etale.localizationRestriction AddCommGrpCat.{u + 1}
        (A.ι ≫ U.hom) inferInstance
      let G := (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (Modules.etaleTensorSectionsSheaf E)
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (p : Γ(A.toScheme, ⊤)) = 0 ∧
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e V ((L.map F).hom.app (op V) s) i =
            ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p)
```

## New

```lean
theorem frobenius_vectorBundle_local_coordinates
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree]
    (F : (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E) ⟶
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E))
    (hF : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)),
      F.hom.app U (ULift.up (a.down • e.down)) =
        ULift.up (a.down ^ p • (@id Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)
          (F.hom.app U e).down))) :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ (n : ℕ) (c : Fin n → Fin n → Γ(A.toScheme, ⊤)),
      let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1}
        (A.ι ≫ U.hom) inferInstance
      let G := (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (Modules.etaleTensorSectionsSheaf E)
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (p : Γ(A.toScheme, ⊤)) = 0 ∧
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e V ((L.map F).hom.app (op V) s) i =
            ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalCoordinates | unclaimed | Necessary proof adaptation and definitionally equal explicit localization base. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalLifts | unclaimed | Compiled unchanged in 28.8 seconds. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleAffineKernelModels | unclaimed | Necessary private localization-base and local-instance adaptation; public theorem unchanged; compiled in 9.1 seconds. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Compiled unchanged in 7.8 seconds. |

The shared claim snapshot has no active holder for these consumer modules.
The original consumer failed against the new frame interface with a
`whnf` deterministic timeout at 200000 heartbeats. The private-let version
compiled at the normal limits in 10.5 seconds; final consumer checks are recorded
in report.md. This repairs the interface change in
`coord/changes/frobenius-local-frames-scalar-sharing.md`.

## Status

landed 20261021T120900-L-3982172 2026-10-21 (merge of deliver/W7/Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalFrames)
