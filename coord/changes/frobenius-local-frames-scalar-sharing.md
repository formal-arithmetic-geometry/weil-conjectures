# AlgebraicGeometry.Scheme.frobenius_vectorBundle_local_frames

## Reason

The statement's inline scalar expression made Lean repeatedly unfold the tensor
pullback construction during conversion. The original proof exceeded the normal
kernel heartbeat limit and single-file compile limit. Share the same explicit
scalar action in a local `let`, and type the structural morphism and etale
composition functor explicitly. These are definitionally equal presentations
of the original statement: all parameters, assumptions, existential witnesses,
naturality requirements and scalar equations are retained. No target in
`Challenge.lean`, source-library definition, attribute or public import changes.
The scalar action is the existing module action, explicitly constructed in the
statement; no data is selected from an existence theorem.

The proof constructs the free frame and its coordinates. Its private coordinate
API and shared action prevent the conversion from unfolding tensor pullback.
The complete module compiles at the normal limits, with zero holes.

## Old

```lean
theorem frobenius_vectorBundle_local_frames
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree] :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ n : ℕ,
      let L := Etale.localizationRestriction AddCommGrpCat.{u + 1}
        (A.ι ≫ U.hom) inferInstance
      let G := (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (Modules.etaleTensorSectionsSheaf E)
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (a : Γ(V.left, ⊤))
          (s : (L.obj G).obj.obj (op V)),
          e V (ULift.up ((@id Γ(((MorphismProperty.Over.map ⊤
              (inferInstance : Etale (A.ι ≫ U.hom))).obj V).left, ⊤) a) •
            (@id Γ((Modules.tensorPullback ((MorphismProperty.Over.map ⊤
              (inferInstance : Etale (A.ι ≫ U.hom))).obj V).hom).obj E, ⊤) s.down))) =
                a • e V s)
```

## New

```lean
theorem frobenius_vectorBundle_local_frames
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree] :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ n : ℕ,
      let f : A.toScheme ⟶ S := A.ι ≫ U.hom
      let M : A.toScheme.Etale ⥤ S.Etale :=
        MorphismProperty.Over.map (Y := S) ⊤
          (inferInstance : Etale f)
      let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1}
        f inferInstance
      let G := (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (Modules.etaleTensorSectionsSheaf E)
      let act (V : A.toScheme.Etale) (b : Γ(V.left, ⊤))
          (s : (Modules.etaleTensorSectionsSheaf E).obj.obj (op (M.obj V))) :=
        (@id Γ((M.obj V).left, ⊤) b) •
          (@id Γ((Modules.tensorPullback (M.obj V).hom).obj E, ⊤) s)
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (a : Γ(V.left, ⊤))
          (s : (L.obj G).obj.obj (op V)),
          e V (ULift.up (act V a s.down)) =
                a • e V s)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalFrames | W7 | Proved; scalar expression shared using transparent local lets. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalCoordinates | unclaimed | Necessary proof adaptation; same mathematical statement with explicit localization base. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalLifts | unclaimed | Compiled unchanged in 28.8 seconds. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleAffineKernelModels | unclaimed | Necessary private localization-base and local-instance adaptation; public theorem unchanged; compiled in 9.1 seconds. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Compiled unchanged in 7.8 seconds. |

No active claim for the four consumer modules was listed in the shared claim
snapshot when preparing this change. Consumer checks are recorded in report.md.

## Status

landed 20261021T120900-L-3982172 2026-10-21 (merge of deliver/W7/Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalFrames)
