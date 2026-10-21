# AlgebraicGeometry.Scheme.affineKernelModelsOfCoordinates

## Reason

The local-coordinate theorem now explicitly names its localization base S.
Matching the original private helper's inferred constant-functor expression
against that base caused conversion to unfold concrete tensor sections; the
original consumer times out after 60 seconds. Explicitly name the same base in
this private hypothesis, and align local category and section-module instance
priorities. The adapted complete module compiles cleanly in 9.1 seconds.

This is a definitionally equal presentation: all hypotheses, witnesses,
equations, and the public theorem are retained. The helper remains private.
The original representability and compactness arguments are unchanged.
No source-library file or Challenge target changes.

## Old

```lean
private theorem affineKernelModelsOfCoordinates
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [CompactSpace S]
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (F : G ⟶ G)
    (hcoords :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ (n : ℕ) (c : Fin n → Fin n → Γ(A.toScheme, ⊤)),
      let L := Etale.localizationRestriction AddCommGrpCat.{u + 1}
        (A.ι ≫ U.hom) inferInstance
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (p : Γ(A.toScheme, ⊤)) = 0 ∧
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e V ((L.map F).hom.app (op V) s) i =
            ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p)) :
    ∃ (n : ℕ) (W : Fin n → S.Opens),
      (∀ a, IsAffineOpen (W a)) ∧
      (⋃ a : Fin n, (W a : Set S)) = Set.univ ∧
      ∀ a, ∃ (P : Scheme.{u}) (π : P ⟶ (W a).toScheme),
        IsAffine P ∧ ∃ _ : Etale π, Nonempty
          ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (W a).ι).obj
              (kernel (F - 𝟙 _))) ≅
                ((W a).toScheme.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π))
```

## New

```lean
private theorem affineKernelModelsOfCoordinates
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [CompactSpace S]
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (F : G ⟶ G)
    (hcoords :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ (n : ℕ) (c : Fin n → Fin n → Γ(A.toScheme, ⊤)),
      let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1}
        (A.ι ≫ U.hom) inferInstance
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (p : Γ(A.toScheme, ⊤)) = 0 ∧
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e V ((L.map F).hom.app (op V) s) i =
            ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p)) :
    ∃ (n : ℕ) (W : Fin n → S.Opens),
      (∀ a, IsAffineOpen (W a)) ∧
      (⋃ a : Fin n, (W a : Set S)) = Set.univ ∧
      ∀ a, ∃ (P : Scheme.{u}) (π : P ⟶ (W a).toScheme),
        IsAffine P ∧ ∃ _ : Etale π, Nonempty
          ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (W a).ι).obj
              (kernel (F - 𝟙 _))) ≅
                ((W a).toScheme.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleAffineKernelModels | unclaimed | Private localization-base and local-instance adaptation; public theorem unchanged; compiled in 9.1 seconds. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Indirect consumer; compiled unchanged in 7.8 seconds. |

The private helper has no users outside its own module. The public downstream
consumer is included for completeness. Neither module has an active holder in
the shared claim snapshot or coord/claims and coord/rework.tsv. The necessary
original failure and changed lines are recorded in report.md.

## Status

landed 20261021T120900-L-3982172 2026-10-21 (merge of deliver/W7/Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalFrames)
