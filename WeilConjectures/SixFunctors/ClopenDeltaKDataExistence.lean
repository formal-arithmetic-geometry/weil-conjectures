/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ClopenOpenTensorDataExistence

/-! Composite clopen tensor coherence below the main data theorem.
Source: Stacks 0GL1, 04TS and the clopen tensor refinement.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.ClopenComparisonTensorSquare

/-- The composite open tensor map and its prescribed inverse transpose.
This is strictly below `data_nonempty`: all tensor and adjunction records are
supplied by `b`, and only the composite coherence remains.
Source: Stacks 0GL1 and 04TS.
(blueprint: lem-sf-clopen-comparison-tensor-data-existence) -/
structure DeltaKData {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    (b : OpenTensorData o s) where
  deltaK : (b.extensionS.ordinary.mapDerivedCategory ⋙ o.opens.jShriek').prod (𝟭 _) ⋙
      o.tensorX'.functor ≅
    (𝟭 _).prod (o.opens.jStar' ⋙
      (OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory) ⋙
        b.tensorA.functor ⋙ (b.extensionS.ordinary.mapDerivedCategory ⋙ o.opens.jShriek')
  inverse_transposeK : ∀ M N,
    ((exactDerivedAdjunction b.extensionS.adjunction).comp o.opens.adj').homEquiv _ _
        (deltaK.inv.app (M, N)) =
      b.tensorA.functor.map
          (Prod.mkHom
            (((exactDerivedAdjunction b.extensionS.adjunction).comp o.opens.adj').unit.app M)
            (𝟙 _)) ≫
        b.tensorS.tensorComparison.comparison.inv.app
          (o.opens.jStar'.obj (o.opens.jShriek'.obj
            (b.extensionS.ordinary.mapDerivedCategory.obj M)), o.opens.jStar'.obj N) ≫
        (OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.map
          (b.tensorB.tensorComparison.comparison.inv.app
            (o.opens.jShriek'.obj (b.extensionS.ordinary.mapDerivedCategory.obj M), N))

/-- Formal mate calculation for two composable open tensor records: the inverse transpose
of the composite delta along the composite adjunction is the composite unit followed by the
two inverse tensor comparisons. Source: Stacks 0GL1
(blueprint: lem-sf-clopen-delta-k-data-existence). -/
private theorem composite_inverse_transpose {A U X : Type*} [Category A] [Category U]
    [Category X] {F₁ : A ⥤ U} {G₁ : U ⥤ A} {F₂ : U ⥤ X} {G₂ : X ⥤ U}
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) {TA : A × A ⥤ A} {TU : U × U ⥤ U} {TX : X × X ⥤ X}
    (cS : TU ⋙ G₁ ≅ G₁.prod G₁ ⋙ TA) (cB : TX ⋙ G₂ ≅ G₂.prod G₂ ⋙ TU)
    (δS : F₁.prod (𝟭 U) ⋙ TU ≅ (𝟭 A).prod G₁ ⋙ TA ⋙ F₁)
    (δB : F₂.prod (𝟭 X) ⋙ TX ≅ (𝟭 U).prod G₂ ⋙ TU ⋙ F₂)
    (hS : ∀ M N, adj₁.homEquiv _ _ (δS.inv.app (M, N)) =
      TA.map (Prod.mkHom (adj₁.unit.app M) (𝟙 _)) ≫ cS.inv.app (F₁.obj M, N))
    (hB : ∀ M N, adj₂.homEquiv _ _ (δB.inv.app (M, N)) =
      TU.map (Prod.mkHom (adj₂.unit.app M) (𝟙 _)) ≫ cB.inv.app (F₂.obj M, N))
    (M : A) (N : X) :
    (adj₁.comp adj₂).homEquiv _ _
        (F₂.map (δS.inv.app (M, G₂.obj N)) ≫ δB.inv.app (F₁.obj M, N)) =
      TA.map (Prod.mkHom ((adj₁.comp adj₂).unit.app M) (𝟙 _)) ≫
        cS.inv.app (G₂.obj (F₂.obj (F₁.obj M)), G₂.obj N) ≫
          G₁.map (cB.inv.app (F₂.obj (F₁.obj M), N)) := by
  rw [Adjunction.comp_homEquiv]
  beta_reduce
  change adj₁.homEquiv _ _ (adj₂.homEquiv _ _ _) = _
  rw [Adjunction.homEquiv_naturality_left]
  erw [hB (F₁.obj M) N]
  rw [Adjunction.homEquiv_naturality_right]
  erw [hS M (G₂.obj N)]
  rw [Adjunction.comp_unit_app]
  have hn := cS.inv.naturality (X := (F₁.obj M, G₂.obj N))
    (Y := (G₂.obj (F₂.obj (F₁.obj M)), G₂.obj N))
    (Prod.mkHom (adj₂.unit.app (F₁.obj M)) (𝟙 _))
  have e : (Prod.mkHom (adj₁.unit.app M ≫ G₁.map (adj₂.unit.app (F₁.obj M)))
      (𝟙 (G₁.obj (G₂.obj N))) : (M, G₁.obj (G₂.obj N)) ⟶ _) =
      Prod.mkHom (adj₁.unit.app M) (𝟙 _) ≫
        Prod.mkHom (G₁.map (adj₂.unit.app (F₁.obj M))) (G₁.map (𝟙 (G₂.obj N))) := by
    ext <;> simp
  dsimp at hn
  erw [e, TA.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  rw [G₁.map_comp]

/-- Composite clopen tensor coherence exists for the records `b`.
The isomorphism `deltaK` at `(M, N)` is `b.tensorB.delta` at `(s_! M, N)` followed by `j'_!` of
`b.tensorS.delta` at `(M, j'^* N)`: the open projection formula for `j'` and then for `s`
(Stacks 0GL1, applied twice). Its naturality is that of the two deltas. For the identity,
the hom-equivalence of the composite adjunction `s_! ⋙ j'_! ⊣ j'^* ⋙ s^*` is that of
`s_! ⊣ s^*` applied after that of `j'_! ⊣ j'^*`. Naturality of the hom-equivalence on the
left and the inverse transpose of `b.tensorB` turn the inner step into `b.tensorS.delta.inv`
followed by the `j'` unit and the inverse `b.tensorB` comparison. Naturality on the right
and the inverse transpose of `b.tensorS` turn the outer step into the `s` unit followed by the
inverse `b.tensorS` comparison. The composite unit is the `s` unit followed by `s^*` of the
`j'` unit. Naturality of the inverse `b.tensorS` comparison moves that second factor past it,
which is the displayed formula (`composite_inverse_transpose`). Source: Stacks 0GL1 and 04TS.
(blueprint: lem-sf-clopen-delta-k-data-existence) -/
theorem deltaK_data_nonempty {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    [IsClosedImmersion s] (b : OpenTensorData o s) :
    Nonempty (DeltaKData b) := by
  refine ⟨{
    deltaK := NatIso.ofComponents
      (fun X => b.tensorB.delta.app (b.extensionS.ordinary.mapDerivedCategory.obj X.1, X.2) ≪≫
        o.opens.jShriek'.mapIso (b.tensorS.delta.app (X.1, o.opens.jStar'.obj X.2)))
      (by
        rintro ⟨M, N⟩ ⟨M', N'⟩ ⟨f, g⟩
        have h₁ := b.tensorB.delta.hom.naturality
          (X := (b.extensionS.ordinary.mapDerivedCategory.obj M, N))
          (Y := (b.extensionS.ordinary.mapDerivedCategory.obj M', N'))
          (Prod.mkHom (b.extensionS.ordinary.mapDerivedCategory.map f) g)
        have h₂ := b.tensorS.delta.hom.naturality
          (X := (M, o.opens.jStar'.obj N)) (Y := (M', o.opens.jStar'.obj N'))
          (Prod.mkHom f (o.opens.jStar'.map g))
        dsimp at h₁ h₂ ⊢
        rw [reassoc_of% h₁, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
        erw [h₂])
    inverse_transposeK := ?_ }⟩
  intro M N
  exact composite_inverse_transpose (exactDerivedAdjunction b.extensionS.adjunction)
    o.opens.adj' b.tensorS.tensorComparison.comparison b.tensorB.tensorComparison.comparison
    b.tensorS.delta b.tensorB.delta b.tensorS.inverse_transpose b.tensorB.inverse_transpose M N

end SheafOfModules.ClopenComparisonTensorSquare
