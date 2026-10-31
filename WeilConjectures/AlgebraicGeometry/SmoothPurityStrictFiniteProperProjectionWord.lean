/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictFiniteTensorPullbackSquare

/-! Component squares of the strict finite projection comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private theorem properProjection_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : D ⥤ C} {G : C ⥤ D} {F' : D' ⥤ C'} {G' : C' ⥤ D'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (EX : C ⥤ C') (EY : D ⥤ D')
    (s : ComparisonAdjunctionCoordinates EY EX adj adj')
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (TC' : C' × C' ⥤ C') (TD' : D' × D' ⥤ D')
    (tx : TC ⋙ EX ≅ (EX.prod EX) ⋙ TC')
    (ty : TD ⋙ EY ≅ (EY.prod EY) ⋙ TD')
    (phi : TD ⋙ F ⟶ (F.prod F) ⋙ TC)
    (phi' : TD' ⋙ F' ⟶ (F'.prod F') ⋙ TC')
    (ht : ∀ A B : D,
      EX.map (phi.app (A, B)) ≫ tx.hom.app (F.obj A, F.obj B) ≫
        TC'.map (Prod.mkHom (s.left.hom.app A) (s.left.hom.app B)) =
      s.left.hom.app (TD.obj (A, B)) ≫ F'.map (ty.hom.app (A, B)) ≫
        phi'.app (EY.obj A, EY.obj B))
    (K : C) (L : D) :
    EY.map (adj.homEquiv _ _ (phi.app (G.obj K, L) ≫
        TC.map (Prod.mkHom (adj.counit.app K) (𝟙 _)))) ≫
      s.right.hom.app (TC.obj (K, F.obj L)) ≫
      G'.map (tx.hom.app (K, F.obj L) ≫
        TC'.map (Prod.mkHom (𝟙 _) (s.left.hom.app L))) =
    ty.hom.app (G.obj K, L) ≫
      TD'.map (Prod.mkHom (s.right.hom.app K) (𝟙 _)) ≫
      adj'.homEquiv _ _ (phi'.app (G'.obj (EX.obj K), EY.obj L) ≫
        TC'.map (Prod.mkHom (adj'.counit.app (EX.obj K)) (𝟙 _))) := by
  dsimp only [Functor.id_obj, Functor.comp_obj] at *
  have transport {M : D} {N : C} (z : F.obj M ⟶ N) :
      adj'.homEquiv _ _ (s.left.inv.app M ≫ EX.map z) =
        EY.map (adj.homEquiv _ _ z) ≫ s.right.hom.app N := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← s.unit M]
    simp only [Functor.map_comp, Category.assoc, ← G'.map_comp_assoc,
      Iso.hom_inv_id_app]
    erw [G'.map_id, Category.id_comp]
    have hn := s.right.hom.naturality z
    change EY.map (G.map z) ≫ s.right.hom.app N =
      s.right.hom.app (F.obj M) ≫ G'.map (EX.map z) at hn
    rw [← hn]
  have hh := transport
    (phi.app (G.obj K, L) ≫ TC.map (Prod.mkHom (adj.counit.app K) (𝟙 (F.obj L))))
  rw [← reassoc_of% hh]
  rw [← adj'.homEquiv_naturality_right, ← adj'.homEquiv_naturality_left,
    ← adj'.homEquiv_naturality_left]
  apply congrArg (adj'.homEquiv _ _)
  have hn := tx.hom.naturality (Prod.mkHom (adj.counit.app K) (𝟙 (F.obj L)))
  have hp := phi'.naturality (Prod.mkHom (s.right.hom.app K) (𝟙 (EY.obj L)))
  have hc : EX.map (adj.counit.app K) =
      s.left.hom.app (G.obj K) ≫ F'.map (s.right.hom.app K) ≫
        adj'.counit.app (EX.obj K) := by
    rw [s.counit]
    simp only [Iso.hom_inv_id_app_assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj,
    Functor.prod_map] at hn hp
  rw [EX.map_id] at hn
  rw [F'.map_id] at hp
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hc]
  simp only [← TC'.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  rw [show Prod.mkHom
      (s.left.hom.app (G.obj K) ≫ F'.map (s.right.hom.app K) ≫
        adj'.counit.app (EX.obj K)) (s.left.hom.app L) =
      Prod.mkHom (s.left.hom.app (G.obj K)) (s.left.hom.app L) ≫
        Prod.mkHom (F'.map (s.right.hom.app K) ≫ adj'.counit.app (EX.obj K)) (𝟙 _) by
    ext <;> simp]
  rw [TC'.map_comp, reassoc_of% (ht (G.obj K) L)]
  simp only [Iso.inv_hom_id_app_assoc]
  have he : Prod.mkHom
      (F'.map (s.right.hom.app K) ≫ adj'.counit.app (EX.obj K)) (𝟙 (F'.obj (EY.obj L))) =
      Prod.mkHom (F'.map (s.right.hom.app K)) (𝟙 _) ≫
        Prod.mkHom (adj'.counit.app (EX.obj K)) (𝟙 _) := by ext <;> simp
  dsimp only [Functor.comp_obj]
  rw [he, TC'.map_comp, ← reassoc_of% hp]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The proper counit factor is preserved by the pinned tensor realization.
Source: blueprint operations proof (2), proper counit transpose.
(blueprint: new-lem-sp-strict-finite-proper-projection-word).
Proof: apply strictFiniteTensorPullbackSquare and identify the left coordinate
with comparisonFinitePull using coordinates.property. Transport the native
adjunction Hom bijection by its unit equation. Naturality of the tensor
comparison moves the counit to its realized image; the coordinate counit equation
replaces this by the left coordinate, the image of the right coordinate and the
target counit. Substitute the tensor pullback square and cancel the left
coordinate. Naturality of the target tensor-pullback map moves the right
coordinate to the source. This gives properProjection_transport. Finally expand
the native proper projection by its component counit-transpose formula and
uncurry the tensor maps. No compactification or open extension is involved.
-/
theorem strictFiniteProperProjectionWord (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (coordinates : StrictFiniteCoordinates l E b)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    (hpin : (∀ (T : Scheme.{u}) (n : ℕ),
    ∃ e : SheafOfModules.OpenTensorNormalization.FiniteRealization.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n),
    ∃ t : AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel.{u} (B l E T n),
    ∃ d : SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
        (ULift.{u + 1, u} (R l E n)) T ⋙ e.derived ≅
          (e.derived.prod e.derived) ⋙ t.functor,
      HEq e.equivalence (sfIntrinsicModuleEquivalence T (R l E n)) ∧
      HEq e.underlying (comparisonFiniteUnderlying l E b T n) ∧
      HEq t.functor (comparisonLevelTensor l E b T n) ∧
      ComparisonFiniteTensorRepresentative l E b T n t ∧ HEq d (tensor T n) ∧
      Nonempty (@SheafOfModules.OpenTensorNormalization.FiniteTensorPin.{u}
        (ULift.{u + 1, u} (R l E n)) _ _ T (B l E T n)
        (comparisonFiniteConstantSection l E T n) e t d))) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))),
      (comparisonFiniteRealization l E b Y n).map
          (X := (SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) Y).obj
              ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                f).rightDerivedFunctor.obj K, L))
          (Y := (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
            f).rightDerivedFunctor.obj
              ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
                (ULift.{u + 1, u} (R l E n)) X).obj
                  (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                    f).leftDerivedFunctor.obj L)))
          (((rightDerivedLowerStarProjectionMap
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).app K).app L) ≫
        (coordinates.val f n).right.hom.app
          ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) X).obj
              (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                f).leftDerivedFunctor.obj L)) ≫
        (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor.map
          ((tensor X n).hom.app
              (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                f).leftDerivedFunctor.obj L) ≫
            (comparisonLevelTensor l E b X n).map
              (Prod.mkHom (𝟙 _) ((comparisonFinitePull l E b f n).hom.app L))) =
      (tensor Y n).hom.app
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
            f).rightDerivedFunctor.obj K, L) ≫
        (comparisonLevelTensor l E b Y n).map
          (Prod.mkHom ((coordinates.val f n).right.hom.app K) (𝟙 _)) ≫
      ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (proEtaleConstantRingAdjunction (R l E n) f)).homEquiv
            ((comparisonLevelTensor l E b Y n).obj
              ((proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor.obj
                ((comparisonFiniteRealization l E b X n).obj K),
                (comparisonFiniteRealization l E b Y n).obj L))
            ((comparisonLevelTensor l E b X n).obj
              ((comparisonFiniteRealization l E b X n).obj K,
                (proEtaleConstantRingDerivedPullback (R l E n) f).obj
                  ((comparisonFiniteRealization l E b Y n).obj L))))
        ((levels.tensorPullback f n).hom.app
            ((proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor.obj
              ((comparisonFiniteRealization l E b X n).obj K),
              (comparisonFiniteRealization l E b Y n).obj L) ≫
          (comparisonLevelTensor l E b X n).map
            (Prod.mkHom
              ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
                (proEtaleConstantRingAdjunction (R l E n) f)).counit.app
                  ((comparisonFiniteRealization l E b X n).obj K)) (𝟙 _))) := by
  intro X Y f n K L
  have ht := strictFiniteTensorPullbackSquare l E b o levels tensor hpin f n
  let phi :
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) Y ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor ⟶
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor.prod
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor) ⋙
          SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) X := by
    let d := Functor.uncurry.map (leftDerivedUpperStarTensorComparison
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f)
    refine { app := fun Z ↦ d.app Z, naturality := ?_ }
    intro Z W a
    have hd := d.naturality a
    dsimp [d, SheafOfModules.OpenTensorNormalization.finiteTensor,
      leftDerivedUpperStarDerivedTensor, derivedTensorLeftDerivedUpperStar,
      Functor.uncurry, Functor.whiskeringLeft₂, Functor.postcompose₂,
      Functor.whiskeringLeft, Functor.whiskeringRight] at hd ⊢
    simpa only [Functor.map_comp] using hd
  have h := properProjection_transport
    (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f)
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (proEtaleConstantRingAdjunction (R l E n) f))
    (comparisonFiniteRealization l E b X n) (comparisonFiniteRealization l E b Y n)
    (coordinates.val f n)
    (SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
      (ULift.{u + 1, u} (R l E n)) X)
    (SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
      (ULift.{u + 1, u} (R l E n)) Y)
    (comparisonLevelTensor l E b X n) (comparisonLevelTensor l E b Y n)
    (tensor X n) (tensor Y n)
    phi (levels.tensorPullback f n).hom (by
      intro M N
      simpa only [coordinates.property f n, phi, Functor.uncurry,
        Functor.comp_obj, proEtaleConstantRingDerivedPullback,
        SheafOfModules.OpenTensorNormalization.finiteTensor,
        leftDerivedUpperStarDerivedTensor, Functor.postcompose₂,
        Functor.whiskeringRight] using ht M N) K L
  dsimp only [Functor.prod_obj, Functor.id_obj, Functor.comp_obj] at h ⊢
  simpa only [coordinates.property f n, rightDerivedLowerStarProjectionMap_app_app,
    SheafOfModules.OpenTensorNormalization.finiteTensor, Functor.uncurry,
    ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) X).obj K).map_id,
    Functor.map_id, NatTrans.id_app, Category.comp_id, phi,
    proEtaleConstantRingDerivedPullback, Functor.prod_obj, Functor.comp_obj,
    Functor.id_obj, Category.assoc] using h

end AlgebraicGeometry.ProEtale.SpTowerShriek
