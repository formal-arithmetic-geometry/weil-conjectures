/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.QuotientScalarTensorComposition

/-! The unrestricted tensor/pullback coherence square underlying the finite smooth
purity-source cocycle.

Source: blueprint sk-lem-sp-reduction-compatibilities.proof.md, part (3),
tensor coefficient-composition square before restricting to bounded inputs.
(blueprint: lem-pur-finite-smooth-purity-source-tensor-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem tensor_comp_post
    {C D E : Type*} [Category C] [Category D] [Category E]
    (TA : C × C ⥤ C) (TB : D × D ⥤ D) (TC : E × E ⥤ E)
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (α : F ⋙ G ≅ H)
    (δF : TA ⋙ F ≅ F.prod F ⋙ TB) (δG : TB ⋙ G ≅ G.prod G ⋙ TC)
    (δH : TA ⋙ H ≅ H.prod H ⋙ TC)
    {X U : C} {Y V : D} {Z W Z' : E}
    (p : F.obj X ⟶ Y) (q : F.obj U ⟶ V)
    (s : G.obj Y ⟶ Z) (t : G.obj V ⟶ W) (v : Z ⟶ Z')
    (c : H.obj X ⟶ Z') (d : H.obj U ⟶ W)
    (hp : G.map p ≫ s ≫ v = α.hom.app X ≫ c)
    (hq : G.map q ≫ t = α.hom.app U ≫ d)
    (hδ : G.map (δF.hom.app (X, U)) ≫ δG.hom.app (F.obj X, F.obj U) ≫
      TC.map (Prod.mkHom (α.hom.app X) (α.hom.app U)) =
      α.hom.app (TA.obj (X, U)) ≫ δH.hom.app (X, U)) :
    G.map (δF.hom.app (X, U) ≫ TB.map (Prod.mkHom p q)) ≫ δG.hom.app (Y, V) ≫
      TC.map (Prod.mkHom s t) ≫ TC.map (Prod.mkHom v (𝟙 W)) =
    α.hom.app (TA.obj (X, U)) ≫ δH.hom.app (X, U) ≫ TC.map (Prod.mkHom c d) := by
  have hn := δG.hom.naturality
    (show (F.obj X, F.obj U) ⟶ (Y, V) from Prod.mkHom p q)
  change G.map (TB.map (Prod.mkHom p q)) ≫ δG.hom.app (Y, V) =
    δG.hom.app (F.obj X, F.obj U) ≫ TC.map (Prod.mkHom (G.map p) (G.map q)) at hn
  rw [G.map_comp, Category.assoc, reassoc_of% hn, ← TC.map_comp, ← TC.map_comp]
  change _ ≫ _ ≫ TC.map (Prod.mkHom (G.map p ≫ s ≫ v) (G.map q ≫ t ≫ 𝟙 W)) = _
  rw [Category.comp_id, hp, hq]
  change _ ≫ _ ≫ TC.map
    (Prod.mkHom (α.hom.app X) (α.hom.app U) ≫ Prod.mkHom c d) = _
  rw [TC.map_comp]
  simpa only [Category.assoc] using congrArg (· ≫ TC.map (Prod.mkHom c d)) hδ

/-- The tensor/pullback square for the concrete purity source, with the
ordinary twist and pullback cocycles supplied as hypotheses.  This is the
unrestricted structural subargument; bounded constructibility is imposed only
by `puritySourceCocycle`.
Source: blueprint sk-lem-sp-reduction-compatibilities.proof.md, part (3).
(blueprint: lem-pur-finite-smooth-purity-source-tensor-composition). -/
theorem finiteSourceTensorComposition
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X)
    (htwist : ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X).map
          ((twists r m (hn.trans hnm) hmr).tensorPower d).hom ≫
        ((twists m n hn hnm).tensorPower d).hom =
      (ordinaryAssociator X ell hmr hnm).hom.app
          (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d) ≫
        ((twists r n hn (hnm.trans hmr)).tensorPower d).hom)
    (hpull : ∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
      (K : DerivedCategoryModule (coefficient ell r) Y),
      QuotientCocycle
        (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
        (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
        (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
        (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
        (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
        (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
        (ordinaryAssociator Y ell hmr hnm)
        (ordinaryAssociator X ell hmr hnm)
        (ordinaryFinitePullback (coefficient ell r) f)
        (ordinaryFinitePullback (coefficient ell m) f)
        (ordinaryFinitePullback (coefficient ell n) f)
        (ordinaryPullbackMap (FiniteReduction.quotient ell hmr) f)
        (ordinaryPullbackMap (FiniteReduction.quotient ell hnm) f)
        (ordinaryPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) :
  ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      (puritySource (coefficient ell r) f
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d))
      (puritySource (coefficient ell m) f
        (line (coefficient ell m) (ell ^ m) (CharP.cast_eq_zero _ _) X d))
      (puritySource (coefficient ell n) f
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d))
      (fun K ↦ (pullbackTwistComparison f d
        (twists r m (hn.trans hnm) hmr) K).hom)
      (fun K ↦ (pullbackTwistComparison f d (twists m n hn hnm) K).hom)
      (fun K ↦ (pullbackTwistComparison f d
        (twists r n hn (hnm.trans hmr)) K).hom) K := by
  intro r m n hn hnm hmr K
  have ht := quotientScalarTensorComp X ell hmr hnm
    ((ordinaryFinitePullback (coefficient ell r) f).obj K)
    (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d)
  have h :=
    (tensor_comp_post
      (Functor.uncurry.obj (derivedTensor (ModuleCat (coefficient ell r)) X))
      (Functor.uncurry.obj (derivedTensor (ModuleCat (coefficient ell m)) X))
      (Functor.uncurry.obj (derivedTensor (ModuleCat (coefficient ell n)) X))
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator X ell hmr hnm)
      (ExceptionalCoefficients.tensorIso (FiniteReduction.quotient ell hmr) X)
      (ExceptionalCoefficients.tensorIso (FiniteReduction.quotient ell hnm) X)
      (ExceptionalCoefficients.tensorIso
        (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryPullbackMap (FiniteReduction.quotient ell hmr) f K)
      ((twists r m (hn.trans hnm) hmr).tensorPower d).hom
      (ordinaryPullbackMap (FiniteReduction.quotient ell hnm) f
        ((ordinaryScalar (FiniteReduction.quotient ell hmr) Y).obj K))
      ((twists m n hn hnm).tensorPower d).hom
      ((ordinaryFinitePullback (coefficient ell n) f).map
        ((ordinaryAssociator Y ell hmr hnm).hom.app K))
      (ordinaryPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f K)
      ((twists r n hn (hnm.trans hmr)).tensorPower d).hom
      (hpull r m n hn hnm hmr K) (htwist r m n hn hnm hmr)
      (by simpa only [Functor.uncurry_obj_map, Functor.prod_obj,
        Functor.uncurry_obj_obj, Functor.comp_obj, Category.assoc] using ht))
  simp only [QuotientCocycle, pullbackTwistComparison, puritySource,
    ordinaryScalar, ordinaryPullbackMap, coefficient, DerivedCategoryModule,
    Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.uncurry_obj_map, Functor.prod_obj, Functor.comp_obj, Functor.comp_map,
    Functor.uncurry_obj_obj, Functor.flip_obj_map, Functor.flip_obj_obj,
    Prod.mkHom, Category.assoc] at h ⊢
  simpa [Category.assoc] using h

end AlgebraicGeometry.Etale.FiniteSmoothPurity
