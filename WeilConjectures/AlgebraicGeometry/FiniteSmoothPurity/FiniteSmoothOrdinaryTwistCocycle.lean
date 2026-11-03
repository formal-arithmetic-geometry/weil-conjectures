/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpointComposition
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothRootDerivedComposition
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothZeroTwistComposition
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.QuotientScalarTensorComposition

/-! # Ordinary quotient coherence for normalized root tensors

Source: smooth-purity reduction compatibilities, part (3).
(blueprint: lem-pur-finite-smooth-ordinary-twist-cocycle).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem quotient_comp (ell : ℕ) {r m n : ℕ}
    (hmr : m ≤ r) (hnm : n ≤ m) :
    FiniteReduction.quotient.{u} ell (hnm.trans hmr) =
      (FiniteReduction.quotient ell hnm).comp (FiniteReduction.quotient ell hmr) := by
  exact RingHom.ext (fun x ↦
    congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : FiniteReduction.Coeff.{u} ell n))
      (DFunLike.congr_fun
        (Subsingleton.elim
          (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
          ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
            (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down))

private theorem root_shift_comp
    (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u})
    {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m)
    (a : CoefficientLineComparison (FiniteReduction.quotient ell hmr)
      (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (b : CoefficientLineComparison (FiniteReduction.quotient ell hnm)
      (ell ^ m) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (c : CoefficientLineComparison (FiniteReduction.quotient ell (hnm.trans hmr))
      (ell ^ r) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (ordinaryScalar (FiniteReduction.quotient ell hnm) T).map
        ((scalarShiftIso (FiniteReduction.quotient ell hmr) T 2).hom.app _ ≫
          a.derivedIso.hom⟦(2 : ℤ)⟧') ≫
      (scalarShiftIso (FiniteReduction.quotient ell hnm) T 2).hom.app _ ≫
        b.derivedIso.hom⟦(2 : ℤ)⟧' =
    (ordinaryAssociator T ell hmr hnm).hom.app
        ((ordinaryFiniteLine (coefficient ell r) (ell ^ r)
          (CharP.cast_eq_zero _ _) T)⟦(2 : ℤ)⟧) ≫
      (scalarShiftIso (FiniteReduction.quotient ell (hnm.trans hmr)) T 2).hom.app _ ≫
        c.derivedIso.hom⟦(2 : ℤ)⟧' := by
  have hs : NatTrans.CommShift
      (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology
        (quotient_comp ell hmr hnm)).hom ℤ := by
    dsimp only [Sheaf.derivedRestrictScalarsCompIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let := hs
  exact AlgebraicGeometry.Etale.shifted_comp
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (FiniteReduction.quotient ell hmr)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (FiniteReduction.quotient ell hnm)))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology
      (FiniteReduction.quotient ell (hnm.trans hmr))))
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology (quotient_comp ell hmr hnm))
    a.derivedIso.hom b.derivedIso.hom c.derivedIso.hom
    (ordinaryRootDerivedComp ell T hmr hnm a b c) 2

private theorem tensor_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (TA : C × C ⥤ C) (TB : D × D ⥤ D) (TC : E × E ⥤ E)
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (α : F ⋙ G ≅ H)
    (δF : TA ⋙ F ≅ F.prod F ⋙ TB) (δG : TB ⋙ G ≅ G.prod G ⋙ TC)
    (δH : TA ⋙ H ≅ H.prod H ⋙ TC)
    {X U : C} {Y V : D} {Z W : E}
    (p : F.obj X ⟶ Y) (q : F.obj U ⟶ V)
    (s : G.obj Y ⟶ Z) (t : G.obj V ⟶ W)
    (c : H.obj X ⟶ Z) (d : H.obj U ⟶ W)
    (hp : G.map p ≫ s = α.hom.app X ≫ c)
    (hq : G.map q ≫ t = α.hom.app U ≫ d)
    (hδ : G.map (δF.hom.app (X, U)) ≫ δG.hom.app (F.obj X, F.obj U) ≫
      TC.map (Prod.mkHom (α.hom.app X) (α.hom.app U)) =
      α.hom.app (TA.obj (X, U)) ≫ δH.hom.app (X, U)) :
    G.map (δF.hom.app (X, U) ≫ TB.map (Prod.mkHom p q)) ≫ δG.hom.app (Y, V) ≫
      TC.map (Prod.mkHom s t) =
    α.hom.app (TA.obj (X, U)) ≫ δH.hom.app (X, U) ≫ TC.map (Prod.mkHom c d) := by
  have hn := δG.hom.naturality (show (F.obj X, F.obj U) ⟶ (Y, V) from Prod.mkHom p q)
  change G.map (TB.map (Prod.mkHom p q)) ≫ δG.hom.app (Y, V) =
    δG.hom.app (F.obj X, F.obj U) ≫ TC.map (Prod.mkHom (G.map p) (G.map q)) at hn
  rw [G.map_comp, Category.assoc, reassoc_of% hn, ← TC.map_comp]
  change _ ≫ _ ≫ TC.map (Prod.mkHom (G.map p ≫ s) (G.map q ≫ t)) = _
  rw [hp, hq]
  change _ ≫ _ ≫ TC.map (Prod.mkHom (α.hom.app X) (α.hom.app U) ≫ Prod.mkHom c d) = _
  rw [TC.map_comp]
  simpa only [Category.assoc] using congrArg (· ≫ TC.map (Prod.mkHom c d)) hδ

private theorem line_succ (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (d : ℕ) :
    line A N hA T (d + 1) =
      ((derivedTensor (ModuleCat A) T).obj (line A N hA T d)).obj
        ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) := rfl

private theorem power_comp
    (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u})
    {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m)
    (a : CoefficientLineComparison (FiniteReduction.quotient ell hmr)
      (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (b : CoefficientLineComparison (FiniteReduction.quotient ell hnm)
      (ell ^ m) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (c : CoefficientLineComparison (FiniteReduction.quotient ell (hnm.trans hmr))
      (ell ^ r) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (d : ℕ) :
    (ordinaryScalar (FiniteReduction.quotient ell hnm) T).map (a.tensorPower d).hom ≫
      (b.tensorPower d).hom =
    (ordinaryAssociator T ell hmr hnm).hom.app
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) T d) ≫
      (c.tensorPower d).hom := by
  induction d with
  | zero => exact ordinaryZeroTwistComp T ell hmr hnm
  | succ d ih =>
    have hs := root_shift_comp ell T hmr hnm a b c
    have ht := quotientScalarTensorComp T ell hmr hnm
      (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) T d)
      ((ordinaryFiniteLine (coefficient ell r) (ell ^ r)
        (CharP.cast_eq_zero _ _) T)⟦(2 : ℤ)⟧)
    simpa only [CoefficientLineComparison.tensorPower,
      CoefficientLineComparison.tensorPowerStep,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.uncurry_obj_map,
      Functor.prod_obj, Functor.comp_obj, Functor.uncurry_obj_obj, line_succ,
      ordinaryScalar, coefficient, DerivedCategoryModule,
      Category.assoc] using
      (tensor_comp
        (Functor.uncurry.obj (derivedTensor (ModuleCat (coefficient ell r)) T))
        (Functor.uncurry.obj (derivedTensor (ModuleCat (coefficient ell m)) T))
        (Functor.uncurry.obj (derivedTensor (ModuleCat (coefficient ell n)) T))
        (ordinaryScalar (FiniteReduction.quotient ell hmr) T)
        (ordinaryScalar (FiniteReduction.quotient ell hnm) T)
        (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T)
        (ordinaryAssociator T ell hmr hnm)
        (ExceptionalCoefficients.tensorIso (FiniteReduction.quotient ell hmr) T)
        (ExceptionalCoefficients.tensorIso (FiniteReduction.quotient ell hnm) T)
        (ExceptionalCoefficients.tensorIso
          (FiniteReduction.quotient ell (hnm.trans hmr)) T)
        (a.tensorPower d).hom
        ((scalarShiftIso (FiniteReduction.quotient ell hmr) T 2).hom.app _ ≫
          a.derivedIso.hom⟦(2 : ℤ)⟧')
        (b.tensorPower d).hom
        ((scalarShiftIso (FiniteReduction.quotient ell hnm) T 2).hom.app _ ≫
          b.derivedIso.hom⟦(2 : ℤ)⟧')
        (c.tensorPower d).hom
        ((scalarShiftIso (FiniteReduction.quotient ell (hnm.trans hmr)) T 2).hom.app _ ≫
          c.derivedIso.hom⟦(2 : ℤ)⟧')
        ih hs (by simpa only [Functor.uncurry_obj_map, Functor.prod_obj,
          Functor.uncurry_obj_obj, Functor.comp_obj, Category.assoc] using ht))

/-- The ordered shifted root-line tensor comparisons satisfy the ordinary quotient
cocycle. This is the root-normalization and tensor-induction subargument of
`finiteSmoothOrdinaryTwistedCocycles`.
Source: blueprint sk-lem-sp-reduction-compatibilities.proof.md, part (3).
(blueprint: lem-pur-finite-smooth-ordinary-twist-cocycle). -/
theorem ordinaryTwistCocycle
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X) :
  ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
    (ordinaryScalar (FiniteReduction.quotient ell hnm) X).map
        ((twists r m (hn.trans hnm) hmr).tensorPower d).hom ≫
      ((twists m n hn hnm).tensorPower d).hom =
    (ordinaryAssociator X ell hmr hnm).hom.app
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d) ≫
      ((twists r n hn (hnm.trans hmr)).tensorPower d).hom := by
  intro r m n hn hnm hmr
  exact power_comp ell X hmr hnm (twists r m (hn.trans hnm) hmr)
    (twists m n hn hnm) (twists r n hn (hnm.trans hmr)) d

set_option linter.unusedVariables false in
end AlgebraicGeometry.Etale.FiniteSmoothPurity
