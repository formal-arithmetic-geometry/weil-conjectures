/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ProjectionTensorTrace

/-! # Ordinary tensor mates of coefficient traces

Source: the coefficient tensor calculation in projection purity agreement.
(blueprint: lem-pur-smooth-purity-tensor-trace)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

private theorem derived_tensor_trace
    (B : Type*) [CategoryTheory.Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [Etale.UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget B)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [IsIso (Etale.projectionMap B f)]
    {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (adj : Etale.rightDerivedLowerShriek B f ⊣ G)
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    (V H : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (t : (Etale.rightDerivedLowerShriek B f).obj W ⟶ V) (e : V ≅ 𝟙_ _) :
    ((Etale.derivedTensor B X).obj ((Etale.upperStar B f).leftDerivedFunctor.obj H)).map
        (adj.homEquiv _ _ t) ≫
      (((Etale.derivedTensor B X).obj ((Etale.upperStar B f).leftDerivedFunctor.obj H)).map
          (G.map e.hom) ≫
        ((Etale.derivedTensorSymmetry B X).hom.app
          ((Etale.upperStar B f).leftDerivedFunctor.obj H)).app (G.obj (𝟙_ _)) ≫
        Etale.lowerShriekRightAdjointUnitTensorMap adj H) =
    adj.homEquiv _ _
      ((Etale.rightDerivedLowerShriek B f).map
          (((Etale.derivedTensorSymmetry B X).hom.app
            ((Etale.upperStar B f).leftDerivedFunctor.obj H)).app W) ≫
        ((inv (Etale.projectionMap B f)).app W).app H ≫
        ((Etale.derivedTensor B Y).map (t ≫ e.hom)).app H ≫
        (Etale.derivedTensorLeftUnitor B Y H).hom) := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology B)
  let hπiso : ∀ (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
      (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B)),
      IsIso (((Etale.projectionMap B f).app M).app N) :=
    fun M N ↦ NatIso.isIso_app_of_isIso ((Etale.projectionMap B f).app M) N
  have h := @CategoryTheory.Adjunction.projectionTensorMap_unit_trace
    (_root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology B)) _ _ _ _ _
    (Etale.upperStar B f).leftDerivedFunctor (Etale.rightDerivedLowerShriek B f) G adj
    (fun M N ↦ ((Etale.projectionMap B f).app M).app N) hπiso
    (fun q N ↦ NatTrans.congr_app
      ((Etale.projectionMap B f).naturality q) N) W V t e H
  simp only [Etale.lowerShriekRightAdjointUnitTensorMap,
    Etale.lowerShriekRightAdjointTensorMap, Etale.derivedTensor,
    Etale.derivedTensorSymmetry, _root_.DerivedCategory.canonicalTensorSymmetry,
    BraidedCategory.curriedBraidingNatIso, NatIso.ofComponents_hom_app,
    MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.curriedTensor_obj_map,
    MonoidalCategory.curriedTensor_map_app,
    Etale.derivedTensorLeftUnitor, NatIso.isIso_inv_app] at h ⊢
  convert h using 1
  rfl

/-- The ordinary smooth tensor arrow takes the unit adjunct of an arbitrary
trace to the coefficient adjunct of the same trace. The ordinary degree-zero
unit comparison is retained explicitly.

Source: the tensor calculation of
blueprint, sec-smooth-purity/sk-thm-smooth-purity,
`lem-pur-projection-purity-agreement.proof.md`.
(blueprint: lem-pur-smooth-purity-tensor-trace)

Proof: move the unit comparison into the trace by naturality of the adjunction
bijection. Naturality of the braiding moves the unit adjunct to the first tensor
factor. Apply the generic projection-tensor trace identity, and use naturality
of the adjunction bijection in its source and target for the braiding and left
unitor. No finite-Tor or geometric purity hypothesis is used. -/
theorem smoothPurityEtaleTheta_trace
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (W : Etale.DerivedCategoryModule A X)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      Etale.ordinaryFiniteUnit A Y)
    (H : Etale.DerivedCategoryModule A Y) :
    ((Etale.ordinaryFiniteTensor A X).obj
      ((Etale.ordinaryFinitePullback A f).obj H)).map
        ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _ t) ≫
      smoothPurityEtaleTheta A f H =
    (Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app
            ((Etale.ordinaryFinitePullback A f).obj H)).app W) ≫
        ((inv (Etale.projectionMap (ModuleCat.{u + 1} A) f)).app W).app H ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map
          (t ≫ (smoothPurityUnitIso A Y).hom)).app H ≫
        (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y H).hom) := by
  exact derived_tensor_trace (ModuleCat.{u + 1} A) f
    (Etale.rightDerivedUpperShriekAdjunction A f) W
    (Etale.ordinaryFiniteUnit A Y) H t (smoothPurityUnitIso A Y)

end WeilConjectures.PurityFiniteSetting
