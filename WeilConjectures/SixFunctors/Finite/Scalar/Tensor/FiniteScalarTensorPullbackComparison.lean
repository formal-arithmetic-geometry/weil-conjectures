/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarPullbackComparison
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackRepresentatives

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Constant-scalar tensor and inverse-image comparison

Source: Stacks Project, Tags 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-pullback-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

private theorem representativePairNatTrans_ext
    {K : Type u₁} [Category.{v₁} K] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (q : K ⥤ D) (P : K → Prop)
    (hres : ∀ Z : D, ∃ X : K, P X ∧ Nonempty (q.obj X ≅ Z))
    {F G : D × D ⥤ E} (α β : F ⟶ G)
    (h : ∀ (X Y : K), P X → P Y → α.app (q.obj X, q.obj Y) =
      β.app (q.obj X, q.obj Y)) : α = β := by
  apply NatTrans.ext
  funext Z
  obtain ⟨X, hx, ⟨eX⟩⟩ := hres Z.1
  obtain ⟨Y, hy, ⟨eY⟩⟩ := hres Z.2
  let e := Iso.prod eX eY
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality e.hom, β.naturality e.hom, h X Y hx hy]

private theorem tensorComparisonCompatible_of_representatives
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄} {K : Type u₅}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C']
    [Category.{v₄} D'] [Category.{v₅} K]
    (q : K ⥤ D) (P : K → Prop)
    (hres : ∀ Z : D, ∃ X : K, P X ∧ Nonempty (q.obj X ≅ Z))
    {F : D ⥤ C} {F' : D' ⥤ C'} {EX : C ⥤ C'} {EY : D ⥤ D'}
    {TX : C ⥤ C ⥤ C} {TY : D ⥤ D ⥤ D}
    {TX' : C' ⥤ C' ⥤ C'} {TY' : D' ⥤ D' ⥤ D'}
    (α : EY ⋙ F' ≅ F ⋙ EX)
    (φ : (postcompose₂.obj F).obj TY ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj TX)
    (φ' : (postcompose₂.obj F').obj TY' ⟶ (((whiskeringLeft₂ C').obj F').obj F').obj TX')
    (tX : (postcompose₂.obj EX).obj TX ≅ (((whiskeringLeft₂ C').obj EX).obj EX).obj TX')
    (tY : (postcompose₂.obj EY).obj TY ≅ (((whiskeringLeft₂ D').obj EY).obj EY).obj TY')
    (hrep : ∀ A B : K, P A → P B →
      EX.map ((φ.app (q.obj A)).app (q.obj B)) ≫
          (tX.hom.app (F.obj (q.obj A))).app (F.obj (q.obj B)) =
        α.inv.app ((TY.obj (q.obj A)).obj (q.obj B)) ≫
          F'.map ((tY.hom.app (q.obj A)).app (q.obj B)) ≫
          (φ'.app (EY.obj (q.obj A))).app (EY.obj (q.obj B)) ≫
          (TX'.map (α.hom.app (q.obj A))).app _ ≫
          (TX'.obj _).map (α.hom.app (q.obj B))) :
    Adjunction.ComparisonCompatible α φ φ' tX tY := by
  let l : uncurry.obj TY ⋙ F ⋙ EX ⟶
      ((F ⋙ EX).prod (F ⋙ EX)) ⋙ uncurry.obj TX' :=
    (isoWhiskerRight (finiteScalarUncurryPostcomposeIso TY F) EX).hom ≫
      Functor.whiskerRight (uncurry.map φ) EX ≫
      (isoWhiskerLeft (F.prod F) (finiteScalarUncurryPostcomposeIso TX EX)).hom ≫
      Functor.whiskerLeft (F.prod F) (uncurry.map tX.hom)
  let r : uncurry.obj TY ⋙ F ⋙ EX ⟶
      ((F ⋙ EX).prod (F ⋙ EX)) ⋙ uncurry.obj TX' :=
    Functor.whiskerLeft (uncurry.obj TY) α.inv ≫
      (isoWhiskerRight (finiteScalarUncurryPostcomposeIso TY EY) F').hom ≫
      Functor.whiskerRight (uncurry.map tY.hom) F' ≫
      (isoWhiskerLeft (EY.prod EY)
        (finiteScalarUncurryPostcomposeIso TY' F')).hom ≫
      Functor.whiskerLeft (EY.prod EY) (uncurry.map φ') ≫
      Functor.whiskerRight (NatTrans.prod α.hom α.hom) (uncurry.obj TX')
  have heq : l = r := by
    refine representativePairNatTrans_ext q P hres l r ?_
    intro A B ha hb
    simpa [l, r, finiteScalarUncurryPostcomposeIso, Functor.uncurry, Functor.prod,
      NatTrans.prod, Category.assoc] using hrep A B ha hb
  intro A B
  have h := congrArg (fun z ↦ z.app (A, B)) heq
  simpa [l, r, finiteScalarUncurryPostcomposeIso, Functor.uncurry, Functor.prod,
    NatTrans.prod, Category.assoc] using h

/-- Scalar realization identifies the two tensor bifunctors compatibly with the
canonical inverse-image tensor maps. This statement concerns only tensor and inverse
image; it contains neither a projection map nor a claim that one is invertible.

Source: Stacks Tags 07A4 and 07A6, constant-scalar specialization.
(blueprint: lem-sf-finite-scalar-tensor-pullback-comparison).

Proof: restrict intrinsic module sheaves to constant scalars. The scalar-unit
normalization identifies the inverse restriction with the specified associated-module
sheaf realization. Its ordinary tensor isomorphism sends each balanced pure tensor
to the same pair of sections. Apply this comparison in every bidegree and sum with
the Koszul differential; exactness and preservation of sums identify total tensors.
Flatness and K-flatness are preserved by the equivalence. On flat-term K-flat pairs,
compose this chain comparison with the given representative isomorphism of aX or aY.
Fully faithful resolving restriction extends these isomorphisms to the displayed
natural tensor isomorphisms. The ordinary inverse-image tensor square commutes on
pure tensors, since all four maps preserve the scalar unit. Its signed total square
therefore commutes, and resolving restriction extends it to all unbounded inputs.
The constant-section direct-image normalization identifies the adjoint inverse-image
comparison with finiteScalarPullbackComparison, so this is precisely the square
ComparisonCompatible below. No flatness of the inputs, boundedness, points, or
nonzero ring is required; empty schemes and zero inputs use the same universal
properties. -/
theorem finiteScalarTensorPullbackComparison
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R)) :
    ∃ (tX : (postcompose₂.obj (sfIntrinsicDerivedEquivalence X R).functor).obj
          (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} R)) X) ≅
        (((whiskeringLeft₂ _).obj (sfIntrinsicDerivedEquivalence X R).functor).obj
          (sfIntrinsicDerivedEquivalence X R).functor).obj (curry.obj aX.tensor))
      (tY : (postcompose₂.obj (sfIntrinsicDerivedEquivalence Y R).functor).obj
          (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} R)) Y) ≅
        (((whiskeringLeft₂ _).obj (sfIntrinsicDerivedEquivalence Y R).functor).obj
          (sfIntrinsicDerivedEquivalence Y R).functor).obj (curry.obj aY.tensor)),
      Adjunction.ComparisonCompatible (finiteScalarPullbackComparison R p)
        (ProEtale.leftDerivedUpperStarTensorComparison
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) p)
        (finiteScalarCurriedTensorPullback R p aX aY) tX tY  := by
  let C := Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))
  let q := DerivedCategory.Q (C := C)
  refine ⟨finiteScalarTensorRealization X R aX, finiteScalarTensorRealization Y R aY, ?_⟩
  refine tensorComparisonCompatible_of_representatives q
    (finiteScalarFlatRepresentatives Y R) ?_ _ _ _ _ _ ?_
  · intro Z
    obtain ⟨P, f, hf, hflat, hk⟩ :=
      CochainComplex.exists_quasiIso_flat_kFlat (q.objPreimage Z)
    have : QuasiIso f := hf
    exact ⟨P, ⟨hk, hflat⟩, ⟨asIso (q.map f) ≪≫ q.objObjPreimageIso Z⟩⟩
  · intro P Q hp hq
    exact finiteScalarTensorPullback_onRepresentatives R p aX aY P Q hp hq

end WeilConjectures
