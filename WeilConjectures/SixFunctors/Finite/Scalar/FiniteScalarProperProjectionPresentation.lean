/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackComparison
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Constant-scalar presentation of the proper counit projection

Source: Stacks Tags 07A4 and 07A6, constant-scalar specialization of the tensor
comparison and the derived adjunction.
(blueprint: lem-sf-finite-scalar-proper-projection-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The intrinsic proper-factor projection, evaluated by its counit transpose.
This is the existing right-adjoint projection component, with the canonical
uncurried tensor comparison exposed.
Source: Stacks 07A4, 07A6
(blueprint: lem-sf-finite-scalar-proper-projection-presentation). -/
@[irreducible] def finiteScalarProperProjection (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R))
    (K : proEtaleDerivedCategory X R) (L : proEtaleDerivedCategory Y R) :=
  let c := proEtaleConstantRingComparison p R
  let adj := proEtaleRingDerivedAdjunction p
    (proEtaleConstantRing Y R) (proEtaleConstantRing X R) c
  adj.homEquiv _ _
    ((proEtaleCanonicalTensorComparison p
      (proEtaleConstantRing Y R) (proEtaleConstantRing X R) c aY aX).hom.app
        ((proEtaleRingDerivedDirectImage p
          (proEtaleConstantRing Y R) (proEtaleConstantRing X R) c).obj K, L) ≫
      aX.tensor.map (Prod.mkHom (adj.counit.app K) (𝟙 _)))

attribute [local irreducible] sfIntrinsicDerivedEquivalence
  CategoryTheory.Functor.mapDerivedCategory

private def arrowComponentIso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) {M N : C} (e : M ≅ N) :
    Arrow.mk (α.app M) ≅ Arrow.mk (α.app N) :=
  Arrow.isoMk (F.mapIso e) (G.mapIso e) (α.naturality e.hom)

open CategoryTheory.Functor in
private def projectionArrowIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
    {N_D : D ⥤ D'} {N_C : C ⥤ C'} (α : N_D ⋙ F' ≅ F ⋙ N_C)
    [IsIso (mateEquiv adj adj' α.hom).natTrans]
    {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
    {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
    (φ : (postcompose₂.obj F).obj T_D ⟶
      (((whiskeringLeft₂ C).obj F).obj F).obj T_C)
    (φ' : (postcompose₂.obj F').obj T_D' ⟶
      (((whiskeringLeft₂ C').obj F').obj F').obj T_C')
    (m_C : (postcompose₂.obj N_C).obj T_C ≅
      (((whiskeringLeft₂ C').obj N_C).obj N_C).obj T_C')
    (m_D : (postcompose₂.obj N_D).obj T_D ≅
      (((whiskeringLeft₂ D').obj N_D).obj N_D).obj T_D')
    (h : Adjunction.ComparisonCompatible α φ φ' m_C m_D) (M : C) (L : D) :
    Arrow.mk (N_D.map (((adj.rightAdjointProjectionMap φ).app M).app L)) ≅
      Arrow.mk (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app (N_D.obj L)) := by
  let β := asIso (mateEquiv adj adj' α.hom).natTrans
  let l := (m_D.app (G.obj M)).app L ≪≫
    (T_D'.mapIso (β.app M)).app (N_D.obj L)
  let r := β.app ((T_C.obj M).obj (F.obj L)) ≪≫
    G'.mapIso ((m_C.app M).app (F.obj L) ≪≫
      (T_C'.obj (N_C.obj M)).mapIso (α.symm.app L))
  refine Arrow.isoMk l r ?_
  simpa only [l, r, β, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom, Arrow.mk_hom, Category.assoc] using
      (adj.map_rightAdjointProjectionMap_comp_mateEquiv adj' h M L).symm

/-- Constant-scalar realization identifies the single proper counit factor.
There is no open immersion, compactification, operation datum, constructibility
or Tor hypothesis in this statement.

Source: Stacks Tags 07A4 and 07A6, constant-scalar specialization; the proper
transpose step of lem-sf-finite-projection-operation-presentation.
(blueprint: lem-sf-finite-scalar-proper-projection-presentation).

Proof: restrict intrinsic modules to constant scalars. The inverse of this
restriction is the specified associated-module-sheaf realization. The ordinary
tensor comparison sends a balanced pure tensor to its two sections. On flat-term
K-flat complexes it identifies signed total tensors, and resolving localization
identifies the two tensor models aX and aY with the fixed-scalar derived tensors.
The direct-image comparison is normalized on sections; its adjoint pullback
comparison preserves the derived adjunction counit. Consequently the two proper
projection transposes are the same tensor-pullback comparison followed by counit
tensor identity. Injectivity of the adjunction Hom bijection proves the square.
The tensor and direct-image comparisons give its invertible endpoints, hence an
arrow isomorphism. This works for unbounded inputs and arbitrary p, and uses no
projection invertibility. Zero inputs and empty schemes use the same comparisons. -/
theorem finiteScalarProperProjection_presentation
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R))
    (K : proEtaleDerivedCategory X R) (L : proEtaleDerivedCategory Y R) :
    Nonempty (Arrow.mk (finiteScalarProperProjection R p aX aY K L) ≅
      Arrow.mk ((sfIntrinsicDerivedEquivalence Y R).functor.map
        (((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).app
            ((sfIntrinsicDerivedEquivalence X R).inverse.obj K)).app
              ((sfIntrinsicDerivedEquivalence Y R).inverse.obj L)))) := by
  let a := ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let b := proEtaleRingDerivedAdjunction p
    (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
    (proEtaleConstantRingComparison p R)
  let α := finiteScalarPullbackComparison R p
  have : IsIso (mateEquiv a b α.hom).natTrans :=
    isIso_mateEquiv_of_isEquivalence a b α.hom
  obtain ⟨tX, tY, ht⟩ := finiteScalarTensorPullbackComparison R p aX aY
  let φ := finiteScalarCurriedTensorPullback R p aX aY
  let K₀ := (sfIntrinsicDerivedEquivalence X R).inverse.obj K
  let L₀ := (sfIntrinsicDerivedEquivalence Y R).inverse.obj L
  let e := projectionArrowIso a b α
    (ProEtale.leftDerivedUpperStarTensorComparison
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) φ tX tY ht K₀ L₀
  let q := arrowComponentIso (Functor.uncurry.map (b.rightAdjointProjectionMap φ))
    (Iso.prod ((sfIntrinsicDerivedEquivalence X R).counitIso.app K)
      ((sfIntrinsicDerivedEquivalence Y R).counitIso.app L))
  have h : ((b.rightAdjointProjectionMap φ).app K).app L =
      finiteScalarProperProjection R p aX aY K L := by
    rw [Adjunction.rightAdjointProjectionMap_app_app]
    unfold finiteScalarProperProjection
    simp only [b, φ, finiteScalarCurriedTensorPullback, NatTrans.comp_app,
      Functor.curry_map_app_app, Functor.curryObjProdComp_hom_app_app,
      Functor.curry_obj_obj_obj, Functor.curry_obj_map_app, Functor.id_obj]
    erw [Category.comp_id]
  refine ⟨?_⟩
  rw [← h]
  simpa only [Functor.uncurry_map_app, Functor.uncurry_obj_obj, Functor.comp_obj,
    Functor.postcompose₂_obj_obj_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.curry_obj_obj_obj, Functor.id_obj,
    ProEtale.rightDerivedLowerStarProjectionMap,
    ProEtale.derivedTensorRightDerivedLowerStar_obj_obj,
    ProEtale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar_obj_obj,
    a, K₀, L₀] using (e ≪≫ q).symm

end WeilConjectures
