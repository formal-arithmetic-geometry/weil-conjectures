/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-!
# Identity-open normalization for condensed-module exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-prop-sf-comp-proper/sk-prop-sf-comp-proper.proof.md`,
sentence beginning “For j=id”.
(blueprint: lem-sf-identity-open-exchange-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactificationReindexing

private theorem identity_unit {C : Type*} [Category C] {L R : C ⥤ C}
    (a : L ⊣ R) (p : R ≅ 𝟭 C) (K : C) :
    a.unit.app K ≫ p.hom.app (L.obj K) =
      ((a.ofNatIsoRight p).leftAdjointUniq Adjunction.id).inv.app K := by
  apply (Iso.comp_hom_eq_id (((a.ofNatIsoRight p).leftAdjointUniq Adjunction.id).app K)).1
  have h := Adjunction.unit_leftAdjointUniq_hom_app (a.ofNatIsoRight p) Adjunction.id K
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.id_map, Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.assoc,
    Iso.app_hom]
    using h

private theorem identity_unit_of_counit {C : Type*} [Category C] {L R : C ⥤ C}
    (a : L ⊣ R) (i : L ≅ 𝟭 C) (p : R ≅ 𝟭 C)
    (hc : ∀ N, i.inv.app (R.obj N) ≫ a.counit.app N = p.hom.app N) (K : C) :
    a.unit.app K ≫ p.hom.app (L.obj K) = i.inv.app K := by
  rw [← hc, ← Category.assoc]
  have hn := i.inv.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [hn, Category.assoc, a.left_triangle_components, Category.comp_id]

private theorem identity_mate {C E : Type*} [Category C] [Category E]
    {L R : C ⥤ C} {L' R' : E ⥤ E} (a : L ⊣ R) (a' : L' ⊣ R')
    (i : L ≅ 𝟭 C) (i' : L' ≅ 𝟭 E) (p : R ≅ 𝟭 C) (p' : R' ≅ 𝟭 E)
    (G : C ⥤ E) (θ : R ⋙ G ≅ G ⋙ R')
    (bc : L ⋙ G ≅ G ⋙ L')
    (hb : bc.inv = ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans)
    (hc : ∀ N, i.inv.app (R.obj N) ≫ a.counit.app N = p.hom.app N)
    (hc' : ∀ N, i'.inv.app (R'.obj N) ≫ a'.counit.app N = p'.hom.app N)
    (hθ : ∀ N, θ.hom.app N ≫ p'.hom.app (G.obj N) = G.map (p.hom.app N))
    (K : C) :
    bc.hom.app K ≫ i'.hom.app (G.obj K) = G.map (i.hom.app K) := by
  have hu := identity_unit_of_counit a i p hc K
  have hm : i'.inv.app (G.obj K) ≫ bc.inv.app K = G.map (i.inv.app K) := by
    have h := unit_mateEquiv_symm a a' (TwoSquare.mk _ _ _ _ θ.hom) K
    change G.map (a.unit.app K) ≫ θ.hom.app (L.obj K) =
      a'.unit.app (G.obj K) ≫ R'.map
        (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans.app K) at h
    rw [← hb] at h
    have hh := congrArg (fun z ↦ z ≫ p'.hom.app (G.obj (L.obj K))) h
    rw [Category.assoc, hθ, ← G.map_comp, hu] at hh
    have hn := p'.hom.naturality (bc.inv.app K)
    dsimp only [Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [Category.assoc, hn,
      ← Category.assoc, identity_unit_of_counit a' i' p' hc'] at hh
    exact hh.symm
  apply (cancel_epi (bc.inv.app K)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (cancel_epi (i'.inv.app (G.obj K))).1
  rw [← Category.assoc, Iso.inv_hom_id_app, hm,
    ← G.map_comp, Iso.inv_hom_id_app, G.map_id]
  rfl

private theorem identity_compactification_exchange
    {C E C' E' : Type*} [Category C] [Category E] [Category C'] [Category E']
    (J : C ⥤ C) (J' : C' ⥤ C')
    (P : E ⥤ C) (R : C ⥤ E) (a : P ⊣ R)
    (P' : E' ⥤ C') (R' : C' ⥤ E') (a' : P' ⊣ R')
    (G : E ⥤ E') (H : C ⥤ C') (θ : G ⋙ P' ≅ P ⋙ H)
    (b : J ⋙ H ≅ H ⋙ J') (i : J ≅ 𝟭 C) (i' : J' ≅ 𝟭 C')
    (χ : (J ⋙ R) ⋙ G ⟶ H ⋙ (J' ⋙ R'))
    (hχ : χ = SuppliedExchangeProjection.compactificationExchangeFromData
      J J' P R a P' R' a' G H H θ b)
    (e : R ⋙ G ⟶ H ⋙ R') (he : e = a.exchangeRight a' θ)
    (hb : ∀ K, b.hom.app K ≫ i'.hom.app (H.obj K) = H.map (i.hom.app K)) (K : C) :
    χ.app K ≫ R'.map (i'.hom.app (H.obj K)) =
      G.map (R.map (i.hom.app K)) ≫ e.app K := by
  rw [hχ, he]
  unfold SuppliedExchangeProjection.compactificationExchangeFromData
  simp only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← R'.map_comp, hb, ← Adjunction.exchangeRight_eq_mateEquiv]
  exact ((a.exchangeRight a' θ).naturality (i.hom.app K)).symm

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  upperStar lowerStar openImmersionLowerShriek
  openImmersionLowerShriekUpperStarAdjunction upperStarComp

-- The native identity-open counit calculation from ClopenLowerShriek, kept private here
-- to avoid importing that module's unrelated compactification and exceptional-image theory.
set_option maxHeartbeats 2000000 in
-- Comparing the native derived identity functors requires extra elaboration time.
private theorem identity_derived_counit (X : Scheme.{u}) (W : D Λ X) :
    (derivedOpenImmersionLowerShriekId Λ X).inv.app ((P Λ (𝟙 X)).obj W) ≫
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ (𝟙 X)).symm).counit.app
          W = (leftDerivedUpperStarId Λ X).hom.app W := by
  have hn := (derivedOpenImmersionLowerShriekId Λ X).inv.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ (𝟙 X)).hom.app W)
  simp only [Functor.id_map] at hn
  have hc := Adjunction.mapDerivedCategoryAdjunction_counit_app_of_iso
    (openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)) (openImmersionLowerShriekId Λ X)
    (upperStarId Λ X)
    (Adjunction.leftAdjointUniq_ofNatIsoRight_inv_app_comp_counit _ _) W
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Iso.symm_inv,
    Functor.whiskerRight_app]
  rw [← reassoc_of% hn]
  erw [hc]
  simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion]

set_option maxHeartbeats 2000000 in
-- Comparing the native derived adjunction endpoints requires extra elaboration time.
private theorem identity_beta {T T' : Scheme.{u}} (a : T' ⟶ T) (K : D Λ T) :
    (beta Λ (j := 𝟙 T) (j' := 𝟙 T') (w := a) (v := a)
      (IsPullback.id_vert a)).hom.app K ≫
      (derivedOpenImmersionLowerShriekId Λ T').hom.app ((P Λ a).obj K) =
    (P Λ a).map ((derivedOpenImmersionLowerShriekId Λ T).hom.app K) := by
  refine identity_mate (oa Λ (𝟙 T)) (oa Λ (𝟙 T'))
    (derivedOpenImmersionLowerShriekId Λ T) (derivedOpenImmersionLowerShriekId Λ T')
    (leftDerivedUpperStarId Λ T) (leftDerivedUpperStarId Λ T')
    (P Λ a) (pullbackSquareComparison Λ (IsPullback.id_vert a).toCommSq).symm
    (beta Λ (IsPullback.id_vert a)) ?_ ?_ ?_ ?_ K
  · unfold beta openMate
    rfl
  · intro N
    exact identity_derived_counit Λ T N
  · intro N
    exact identity_derived_counit Λ T' N
  · intro N
    rw [← pullbackSquareComparison_flip]
    exact pullbackSquareComparison_identity Λ a N

private theorem identity_native_unit :
    ∀ (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)),
      (openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 T)).unit.app M ≫
          (upperStarId Λ T).hom.app (((𝟙 T)_!open⟦Λ⟧).obj M) =
        (AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriekId Λ T).inv.app M := by
  intro T M
  exact identity_unit (openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 T))
    (upperStarId Λ T) M

private theorem proper_square_exchange_eq {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (a : Y' ⟶ Y) :
    squareExchange Λ (c := Compactification.ofIsProper f)
      (c' := Compactification.ofIsProper (pullback.snd f a))
      { middle := pullback.fst f a
        openSquare := IsPullback.id_vert (pullback.fst f a)
        properSquare := (IsPullback.of_hasPullback f a).toCommSq } =
      SuppliedExchangeProjection.compactificationExchangeFromData
        (J Λ (𝟙 X)) (J Λ (𝟙 (pullback f a)))
        (P Λ f) (R Λ f) (derivedUpperStarLowerStarAdjunction Λ f)
        (P Λ (pullback.snd f a)) (R Λ (pullback.snd f a))
        (derivedUpperStarLowerStarAdjunction Λ (pullback.snd f a))
        (P Λ a) (P Λ (pullback.fst f a)) (P Λ (pullback.fst f a))
        (pullbackSquareComparison Λ (IsPullback.of_hasPullback f a).toCommSq)
        (beta Λ (IsPullback.id_vert (pullback.fst f a))) := by
  unfold squareExchange
  rfl

private theorem base_change_eq {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    baseChangeMap Λ sq =
      (derivedUpperStarLowerStarAdjunction Λ p).exchangeRight
        (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq) := rfl

private theorem identity_proper_exchange :
    ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (a : Y' ⟶ Y) (K : D Λ X),
      (squareExchange Λ (c := Compactification.ofIsProper f)
          (c' := Compactification.ofIsProper (pullback.snd f a))
          { middle := pullback.fst f a
            openSquare := IsPullback.id_vert (pullback.fst f a)
            properSquare := (IsPullback.of_hasPullback f a).toCommSq }).app K ≫
          (R Λ (pullback.snd f a)).map
            ((AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId
              Λ (pullback f a)).hom.app ((P Λ (pullback.fst f a)).obj K)) =
        (P Λ a).map ((R Λ f).map
          ((AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId
            Λ X).hom.app K)) ≫
          (baseChangeMap Λ (IsPullback.of_hasPullback f a).toCommSq).app K := by
  intro X Y Y' f hf a K
  exact identity_compactification_exchange
    (J Λ (𝟙 X)) (J Λ (𝟙 (pullback f a)))
    (P Λ f) (R Λ f) (derivedUpperStarLowerStarAdjunction Λ f)
    (P Λ (pullback.snd f a)) (R Λ (pullback.snd f a))
    (derivedUpperStarLowerStarAdjunction Λ (pullback.snd f a))
    (P Λ a) (P Λ (pullback.fst f a))
    (pullbackSquareComparison Λ (IsPullback.of_hasPullback f a).toCommSq)
    (beta Λ (IsPullback.id_vert (pullback.fst f a)))
    (derivedOpenImmersionLowerShriekId Λ X)
    (derivedOpenImmersionLowerShriekId Λ (pullback f a))
    (squareExchange Λ (c := Compactification.ofIsProper f)
      (c' := Compactification.ofIsProper (pullback.snd f a))
      { middle := pullback.fst f a
        openSquare := IsPullback.id_vert (pullback.fst f a)
        properSquare := (IsPullback.of_hasPullback f a).toCommSq })
    (proper_square_exchange_eq Λ f a)
    (baseChangeMap Λ (IsPullback.of_hasPullback f a).toCommSq)
    (base_change_eq Λ (IsPullback.of_hasPullback f a).toCommSq)
    (identity_beta Λ (pullback.fst f a)) K

/-- The identity-open extension is canonically the identity, its base-change comparison is
identity after this normalization, and the identity-open compactification exchange is the
ordinary direct-image exchange.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-prop-sf-comp-proper/sk-prop-sf-comp-proper.proof.md`, sentence beginning “For j=id”.
(blueprint: lem-sf-identity-open-exchange-normalization)

The first conjunct is the unit normalization `π_T ∘ η_{id_T} = ι_T⁻¹` of the canonical
identification `ι_T : (id_T)_! ≅ Id`. The second is `ι_{T'} ∘ β = La^*(ι_T)` for the
identity-open square over `a : T' ⟶ T`. The third is the compact-support exchange of the
compactification `(id_X, f)` of a proper `f` and of its base change `(id_{X'}, f')`, with
`ḡ = g'`: after `Rf'_*(ι_{X'})` and `Rf_*(ι_X)` it is the direct-image exchange `Ex_{*,f}`.

Proof.
1. The canonical underived identity-open comparison is the unique comparison of left
   adjoints after transporting the open adjunction by `upperStarId`. The Mathlib unit
   equation for `leftAdjointUniq`, followed by cancellation, gives the first conjunct.
   At the derived level, the existing identity-open counit normalization and the triangle
   identity give the same unit normalization for `oa` and `leftDerivedUpperStarId`.
2. Work directly with the derived mate whose inverse defines `β`. The comparison for
   the identity-open square is the comparison on the flipped square. The existing native
   pullback identity-coherence theorem identifies it with the identity under the canonical
   pullback identity comparisons. Apply the mate-unit equation, naturality of the target
   identity comparison, and the derived unit normalization from step 1. This identifies
   the inverse of `β` with the inverse identity-open comparisons. Cancel these
   isomorphisms to obtain `ι_{T',La^*K} ∘ β_K = La^*(ι_{T,K})`.
3. Unfold the compactification exchange for `(id_X, f)` and its base change. Its
   components are the direct-image mate at `j_! K`, followed by `Rf'_*(β_K)`.
   The mate is the ordinary `baseChangeMap`. Apply step 2 to the latter factor and
   naturality of `baseChangeMap` at `ι_{X,K}` to obtain the third conjunct.
-/
theorem identityOpenExchangeNormalization :
    (∀ (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)),
      (openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 T)).unit.app M ≫
          (upperStarId Λ T).hom.app (((𝟙 T)_!open⟦Λ⟧).obj M) =
        (AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriekId Λ T).inv.app M) ∧
    (∀ {T T' : Scheme.{u}} (a : T' ⟶ T) (K : D Λ T),
      (beta Λ (j := 𝟙 T) (j' := 𝟙 T') (w := a) (v := a)
            (IsPullback.id_vert a)).hom.app K ≫
          (AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId Λ T').hom.app
            ((P Λ a).obj K) =
        (P Λ a).map
        ((AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId
          Λ T).hom.app K)) ∧
    (∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (a : Y' ⟶ Y) (K : D Λ X),
      (squareExchange Λ (c := Compactification.ofIsProper f)
          (c' := Compactification.ofIsProper (pullback.snd f a))
          { middle := pullback.fst f a
            openSquare := IsPullback.id_vert (pullback.fst f a)
            properSquare := (IsPullback.of_hasPullback f a).toCommSq }).app K ≫
          (R Λ (pullback.snd f a)).map
            ((AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId
              Λ (pullback f a)).hom.app ((P Λ (pullback.fst f a)).obj K)) =
        (P Λ a).map ((R Λ f).map
          ((AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId
            Λ X).hom.app K)) ≫
          (baseChangeMap Λ (IsPullback.of_hasPullback f a).toCommSq).app K) := by
  exact ⟨identity_native_unit Λ, identity_beta Λ, identity_proper_exchange Λ⟩

end AlgebraicGeometry.ProEtale.CondensedRing
