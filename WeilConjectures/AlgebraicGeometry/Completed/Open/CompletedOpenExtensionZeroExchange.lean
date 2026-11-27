/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction

/-!
# Completed extension by zero and completed pullback

For a cartesian square of open immersions, completed pullback commutes with extension by
zero along a quasi-compact open immersion on complete objects.

## Main definitions

- `AlgebraicGeometry.Scheme.cbcDerivedOpenRestrictionAdjunction`: extension by zero is left
  adjoint to restriction on derived categories of completed-ring modules.
- `AlgebraicGeometry.Scheme.cbcCompletedExchange`: the completed base-change map of
  extension by zero.
- `AlgebraicGeometry.Scheme.cbcDatumCompletedExchange`: the same map on `d.completedPull`.

## Main statements

- `AlgebraicGeometry.Scheme.cbcCompletedExchange_exists`: the completed base-change map is
  the unique map compatible with ordinary base change and the completion comparisons.
- `AlgebraicGeometry.Scheme.completedExtensionZeroComparison`: it is an isomorphism, and
  extension by zero preserves completeness.
- `AlgebraicGeometry.Scheme.completedOpenExchangeComparison`: the same on `d.completedPull`.

## Implementation details

The ordinary-to-completed comparison is a reflection onto quotient-tower complete objects
(`AdicCoefficientDatum.completedPull_reflection`). Extension by zero carries such reflections
to reflections, because its right adjoint, restriction to the open, preserves completeness.
Hence the completed base-change map is the comparison of two reflections of the same object,
so it exists, is unique and is invertible.

## References

* Stacks Project, Tags 03DI, 099N and 09BP
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

section Reflection

/-- Precomposition with an isomorphism is bijective. -/
private theorem bijective_precomp_iso {C : Type*} [Category C] {M N : C} (e : M ≅ N)
    (L : C) : Function.Bijective (fun a : N ⟶ L ↦ e.hom ≫ a) :=
  ⟨fun a b h ↦ by simpa using congrArg (e.inv ≫ ·) h,
    fun c ↦ ⟨e.inv ≫ c, by simp⟩⟩

/-- A map between the targets of two reflections of the same object, compatible with them,
is an isomorphism. -/
private theorem isIso_of_reflections {C : Type*} [Category C] (P : C → Prop)
    {M N N' : C} (f : M ⟶ N) (f' : M ⟶ N') (β : N ⟶ N') (hN : P N) (hN' : P N')
    (hf : ∀ L, P L → Function.Bijective (fun a : N ⟶ L ↦ f ≫ a))
    (hf' : ∀ L, P L → Function.Bijective (fun a : N' ⟶ L ↦ f' ≫ a))
    (h : f ≫ β = f') : IsIso β := by
  obtain ⟨γ, hγ⟩ := (hf' N hN).2 f
  change f' ≫ γ = f at hγ
  refine ⟨γ, (hf N hN).1 ?_, (hf' N' hN').1 ?_⟩
  · change f ≫ β ≫ γ = f ≫ 𝟙 N
    rw [← Category.assoc, h, hγ, Category.comp_id]
  · change f' ≫ γ ≫ β = f' ≫ 𝟙 N'
    rw [← Category.assoc, hγ, h, Category.comp_id]

end Reflection

/-- Intrinsic completeness implies quotient-tower completeness. -/
theorem cbcTowerComplete_of_completeProperty (T : Scheme.{t})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) (hK : cbcCompleteProperty d T r a ha K) :
    d.TowerComplete T K := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)
  change IsIso (intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)) at hK
  change IsIso (d.completionUnit T K)
  change intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫
      c.hom = d.completionUnit T K at hc
  rw [← hc]
  infer_instance

/-- Quotient-tower completeness implies intrinsic completeness. -/
theorem cbcCompleteProperty_of_towerComplete (T : Scheme.{t})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) (hK : d.TowerComplete T K) :
    cbcCompleteProperty d T r a ha K := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)
  change IsIso (d.completionUnit T K) at hK
  change IsIso (intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K))
  change intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫
      c.hom = d.completionUnit T K at hc
  have : IsIso (intrinsicCompletionUnit T d r a ha K
      (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫ c.hom) := by
    rw [hc]
    exact hK
  exact IsIso.of_isIso_comp_right _ c.hom

/-- Restriction of completed-ring modules to an open preserves finite limits. -/
@[instance] theorem cbcOpenRestriction_preservesFiniteLimits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    PreservesFiniteLimits (cbcOpenRestriction d j hj) := by
  let G := cbcOpenSiteFunctor j hj
  let F := cbcOpenRestriction d j hj
  let V := SheafOfModules.toSheaf (reductionModuleRing U (d.completedRing U))
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{t + 1}
    (ProEt.topology U) (ProEt.topology T)
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesFiniteLimits (F ⋙ V) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T)) ⋙ H))
  exact preservesFiniteLimits_of_reflects_of_preserves F V

/-- Restriction of completed-ring modules to an open preserves finite colimits. -/
@[instance] theorem cbcOpenRestriction_preservesFiniteColimits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    PreservesFiniteColimits (cbcOpenRestriction d j hj) := by
  let := hj
  let G := cbcOpenSiteFunctor j hj
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology T) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let F := cbcOpenRestriction d j hj
  let V := SheafOfModules.toSheaf (reductionModuleRing U (d.completedRing U))
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{t + 1}
    (ProEt.topology U) (ProEt.topology T)
  have : PreservesColimitsOfSize.{t + 1, t + 1} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{t + 1}
      (ProEt.topology U) (ProEt.topology T)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (F ⋙ V) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T)) ⋙ H))
  exact preservesFiniteColimits_of_reflects_of_preserves F V

/-- Restriction of completed-ring modules to an open is additive. -/
@[instance] theorem cbcOpenRestriction_additive {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : (cbcOpenRestriction d j hj).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction to an open, applied termwise and descended to the derived category. -/
abbrev cbcDerivedOpenRestriction {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    d.derived T ⥤ d.derived U :=
  (cbcOpenRestriction d j hj).mapDerivedCategory

/-- Derived extension by zero is left adjoint to derived restriction to the open. -/
def cbcDerivedOpenRestrictionAdjunction {U T : Scheme.{t}} (j : U ⟶ T)
    (hj : IsOpenImmersion j) :
    cbcDerivedOpenShriek d j hj ⊣ cbcDerivedOpenRestriction d j hj :=
  letI : CatCommSq ((cbcOpenShriek d j hj).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (cbcDerivedOpenShriek d j hj) :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  letI : CatCommSq ((cbcOpenRestriction d j hj).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (cbcDerivedOpenRestriction d j hj) :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  ((cbcOpenAdjunction d j hj).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (cbcDerivedOpenShriek d j hj) (cbcDerivedOpenRestriction d j hj)

/-- Restriction to an open preserves quotient-tower completeness. -/
theorem cbcDerivedOpenRestriction_towerComplete {U T : Scheme.{t}} (j : U ⟶ T)
    (hj : IsOpenImmersion j) (L : d.derived T) (hL : d.TowerComplete T L) :
    d.TowerComplete U ((cbcDerivedOpenRestriction d j hj).obj L) := by
  sorry

/-- Extension by zero along a quasi-compact open immersion preserves intrinsic
completeness. -/
theorem cbcDerivedOpenShriek_completeProperty {U T : Scheme.{t}} (j : U ⟶ T)
    (hj : IsOpenImmersion j) [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived U) (hK : cbcCompleteProperty d U r a ha K) :
    cbcCompleteProperty d T r a ha ((cbcDerivedOpenShriek d j hj).obj K) := by
  sorry

/-- Extension by zero carries a reflection onto quotient-tower complete objects to such a
reflection. -/
theorem cbcDerivedOpenShriek_map_bijective {U T : Scheme.{t}} (j : U ⟶ T)
    (hj : IsOpenImmersion j) {M N : d.derived U} (f : M ⟶ N)
    (hf : ∀ L, d.TowerComplete U L → Function.Bijective (fun a : N ⟶ L ↦ f ≫ a))
    (L : d.derived T) (hL : d.TowerComplete T L) :
    Function.Bijective
      (fun a : (cbcDerivedOpenShriek d j hj).obj N ⟶ L ↦
        (cbcDerivedOpenShriek d j hj).map f ≫ a) := by
  let adj := cbcDerivedOpenRestrictionAdjunction d j hj
  have he : (fun a : (cbcDerivedOpenShriek d j hj).obj N ⟶ L ↦
      (cbcDerivedOpenShriek d j hj).map f ≫ a) =
      (adj.homEquiv M L).symm ∘ (fun b ↦ f ≫ b) ∘ adj.homEquiv N L := by
    funext a
    simp only [Function.comp_apply]
    rw [← adj.homEquiv_naturality_left, Equiv.symm_apply_apply]
  rw [he]
  exact (adj.homEquiv M L).symm.bijective.comp
    ((hf _ (cbcDerivedOpenRestriction_towerComplete d j hj L hL)).comp
      (adj.homEquiv N L).bijective)

/-- The ordinary-to-completed pullback comparison is a reflection onto quotient-tower
complete objects. -/
theorem cbcCompletedPullbackComparison_bijective {X Y : Scheme.{t}} (g : X ⟶ Y)
    (K : d.derived Y) (L : d.derived X) (hL : d.TowerComplete X L) :
    Function.Bijective (fun a : (cbcCompletedPullback d g).obj K ⟶ L ↦
      (cbcCompletedPullbackComparison d g).app K ≫ a) := by
  have hu := cbcDatumCompletedTransport_unit d g K
  have he : (fun a : (cbcCompletedPullback d g).obj K ⟶ L ↦
      (cbcCompletedPullbackComparison d g).app K ≫ a) =
      (fun b ↦ (cbcDatumOrdinaryTransport d g).hom.app K ≫ b) ∘
        (fun b ↦ d.ordinaryToCompleted g K ≫ b) ∘
          (fun a ↦ (cbcDatumCompletedTransport d g).inv.app K ≫ a) := by
    funext a
    simp only [Function.comp_apply]
    rw [← Category.assoc, ← Category.assoc, ← hu]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [he]
  exact (bijective_precomp_iso ((cbcDatumOrdinaryTransport d g).app K) L).comp
    (((d.completedPull_reflection g).2 K L hL).comp
      (bijective_precomp_iso ((cbcDatumCompletedTransport d g).app K).symm L))

/-- Completed pullback of an intrinsically complete object is intrinsically complete. -/
theorem cbcCompletedPullback_completeProperty {X Y : Scheme.{t}} (g : X ⟶ Y)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived Y) (hK : cbcCompleteProperty d Y r a ha K) :
    cbcCompleteProperty d X r a ha ((cbcCompletedPullback d g).obj K) :=
  (completedPullback_reduction g d r a ha K (DerivedCategory.Q.objPreimage K)
    (DerivedCategory.Q.objObjPreimageIso K) hK).1 _ _

variable {U' U X' X : Scheme.{t}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g)

include sq in
/-- The base change of a quasi-compact open immersion along an open-immersion square is
quasi-compact. -/
private theorem quasiCompact_of_square [QuasiCompact j] : QuasiCompact j' := by
  have hsq : IsPullback gU j' j g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  exact MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance

/-- The ordinary exchange followed by the completion comparison of the open is a reflection
onto quotient-tower complete objects. -/
private theorem ordinaryExchange_comparison_bijective
    (K : d.derived U) (L : d.derived X') (hL : d.TowerComplete X' L) :
    Function.Bijective (fun a : (cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
        ((cbcCompletedPullback d gU).obj K) ⟶ L ↦
      ((cbcOrdinaryExchange d sq).app K ≫
        (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
          ((cbcCompletedPullbackComparison d gU).app K)) ≫ a) := by
  have : IsIso (cbcOrdinaryExchange d sq) := by
    unfold cbcOrdinaryExchange
    infer_instance
  have he : (fun a : (cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
        ((cbcCompletedPullback d gU).obj K) ⟶ L ↦
      ((cbcOrdinaryExchange d sq).app K ≫
        (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
          ((cbcCompletedPullbackComparison d gU).app K)) ≫ a) =
      (fun b ↦ (asIso ((cbcOrdinaryExchange d sq).app K)).hom ≫ b) ∘
        (fun a ↦ (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
          ((cbcCompletedPullbackComparison d gU).app K) ≫ a) := by
    funext a
    simp only [Function.comp_apply, asIso_hom, Category.assoc]
  rw [he]
  exact (bijective_precomp_iso _ L).comp
    (cbcDerivedOpenShriek_map_bijective d j' sq.isOpenImmersion' _
      (fun L' hL' ↦ cbcCompletedPullbackComparison_bijective d gU K L' hL') L hL)

/-- The completed base-change map is the unique natural map compatible with ordinary base
change and the completion comparisons. -/
theorem cbcCompletedExchange_exists [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃! β : (cbcCompleteProperty d U r a ha).ι ⋙
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ cbcCompletedPullback d g ⟶
      (cbcCompleteProperty d U r a ha).ι ⋙ cbcCompletedPullback d gU ⋙
        cbcDerivedOpenShriek d j' sq.isOpenImmersion',
      ∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        (cbcCompletedPullbackComparison d g).app
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ≫ β.app K =
          (cbcOrdinaryExchange d sq).app K.obj ≫
            (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
              ((cbcCompletedPullbackComparison d gU).app K.obj) := by
  have := quasiCompact_of_square sq
  have ht (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :
      d.TowerComplete X' ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
        ((cbcCompletedPullback d gU).obj K.obj)) :=
    cbcTowerComplete_of_completeProperty d X' r a ha _
      (cbcDerivedOpenShriek_completeProperty d j' sq.isOpenImmersion' r a ha _
        (cbcCompletedPullback_completeProperty d gU r a ha K.obj K.property))
  have hb (K : (cbcCompleteProperty d U r a ha).FullSubcategory) (L : d.derived X')
      (hL : d.TowerComplete X' L) :=
    cbcCompletedPullbackComparison_bijective d g
      ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) L hL
  choose β hβ using fun K ↦ (hb K _ (ht K)).2 ((cbcOrdinaryExchange d sq).app K.obj ≫
    (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
      ((cbcCompletedPullbackComparison d gU).app K.obj))
  beta_reduce at hβ
  refine ⟨{ app := β, naturality := ?_ }, hβ, ?_⟩
  · intro K K' f
    have h₁ := (cbcCompletedPullbackComparison d g).naturality
      ((cbcDerivedOpenShriek d j sq.isOpenImmersion).map f.hom)
    have h₂ := (cbcOrdinaryExchange d sq).naturality f.hom
    have h₃ := (cbcCompletedPullbackComparison d gU).naturality f.hom
    dsimp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj,
      ObjectProperty.ι_map] at h₂ ⊢
    refine (hb K _ (ht K')).1 (?_ : (cbcCompletedPullbackComparison d g).app
        ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ≫
          ((cbcCompletedPullback d g).map
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).map f.hom) ≫ β K') =
      (cbcCompletedPullbackComparison d g).app
        ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ≫
          (β K ≫ (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
            ((cbcCompletedPullback d gU).map f.hom)))
    rw [← Category.assoc, ← h₁, Category.assoc, hβ K', reassoc_of% (hβ K),
      ← Functor.map_comp,
      ← h₃, Functor.map_comp, reassoc_of% h₂]
  · intro β' hβ'
    ext K
    exact (hb K _ (ht K)).1 ((hβ' K).trans (hβ K).symm)

/-- The canonical completed base-change map, natural on the full complete subcategory.
It is fixed by the ordinary adjoint mate and the strict quotient completion units. -/
def cbcCompletedExchange [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :=
  (cbcCompletedExchange_exists d sq r a ha).exists.choose

/-- Completed extension by zero commutes with pullback, naturally in complete K.
It preserves completeness and both sides of the canonical exchange are complete. -/
theorem completedExtensionZeroComparison [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    IsIso (cbcCompletedExchange d sq r a ha) ∧
      (∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        cbcCompleteProperty d X r a ha
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcCompletedPullback d g).obj
              ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj)) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
              ((cbcCompletedPullback d gU).obj K.obj))) := by
  have := quasiCompact_of_square sq
  have h₁ (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :=
    cbcDerivedOpenShriek_completeProperty d j sq.isOpenImmersion r a ha K.obj K.property
  have h₂ (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :=
    cbcCompletedPullback_completeProperty d g r a ha _ (h₁ K)
  have h₃ (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :=
    cbcDerivedOpenShriek_completeProperty d j' sq.isOpenImmersion' r a ha _
      (cbcCompletedPullback_completeProperty d gU r a ha K.obj K.property)
  refine ⟨?_, fun K ↦ ⟨h₁ K, h₂ K, h₃ K⟩⟩
  have hspec := (cbcCompletedExchange_exists d sq r a ha).exists.choose_spec
  have (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :
      IsIso ((cbcCompletedExchange d sq r a ha).app K) :=
    isIso_of_reflections (d.TowerComplete X') _ _ _
      (cbcTowerComplete_of_completeProperty d X' r a ha _ (h₂ K))
      (cbcTowerComplete_of_completeProperty d X' r a ha _ (h₃ K))
      (fun L hL ↦ cbcCompletedPullbackComparison_bijective d g _ L hL)
      (fun L hL ↦ ordinaryExchange_comparison_bijective d sq K.obj L hL) (hspec K)
  exact NatIso.isIso_of_isIso_app _

/-- Canonical completed open exchange on the same presentation as proper exchange.
It is Rlim of the finite exchange followed by the extension/Rlim comparison,
transported through the strict tower counits. -/
def cbcDatumCompletedExchange [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    (cbcCompleteProperty d U r a ha).ι ⋙
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ d.completedPull g ⟶
      (cbcCompleteProperty d U r a ha).ι ⋙ d.completedPull gU ⋙
        cbcDerivedOpenShriek d j' sq.isOpenImmersion' :=
  whiskerLeft ((cbcCompleteProperty d U r a ha).ι ⋙
      cbcDerivedOpenShriek d j sq.isOpenImmersion)
      (cbcDatumCompletedTransport d g).inv ≫
    cbcCompletedExchange d sq r a ha ≫
      whiskerLeft (cbcCompleteProperty d U r a ha).ι
        (whiskerRight (cbcDatumCompletedTransport d gU).hom
          (cbcDerivedOpenShriek d j' sq.isOpenImmersion'))


/-- Quasi-compact open extension preserves intrinsic completeness, and its canonical
completed exchange is invertible and natural, with both sides intrinsically complete. -/
theorem completedOpenExchangeComparison [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    IsIso (cbcDatumCompletedExchange d sq r a ha) ∧
      (∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        cbcCompleteProperty d X r a ha
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ∧
          cbcCompleteProperty d X' r a ha
            ((d.completedPull g).obj
              ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj)) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
              ((d.completedPull gU).obj K.obj))) := by
  have hold := completedExtensionZeroComparison d sq r a ha
  have : IsIso (cbcCompletedExchange d sq r a ha) := hold.1
  constructor
  · unfold cbcDatumCompletedExchange
    infer_instance
  · have hpull {V W : Scheme.{t}} (f : V ⟶ W) (M : d.derived W)
        (hm : cbcCompleteProperty d W r a ha M) :
        cbcCompleteProperty d V r a ha ((d.completedPull f).obj M) := by
      let N := (d.completedPull f).obj M
      let C := DerivedCategory.Q.objPreimage N
      let eN : DerivedCategory.Q.obj C ≅ N := DerivedCategory.Q.objObjPreimageIso N
      let e := eN ≪≫ ((cbcDatumCompletedTransport d f).app M).symm
      have hc := (completedPullback_reduction f d r a ha M
        (DerivedCategory.Q.objPreimage M) (DerivedCategory.Q.objObjPreimageIso M) hm).1 C e
      change IsIso (e.inv ≫ DerivedCategory.Q.map
        (intrinsicCompletionComplexUnit V d r a C)) at hc
      have : IsIso (DerivedCategory.Q.map
          (intrinsicCompletionComplexUnit V d r a C)) :=
        IsIso.of_isIso_comp_left e.inv _
      change IsIso (eN.inv ≫ DerivedCategory.Q.map
        (intrinsicCompletionComplexUnit V d r a C))
      infer_instance
    have hsq : IsPullback gU j' j g :=
      IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
    have : QuasiCompact j' := MorphismProperty.of_isPullback (P := @QuasiCompact)
      hsq inferInstance
    let hi := IsPullback.id_horiz j'
    let sq' : AlgebraicGeometry.OpenImmersionSquare (𝟙 U') j' j' (𝟙 X') :=
      { toCommSq := hi.toCommSq
        isoPullback := hi.isoPullback
        hom_fst := hi.isoPullback_hom_fst
        hom_snd := hi.isoPullback_hom_snd
        isOpenImmersion := sq.isOpenImmersion'
        isOpenImmersion' := sq.isOpenImmersion' }
    intro K
    refine ⟨(hold.2 K).1, hpull g _ (hold.2 K).1, ?_⟩
    exact ((completedExtensionZeroComparison d sq' r a ha).2
      ⟨(d.completedPull gU).obj K.obj, hpull gU K.obj K.property⟩).1

end AlgebraicGeometry.Scheme
