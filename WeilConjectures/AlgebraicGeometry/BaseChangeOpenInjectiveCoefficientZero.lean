/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.LongExactSequence
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.AlgebraicGeometry.EtaleOpenInjectiveLerayEdge
import WeilConjectures.AlgebraicGeometry.BaseChangeTargetCoefficientNaturality

/-! # Open injective coefficient comparison

Source: Stacks Project, Tag 0F07, closed–open part of the proof.
(blueprint: lem-sbc-open-injective-coefficient-zero)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private lemma module_comp_apply {R : Type*} [Ring R] {M N P : ModuleCat R}
    (f : M ⟶ N) (g : N ⟶ P) (z : M) :
    (f ≫ g).hom z = g.hom (f.hom z) := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma adjoint_coefficient_cancel
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (F : C) (J : D) (α : L.obj F ⟶ J) :
    L.map (adj.unit.app F ≫ R.map α) ≫ adj.counit.app J = α := by
  have hc := adj.counit.naturality α
  simp only [Functor.comp_map, Functor.id_map] at hc
  rw [L.map_comp, Category.assoc, hc, ← Category.assoc]
  exact (congrArg (fun k ↦ k ≫ α) (adj.left_triangle_components F)).trans
    (Category.id_comp α)

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)

/-- A class that is a base-change image on V maps to zero after the open injective
coefficient embedding. This is the Leray part of the closed–open argument.

Source: Stacks Project, Tag 0F07, open summand in condition (3).
(blueprint: lem-sbc-open-injective-coefficient-zero)

Proof: put J = Injective.under (F restricted to V). The degree q source for J
vanishes since J is injective and q is positive. Naturality therefore sends the
assumed base-change image on V to zero in R^q(h composed with j')_* e_V^* J.
Apply the universal lower-degree hypothesis after the preliminary base change to T,
to the quasi-compact separated open immersion j:V -> T. In degree zero it identifies
e^* j_* J with j'_* e_V^* J. In degrees 1 through q-1 it implies that R^a j'_*
e_V^* J vanishes, since R^a j_* J vanishes by injectivity. The Leray edge map
R^q h_* e^* j_* J -> R^q(h composed with j')_* e_V^* J is consequently injective.
Compatibility of the edge map with the coefficient unit and target transition
identifies the image of the class under this injection with the zero just obtained.
Injectivity on stalks proves the asserted vanishing. The empty open causes no exception.
-/
theorem baseChange_open_injective_coefficient_eq_zero [IsAffine S]
    (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, UniversalBaseChangeProperty Λ p q')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    {T' : Scheme.{u}} (f : T' ⟶ T)
    [CompactSpace T'] [QuasiSeparatedSpace T']
    (ζ : baseChangeTargetStalk Λ p g q F x (Over.mk f))
    (V : T'.Opens) (hV : IsCompact (V : Set T'))
    (hζ : (baseChangeTargetStalkMap Λ p g q F x
      (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f)).hom ζ ∈
        Set.range (baseChangeStalkMap Λ p g q F x (Over.mk (V.ι ≫ f))).hom) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
      ((baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p)
        (pullback.snd (f ≫ g) p) q).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.ι).unit.app
          (((f)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
            ((V.ι)_*[ModuleCat.{u + 1} Λ]).map
              (Injective.ι (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj
                (((f)^*[ModuleCat.{u + 1} Λ]).obj F)))))).hom ζ = 0 := by
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  let F' := ((f)^*[ModuleCat.{u + 1} Λ]).obj F
  let J := Injective.under (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj F')
  let β : ((V.ι)^*[ModuleCat.{u + 1} Λ]).obj F' ⟶ J := Injective.ι _
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.ι
  let G := ((V.ι)_*[ModuleCat.{u + 1} Λ]).obj J
  let η : F' ⟶ G := adj.unit.app F' ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map β
  let e := pullback.fst (f ≫ g) p
  let h := pullback.snd (f ≫ g) p
  let eV := pullback.fst ((V.ι ≫ f) ≫ g) p
  let hYV := pullback.snd ((V.ι ≫ f) ≫ g) p
  let a : pullback ((V.ι ≫ f) ≫ g) p ⟶ pullback (f ≫ g) p :=
    pullback.lift (eV ≫ V.ι) hYV (by
      dsimp [eV, hYV]
      rw [Category.assoc, Category.assoc]
      exact pullback.condition)
  have wa : a ≫ e = eV ≫ V.ι := pullback.lift_fst _ _ _
  have wh : a ≫ h = hYV := pullback.lift_snd _ _ _
  let B := baseChangeTargetFunctor Λ e h q
  let BV := baseChangeTargetFunctor Λ eV hYV q
  let fiber := (X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let : fiber.Additive := (X.uliftPointSmallEtale x).sheafFiber_additive
  let : PreservesFiniteLimits fiber :=
    inferInstanceAs (PreservesFiniteLimits
      ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)))
  let t (K : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    baseChangeTargetTransition Λ e h q V.ι a eV hYV wa wh K
  let E : B.obj G ⟶ BV.obj J := t G ≫ BV.map (adj.counit.app J)
  have hmono : Mono E := by
    let : CompactSpace V := isCompact_iff_compactSpace.mp hV
    let : QuasiCompact V.ι := inferInstance
    have outer : IsPullback (a ≫ h) eV p (V.ι ≫ (f ≫ g)) := by
      rw [wh]
      simpa only [Category.assoc] using
        (IsPullback.of_hasPullback ((V.ι ≫ f) ≫ g) p).flip
    have hs : IsPullback eV a V.ι e :=
      (outer.of_right wa (IsPullback.of_hasPullback (f ≫ g) p).flip).flip
    exact baseChangeTargetTransition_counit_mono Λ h e V.ι eV a hYV wa wh hs q hq
      (fun n hn ↦ hprev n hn (f ≫ g) h e
        (IsPullback.of_hasPullback (f ≫ g) p).flip) J
  let : Mono E := hmono
  have hi : Function.Injective (fiber.map E).hom :=
    (ModuleCat.mono_iff_injective _).mp (by infer_instance)
  let c := (upperStarComp (ModuleCat.{u + 1} Λ) V.ι f (V.ι ≫ f) rfl).app F
  let γ : ((V.ι ≫ f)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ J := c.hom ≫ β
  have hβ : ((V.ι)^*[ModuleCat.{u + 1} Λ]).map η ≫ adj.counit.app J = β :=
    adjoint_coefficient_cancel adj F' J β
  have hc : c.inv ≫ γ = β := by
    dsimp [γ]
    rw [← Category.assoc, c.inv_hom_id]
    exact Category.id_comp β
  have hn : B.map η ≫ E = t F' ≫ BV.map β := by
    have hn' := target_transition_naturality Λ e h q V.ι a eV hYV wa wh η
    change (B.map η ≫ t G) ≫ BV.map (adj.counit.app J) = _
    rw [hn', Category.assoc, ← BV.map_comp, hβ]
  let y := Classical.choose hζ
  have hy := Classical.choose_spec hζ
  have hz : (fiber.map (BV.map γ)).hom
      ((baseChangeTargetStalkMap Λ p g q F x
        (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f)).hom ζ) = 0 := by
    rw [← hy]
    have hzero := baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ
      (IsPullback.of_hasPullback ((V.ι ≫ f) ≫ g) p) (q := q) (by lia) γ
    have hfzero := congrArg fiber.map hzero
    rw [fiber.map_comp, fiber.map_zero] at hfzero
    exact congrArg (fun k ↦ k.hom y) hfzero
  have hsmap : baseChangeTargetStalkMap Λ p g q F x
      (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f) =
      fiber.map (t F' ≫ BV.map c.inv) := by
    rfl
  have hsquare : fiber.map (B.map η) ≫ fiber.map E =
      baseChangeTargetStalkMap Λ p g q F x
        (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f) ≫
          fiber.map (BV.map γ) := by
    rw [hsmap, ← fiber.map_comp, ← fiber.map_comp, hn]
    congr 1
    calc
      t F' ≫ BV.map β = t F' ≫ BV.map (c.inv ≫ γ) :=
        congrArg (fun k ↦ t F' ≫ BV.map k) hc.symm
      _ = (t F' ≫ BV.map c.inv) ≫ BV.map γ := by
        rw [BV.map_comp]
        exact (Category.assoc _ _ _).symm
  have hzero : (baseChangeTargetStalkMap Λ p g q F x
      (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f) ≫
        fiber.map (BV.map γ)).hom ζ = 0 := by
    rw [module_comp_apply]
    exact hz
  rw [← hsquare, module_comp_apply] at hzero
  change (fiber.map (B.map η)).hom ζ = 0
  apply hi
  exact hzero.trans ((fiber.map E).hom.map_zero).symm



end AlgebraicGeometry.Etale
