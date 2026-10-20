/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower
import Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage
import Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientSquare
import Sheaf.AlgebraicGeometry.UpperStarCoefficientSquare
import WeilConjectures.AlgebraicGeometry.BaseChangePullbackComparisonComp
import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.TransitionComposition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Naturality of the canonical target sheaf comparison

Source: Stacks Project Tags 0F07 and 09Z1.
(blueprint: lem-sbc-target-sheaf-comparison-naturality)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] lowerStarPlusTransition

variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)

/-- The canonical map from the iterated pullback to the single pullback. -/
noncomputable def targetPullbackComparison (U : Over T) :
    ((Over.pullback (pullback.fst g p)).obj U).left ⟶ pullback (U.hom ≫ g) p :=
  pullback.lift (pullback.fst U.hom (pullback.fst g p))
    (pullback.snd U.hom (pullback.fst g p) ≫ pullback.snd g p)
    (by
      rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
        pullback.condition])

/-- Projection of the canonical comparison to X.
(blueprint: lem-sbc-target-sheaf-comparison-naturality) -/
lemma targetPullbackComparison_snd (U : Over T) :
    targetPullbackComparison p g U ≫ pullback.snd (U.hom ≫ g) p =
      ((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p := by
  unfold targetPullbackComparison
  exact pullback.lift_snd _ _ _

/-- The explicit inverse of the iterated-pullback comparison. -/
noncomputable def targetPullbackComparisonInv (U : Over T) :
    pullback (U.hom ≫ g) p ⟶ ((Over.pullback (pullback.fst g p)).obj U).left :=
  pullback.lift (pullback.fst (U.hom ≫ g) p)
    (pullback.lift (pullback.fst (U.hom ≫ g) p ≫ U.hom)
      (pullback.snd (U.hom ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition))
    (by exact (pullback.lift_fst _ _ _).symm)

lemma targetPullbackComparison_hom_inv (U : Over T) :
    targetPullbackComparison p g U ≫ targetPullbackComparisonInv p g U = 𝟙 _ := by
  apply pullback.hom_ext
  · unfold targetPullbackComparison targetPullbackComparisonInv
    simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext (f := g) (g := p)
    · unfold targetPullbackComparison targetPullbackComparisonInv
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
      rw [pullback.lift_fst_assoc]
      exact pullback.condition (f := U.hom) (g := pullback.fst g p)
    · unfold targetPullbackComparison targetPullbackComparisonInv
      simp only [Category.assoc, pullback.lift_snd, Category.id_comp]

lemma targetPullbackComparison_inv_hom (U : Over T) :
    targetPullbackComparisonInv p g U ≫ targetPullbackComparison p g U = 𝟙 _ := by
  apply pullback.hom_ext
  · unfold targetPullbackComparison targetPullbackComparisonInv
    simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
  · unfold targetPullbackComparison targetPullbackComparisonInv
    rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      pullback.lift_snd, Category.id_comp]

noncomputable def targetPullbackComparisonIso (U : Over T) :
    ((Over.pullback (pullback.fst g p)).obj U).left ≅ pullback (U.hom ≫ g) p where
  hom := targetPullbackComparison p g U
  inv := targetPullbackComparisonInv p g U
  hom_inv_id := targetPullbackComparison_hom_inv p g U
  inv_hom_id := targetPullbackComparison_inv_hom p g U

variable (Λ : Type (u + 1)) [CommRing Λ] (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The coefficient comparison on the iterated pullback, with its canonical direction. -/
noncomputable def targetPullbackCoefficientIso (U : Over T) :
    ((targetPullbackComparison p g U)^*[ModuleCat.{u + 1} Λ]).obj
      (((pullback.fst (U.hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
        (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)) ≅
      ((((Over.pullback (pullback.fst g p)).obj U).hom)^*[ModuleCat.{u + 1} Λ]).obj
        (((pullback.fst g p)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  ((targetPullbackComparison p g U)^*[ModuleCat.{u + 1} Λ]).mapIso
      ((upperStarComp (ModuleCat.{u + 1} Λ) (pullback.fst (U.hom ≫ g) p) U.hom).app F).symm
    ≪≫ ((upperStarComp (ModuleCat.{u + 1} Λ) (targetPullbackComparison p g U)
      (pullback.fst (U.hom ≫ g) p ≫ U.hom)).app F).symm
    ≪≫ eqToIso (by
      apply congrArg (fun k ↦ ((k)^*[ModuleCat.{u + 1} Λ]).obj F)
      unfold targetPullbackComparison
      rw [pullback.lift_fst_assoc]
      exact pullback.condition (f := U.hom) (g := pullback.fst g p))
    ≪≫ (upperStarComp (ModuleCat.{u + 1} Λ)
      ((Over.pullback (pullback.fst g p)).obj U).hom (pullback.fst g p)).app F

lemma targetPullbackTransition_isIso (U : Over T)
    (K : DerivedCategory.Plus
      (Sheaf (pullback (U.hom ≫ g) p).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (lowerStarPlusTransition Λ (targetPullbackComparison p g U)
      (pullback.snd (U.hom ≫ g) p)
      (((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p)
      (by unfold targetPullbackComparison; exact pullback.lift_snd _ _ _) K) := by
  let a := targetPullbackComparison p g U
  let b := targetPullbackComparisonInv p g U
  let h := pullback.snd (U.hom ≫ g) p
  let h' := ((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p
  have w : a ≫ h = h' := by
    dsimp only [a, h, h']
    unfold targetPullbackComparison
    exact pullback.lift_snd _ _ _
  let sq : CommSq a h' h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  rw [lowerStarPlusTransition_eq_baseChange Λ a h h' w sq K]
  have := isIso_baseChange_app_of_inverses Λ sq b (𝟙 X)
    (targetPullbackComparison_hom_inv p g U) (targetPullbackComparison_inv_hom p g U)
    (Category.id_comp _) (Category.id_comp _) K
  infer_instance

/-- Canonical sheaf comparison via exact single complexes and pullback associativity. -/
noncomputable def baseChangeTargetSheafComparison (U : Over T) :
    (baseChangeTargetFunctor Λ (pullback.fst (U.hom ≫ g) p)
      (pullback.snd (U.hom ≫ g) p) q).obj (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F) ≅
    higherDirectImage Λ
      (((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p) q
      (((((Over.pullback (pullback.fst g p)).obj U).hom)^*[ModuleCat.{u + 1} Λ]).obj
        (((pullback.fst g p)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
  let a := targetPullbackComparison p g U
  let h := pullback.snd (U.hom ≫ g) p
  let h' := ((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p
  let w : a ≫ h = h' := targetPullbackComparison_snd p g U
  let C := ((pullback.fst (U.hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  let R := R+((h')_*[ModuleCat.{u + 1} Λ])
  let t := higherDirectImageTransition Λ a h h' w q C
  have ht : IsIso t := higherDirectImageTransition_isIso_of_lower Λ a h h' w q C
    (targetPullbackTransition_isIso p g Λ U _)
  let I := baseChangeTargetFunctorHigherImageIso Λ (pullback.fst (U.hom ≫ g) p) h q
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
  let M := higherDirectImageMapIso Λ h' q (targetPullbackCoefficientIso p g Λ F U)
  exact I ≪≫ (@asIso _ _ _ _ t ht) ≪≫ M


private lemma comparison_hom (U : Over T) :
    (baseChangeTargetSheafComparison p g Λ q F U).hom =
      (baseChangeTargetFunctorHigherImageIso Λ (pullback.fst (U.hom ≫ g) p)
        (pullback.snd (U.hom ≫ g) p) q
          (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)).hom ≫
      higherDirectImageTransition Λ (targetPullbackComparison p g U)
        (pullback.snd (U.hom ≫ g) p)
        (((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p)
        (targetPullbackComparison_snd p g U) q
        (((pullback.fst (U.hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
          (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      higherDirectImageMap Λ
        (((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p) q
        (targetPullbackCoefficientIso p g Λ F U).hom := by
  dsimp only [baseChangeTargetSheafComparison]
  simp only [Iso.trans_hom, asIso_hom, higherDirectImageMapIso_hom_eq]

private lemma paste_comparisons
    {C : Type*} [Category C] {A B D E F G H I J K L : C}
    (r₁ : A ⟶ B) (r₂ : B ⟶ D) (iU : D ⟶ E) (iV : A ⟶ F)
    (t₁ : F ⟶ G) (t₂ : G ⟶ E) (u₁ : E ⟶ H) (u₂ : H ⟶ I)
    (v₁ : F ⟶ J) (v₂ : J ⟶ K) (s₁ : K ⟶ L) (s₂ : L ⟶ I)
    (cU : D ⟶ I) (cV : A ⟶ K) (s : K ⟶ I)
    (hU : cU = iU ≫ u₁ ≫ u₂) (hV : cV = iV ≫ v₁ ≫ v₂)
    (hn : r₁ ≫ r₂ ≫ iU = iV ≫ t₁ ≫ t₂)
    (hs : (t₁ ≫ t₂) ≫ (u₁ ≫ u₂) = (v₁ ≫ v₂) ≫ (s₁ ≫ s₂))
    (ho : s = s₁ ≫ s₂) : (r₁ ≫ r₂) ≫ cU = cV ≫ s := by
  rw [hU, hV, ho]
  set_option backward.isDefEq.respectTransparency false in
    simp only [Category.assoc] at hn hs ⊢
  rw [reassoc_of% hn, hs]

/-- The explicit target sheaf comparison commutes with canonical restriction.

Source: Stacks Project Tag 0F07, coefficient identification preceding condition (2),
and Tag 09Z1, canonical restriction maps.
(blueprint: lem-sbc-target-sheaf-comparison-naturality)

Proof: Expand both transitions as homology of the derived unit-composition-counit
maps. The canonical map from an iterated pullback to a single pullback commutes
with a morphism over T: check its two projections, then use pullback uniqueness.
The lower-star transitions are natural in the coefficient object, by naturality
of the derived adjunction unit and counit. Their composition is the transition
of the composite triangle, by mate pasting and the triangle identities. These
facts move the transport along the canonical scheme isomorphism past the
transition. The inverse-image composition isomorphisms on coefficients satisfy
associativity; their derived single-complex comparisons respect this composition.
Consequently the remaining coefficient maps agree. Apply degree-q homology;
this argument applies to all integer q, including negative degrees.
-/
theorem baseChangeTargetSheafComparison_naturality {U V : Over T} (φ : U ⟶ V) :
    (baseChangeTargetTransition Λ (pullback.fst (V.hom ≫ g) p)
      (pullback.snd (V.hom ≫ g) p) q φ.left
      (pullback.lift (pullback.fst (U.hom ≫ g) p ≫ φ.left)
        (pullback.snd (U.hom ≫ g) p)
        (by rw [Category.assoc, ← Category.assoc φ.left, Over.w]
            exact pullback.condition))
      (pullback.fst (U.hom ≫ g) p) (pullback.snd (U.hom ≫ g) p)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
      (baseChangeTargetFunctor Λ (pullback.fst (U.hom ≫ g) p)
        (pullback.snd (U.hom ≫ g) p) q).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
          (Over.w φ).symm).inv.app F)) ≫
        (baseChangeTargetSheafComparison p g Λ q F U).hom =
      (baseChangeTargetSheafComparison p g Λ q F V).hom ≫
        higherDirectImageOverMap Λ (pullback.snd g p)
          (((pullback.fst g p)^*[ModuleCat.{u + 1} Λ]).obj F) q
          ((Over.pullback (pullback.fst g p)).map φ) := by
  let A := ModuleCat.{u + 1} Λ
  let eV := pullback.fst (V.hom ≫ g) p
  let eU := pullback.fst (U.hom ≫ g) p
  let hV := pullback.snd (V.hom ≫ g) p
  let hU := pullback.snd (U.hom ≫ g) p
  let PV := (Over.pullback (pullback.fst g p)).obj V
  let PU := (Over.pullback (pullback.fst g p)).obj U
  let a : pullback (U.hom ≫ g) p ⟶ pullback (V.hom ≫ g) p :=
    pullback.lift (eU ≫ φ.left) hU
      (by
        dsimp only [eU, hU]
        rw [Category.assoc, ← Category.assoc φ.left, Over.w]
        exact pullback.condition)
  let ψ := (Over.pullback (pullback.fst g p)).map φ
  let b : PU.left ⟶ PV.left := ψ.left
  let cV := targetPullbackComparison p g V
  let cU := targetPullbackComparison p g U
  have wa : a ≫ eV = eU ≫ φ.left := pullback.lift_fst _ _ _
  have wh : a ≫ hV = hU := pullback.lift_snd _ _ _
  have wV : cV ≫ hV = PV.hom ≫ pullback.snd g p := by
    exact targetPullbackComparison_snd p g V
  have wU : cU ≫ hU = PU.hom ≫ pullback.snd g p := by
    exact targetPullbackComparison_snd p g U
  have wk : b ≫ PV.hom = PU.hom := Over.w ψ
  have wb : b ≫ (PV.hom ≫ pullback.snd g p) = PU.hom ≫ pullback.snd g p := by
    rw [← Category.assoc, wk]
  have ws : cU ≫ a = b ≫ cV := by
    apply pullback.hom_ext
    · dsimp only [cU, cV, a, b, ψ, eU, eV, hU, hV]
      unfold targetPullbackComparison
      simp only [Category.assoc, pullback.lift_fst, Over.pullback_map_left]
      simp only [pullback.lift_fst_assoc]
    · dsimp only [cU, cV, a, b, ψ, eU, eV, hU, hV]
      unfold targetPullbackComparison
      simp only [Category.assoc, pullback.lift_snd, Over.pullback_map_left]
      simp only [pullback.lift_snd_assoc]
  have wCV : cV ≫ (eV ≫ V.hom) = PV.hom ≫ pullback.fst g p := by
    dsimp only [cV, eV, PV]
    unfold targetPullbackComparison
    rw [pullback.lift_fst_assoc]
    exact pullback.condition
  have wCU : cU ≫ (eU ≫ U.hom) = PU.hom ≫ pullback.fst g p := by
    dsimp only [cU, eU, PU]
    unfold targetPullbackComparison
    rw [pullback.lift_fst_assoc]
    exact pullback.condition
  let FV := ((eV)^*[A]).obj (((V.hom)^*[A]).obj F)
  let FU := ((eU)^*[A]).obj (((U.hom)^*[A]).obj F)
  let G := ((pullback.fst g p)^*[A]).obj F
  let GV := ((PV.hom)^*[A]).obj G
  let GU := ((PU.hom)^*[A]).obj G
  let d : ((a)^*[A]).obj FV ⟶ FU :=
    (upperStarComp A a eV).inv.app (((V.hom)^*[A]).obj F) ≫
      (upperStarComp A eU φ.left (a ≫ eV) wa).hom.app (((V.hom)^*[A]).obj F) ≫
      ((eU)^*[A]).map ((upperStarComp A φ.left V.hom U.hom (Over.w φ).symm).inv.app F)
  let fV := (targetPullbackCoefficientIso p g Λ F V).hom
  let fU := (targetPullbackCoefficientIso p g Λ F U).hom
  let e := (upperStarComp A b PV.hom PU.hom wk.symm).inv.app G
  have hc := upperStar_coefficient_square Λ V.hom U.hom φ.left (Over.w φ)
    eV eU a wa (pullback.fst g p) PV.hom PU.hom cV cU b wCV wCU wk ws F
  have hc' : (upperStarComp A cU a).hom.app FV ≫ ((cU)^*[A]).map d ≫ fU =
      (upperStarComp A b cV (cU ≫ a) ws).hom.app FV ≫ ((b)^*[A]).map fV ≫ e := by
    set_option backward.isDefEq.respectTransparency false in
      simpa only [fU, fV, d, e, FV, G, A, cU, cV, PU, PV, eU, eV,
        targetPullbackCoefficientIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Iso.app_hom, Iso.app_inv, eqToIso.hom, Functor.comp_obj, Category.assoc] using hc
  let ringInst : CommRing Λ := inferInstance
  let YV := pullback (V.hom ≫ g) p
  let YU := pullback (U.hom ≫ g) p
  let ZV := PV.left
  let ZU := PU.left
  let kV := PV.hom ≫ pullback.snd g p
  let kU := PU.hom ≫ pullback.snd g p
  have hs := higherDirectImage_coefficient_square Λ a b cV cU hV hU kV kU
    wh wb wV wU ws q FV FU GV GU d fV fU e hc'
  have hn := baseChangeTargetTransition_higherImage Λ eV hV q φ.left a eU hU wa wh
    (((V.hom)^*[A]).obj F) (((U.hom)^*[A]).obj F)
    ((upperStarComp A φ.left V.hom U.hom (Over.w φ).symm).inv.app F)
  have hCU := comparison_hom p g Λ q F U
  have hCV := comparison_hom p g Λ q F V
  have ho := higherDirectImageOverMap_eq Λ (pullback.snd g p) G q ψ
  bc_paste paste_comparisons using hCU hCV hn hs ho

end AlgebraicGeometry.Etale
