/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
import Sheaf.AlgebraicGeometry.BaseChangePullbackComparisonComp
import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
import Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp
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

variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)

/-- The canonical map from the iterated pullback to the single pullback. -/
noncomputable def targetPullbackComparison (U : Over T) :
    ((Over.pullback (pullback.fst g p)).obj U).left ⟶ pullback (U.hom ≫ g) p :=
  pullback.lift (pullback.fst U.hom (pullback.fst g p))
    (pullback.snd U.hom (pullback.fst g p) ≫ pullback.snd g p)
    (by
      rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
        pullback.condition])

/-- The explicit inverse of the iterated-pullback comparison. -/
noncomputable def targetPullbackComparisonInv (U : Over T) :
    pullback (U.hom ≫ g) p ⟶ ((Over.pullback (pullback.fst g p)).obj U).left :=
  pullback.lift (pullback.fst (U.hom ≫ g) p)
    (pullback.lift (pullback.fst (U.hom ≫ g) p ≫ U.hom)
      (pullback.snd (U.hom ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition))
    (by simp)

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
  let w : a ≫ h = h' := by
    dsimp only [a, h, h']
    unfold targetPullbackComparison
    exact pullback.lift_snd _ _ _
  let C := ((pullback.fst (U.hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  let R := R+((h')_*[ModuleCat.{u + 1} Λ])
  have := targetPullbackTransition_isIso p g Λ U
    ((DerivedCategory.Plus.singleFunctor _ 0).obj C)
  let t := higherDirectImageTransition Λ a h h' w q C
  have : IsIso t := by
    dsimp [t, higherDirectImageTransition]
    infer_instance
  exact (baseChangeTargetFunctorIso Λ (pullback.fst (U.hom ≫ g) p) h q).app _
    ≪≫ asIso t
    ≪≫ (DerivedCategory.Plus.singleFunctor _ 0 ⋙ R ⋙ H).mapIso
      (targetPullbackCoefficientIso p g Λ F U)

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
          ((Over.pullback (pullback.fst g p)).map φ) := by sorry

end AlgebraicGeometry.Etale
