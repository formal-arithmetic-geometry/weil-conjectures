/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# ProEtaleInverseImageComparisonCoherence

Source: blueprint direct-image comparison, Stacks Tags 09A6 and 0B65.
(blueprint: lem-pe-inverse-image-comparison-coherence).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The identity and composition equations for the inverse-image square.
Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-thm-pe-direct-image-comparison/_section.md, proof steps 1 and 6; Stacks Tags 09A6 and 0B65.
(blueprint: lem-pe-inverse-image-comparison-coherence).

Proof: The right-image restrictions agree on sections over every chosen fibre product. Their
identity
and associativity equations follow from the universal properties of these products. Apply
conjugateIsoEquiv to the composite adjunctions; its injectivity transfers those equations to
inverse images. The comparison used here is the inverse of comparisonCoefficientPullbackIso.
Cancel each invertible comparison component to reverse the orientation of the existing coherence
equations. Identify the canonical identity and composition isomorphisms by their conjugates,
which are exactly the specified direct-image fibre-product identifications. This proves both
equations for arbitrary commutative coefficients, including identity arrows, empty schemes and
the zero ring. -/
theorem inverseImageComparisonCoherence
    (Λ : Type u) [CommRing Λ] {X Y : Scheme.{u}} (_g : X ⟶ Y) :
    (∀ (U : Scheme.{u})
          (F : Sheaf U.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))),
        (comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) (𝟙 U)).hom.app F ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).map
            ((Etale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).hom.app F) =
        (ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).obj F)) ∧
    (∀ {U V W : Scheme.{u}} (f : U ⟶ V) (h : V ⟶ W)
          (F : Sheaf W.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))),
        (comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) (f ≫ h)).hom.app F ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).map
            ((Etale.upperStarComp
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f h).hom.app F) =
        (ProEtale.upperStarComp
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f h).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) W).obj F) ≫
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f).map
            ((comparisonUpperStarCompUpperStarIso
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) h).hom.app F) ≫
          (comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f).hom.app
              ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) h).obj F)) := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
  have hc := comparison_pullback_coherent.2.2 (ULift.{u + 1, u} Λ)
  constructor
  · intro U F
    have h := hc.1 U F
    change (comparisonUpperStarCompUpperStarIso A (𝟙 U)).inv.app F ≫
      (upperStarId A U).hom.app ((comparisonUpperStar A U).obj F) =
      (comparisonUpperStar A U).map ((Etale.upperStarId A U).hom.app F) at h
    rw [← h, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  · intro U V W f h F
    have hc' := hc.2.1 U V W f h F
    change (comparisonUpperStar A U).map ((Etale.upperStarComp A f h).hom.app F) ≫
      (comparisonUpperStarCompUpperStarIso A f).inv.app ((Etale.upperStar A h).obj F) ≫
      (upperStar A f).map ((comparisonUpperStarCompUpperStarIso A h).inv.app F) =
      (comparisonUpperStarCompUpperStarIso A (f ≫ h)).inv.app F ≫
      (upperStarComp A f h).hom.app ((comparisonUpperStar A W).obj F) at hc'
    apply (cancel_epi ((comparisonUpperStarCompUpperStarIso A (f ≫ h)).inv.app F)).mp
    dsimp only [A] at hc' ⊢
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← reassoc_of% hc']
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

end AlgebraicGeometry.ProEtale
