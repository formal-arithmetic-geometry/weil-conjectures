/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.RootTowerCoordinateFace
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coherence of the canonical scalar direct-image mate

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-direct-image.proof.md, Formal properties and Preservation;
det-prop-scalar-six-pullback.proof.md, clauses (1) and (3).
(blueprint: lem-sfb-scalar-direct-image-mate-coherence).

All functors act on ordinary unbounded derived categories of internal modules.
The exact inverse-image presentation uses the published derived adjunction and
the adjunction-normalized direct-image compositor from the test-map interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem scalarMate_comp
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    [Category D₁] [Category D₂] [Category D₃]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (a₁ : L₁ ⊣ R₁)
    {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂} (a₂ : L₂ ⊣ R₂)
    {M₁ : D₁ ⥤ D₂} {S₁ : D₂ ⥤ D₁} (b₁ : M₁ ⊣ S₁)
    {M₂ : D₂ ⥤ D₃} {S₂ : D₃ ⥤ D₂} (b₂ : M₂ ⊣ S₂)
    {L : C₁ ⥤ C₃} {R : C₃ ⥤ C₁} (a : L ⊣ R)
    {M : D₁ ⥤ D₃} {S : D₃ ⥤ D₁} (b : M ⊣ S)
    {F : C₁ ⥤ D₁} {G : C₂ ⥤ D₂} {H : C₃ ⥤ D₃}
    (α : TwoSquare F L₁ M₁ G) (β : TwoSquare G L₂ M₂ H)
    (γ : TwoSquare F L M H) (u : L ≅ L₁ ⋙ L₂) (v : M ≅ M₁ ⋙ M₂)
    (ho : ∀ K : C₁, M₂.map (α.natTrans.app K) ≫ β.natTrans.app (L₁.obj K) =
      v.inv.app (F.obj K) ≫ γ.natTrans.app K ≫ H.map (u.hom.app K)) (K : C₃) :
    (mateEquiv a₁ b₁ α).natTrans.app (R₂.obj K) ≫
        S₁.map ((mateEquiv a₂ b₂ β).natTrans.app K) ≫
        (conjugateIsoEquiv (b₁.comp b₂) b v).hom.app (H.obj K) =
      F.map ((conjugateIsoEquiv (a₁.comp a₂) a u).hom.app K) ≫
        (mateEquiv a b γ).natTrans.app K := by
  have hs : (TwoSquare.vComp α β).whiskerLeft u.inv = γ.whiskerRight v.inv := by
    ext T
    have ht := congrArg (fun z ↦ z ≫ H.map (u.inv.app T)) (ho T)
    simp only [Category.assoc] at ht
    rw [← H.map_comp, Iso.hom_inv_id_app, H.map_id] at ht
    have htid := congrArg (fun z ↦ v.inv.app (F.obj T) ≫ z)
      (Category.comp_id (γ.natTrans.app T))
    have ht' := ht.trans htid
    simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht'
  have hm := congrArg (mateEquiv a (b₁.comp b₂)) hs
  rw [conjugateEquiv_mateEquiv_vcomp a (a₁.comp a₂) (b₁.comp b₂),
    mateEquiv_conjugateEquiv_vcomp a b (b₁.comp b₂),
    mateEquiv_hcomp a₁ b₁ a₂ b₂] at hm
  have hc := congrArg (fun z ↦ z.natTrans.app K) hm
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hc
  rw [← conjugateIsoEquiv_apply_inv, ← conjugateIsoEquiv_apply_inv] at hc
  apply (cancel_epi (F.map ((conjugateIsoEquiv (a₁.comp a₂) a u).inv.app K))).mp
  have ht := congrArg
    (fun z ↦ z ≫ (conjugateIsoEquiv (b₁.comp b₂) b v).hom.app (H.obj K)) hc
  simp only [Category.assoc] at ht
  rw [Iso.inv_hom_id_app] at ht
  have ht' := ht.trans (Category.comp_id ((mateEquiv a b γ).natTrans.app K))
  simpa only [Category.assoc, ← F.map_comp_assoc,
    Iso.inv_hom_id_app, F.map_id, Category.id_comp] using ht'


private theorem scalarMate_coefficients
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {L₁ : C ⥤ C'} {R₁ : C' ⥤ C} (a₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ D'} {R₂ : D' ⥤ D} (a₂ : L₂ ⊣ R₂)
    {L₃ : E ⥤ E'} {R₃ : E' ⥤ E} (a₃ : L₃ ⊣ R₃)
    {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ E} {G' : D' ⥤ E'}
    {H : C ⥤ E} {H' : C' ⥤ E'}
    (α : TwoSquare F L₁ L₂ F') (β : TwoSquare G L₂ L₃ G')
    (γ : TwoSquare H L₁ L₃ H') (u : F ⋙ G ≅ H) (v : F' ⋙ G' ≅ H')
    (ho : ∀ T : C, β.natTrans.app (F.obj T) ≫ G'.map (α.natTrans.app T) ≫
      v.hom.app (L₁.obj T) = L₃.map (u.hom.app T) ≫ γ.natTrans.app T) (K : C') :
    G.map ((mateEquiv a₁ a₂ α).natTrans.app K) ≫
        (mateEquiv a₂ a₃ β).natTrans.app (F'.obj K) ≫ R₃.map (v.hom.app K) =
      u.hom.app (R₁.obj K) ≫ (mateEquiv a₁ a₃ γ).natTrans.app K := by
  have hs : ((TwoSquare.hComp α β).whiskerTop u.inv).whiskerBottom v.hom = γ := by
    ext T
    have ht := congrArg (fun z ↦ L₃.map (u.inv.app T) ≫ z) (ho T)
    simp only [← L₃.map_comp_assoc, Iso.inv_hom_id_app, L₃.map_id,
      Category.id_comp] at ht
    simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht
  have hm := mateEquiv_whiskerTop_whiskerBottom a₁ a₃ (TwoSquare.hComp α β)
    u.inv v.hom
  rw [hs, mateEquiv_vcomp a₁ a₂ a₃] at hm
  have hc := congrArg (fun z ↦ z.natTrans.app K) hm
  apply (cancel_epi (u.inv.app (R₁.obj K))).mp
  change _ = u.inv.app _ ≫ u.hom.app _ ≫ _
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc] using hc.symm



/-- The canonically normalized pullback comparisons already supplied by scalarSixPullback.
The theta field is uniquely fixed by thetaNormalization to scalarSixPullHom, so this
choice does not select an unspecified map or a new scalar-extension construction.
All other fields are proofs of its prescribed coherence equations.
Source: blueprint scalar pullback (1), (3)
(blueprint: lem-sfb-scalar-direct-image-mate-coherence). -/
def scalarDirectImagePullbackData : ScalarSixPullbackData.{u} :=
  Classical.choose (Classical.choose_spec scalarSixPullback)

/-- The canonical direct-image mate of c_f = theta_f inverse. At K the mate formula is
eta' at T_Y R_f K, followed by R'_f of c_f at R_f K, followed by R'_f T_X of epsilon.
The geometric adjunction is the recorded exact-pullback/total-direct-image adjunction;
no invertibility of this mate is imposed.
Source: blueprint direct-image proof, Formal properties
(blueprint: lem-sfb-scalar-direct-image-mate-coherence). -/
def scalarDirectImageMate {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RootCoordinateFace.lower Λ.X f ⋙ scalarSixChange a Y ⟶
      scalarSixChange a X ⋙ RootCoordinateFace.lower Λ'.X f :=
  (mateEquiv (RootCoordinateFace.adjunction Λ.X f)
    (RootCoordinateFace.adjunction Λ'.X f)
    (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv)).natTrans

set_option maxHeartbeats 800000 in
-- Normalize the folded derived functors in the two inverse-compositor cancellations.
/-- Naturality, geometric composition, the two adjunction identities, and scalar
composition for the specified module-derived direct-image mate.

Source: blueprint latest, direct-image proof Formal properties and Preservation,
and scalar pullback proof (1), (3)
(blueprint: lem-sfb-scalar-direct-image-mate-coherence).

Proof:
1. Apply def-weil-pbc-adjunction-mate with the recorded geometric adjunctions,
G = T_Y, H = T_X and alpha = c_f, the inverse normalized pullback comparison.
Its mate formula defines scalarDirectImageMate and supplies naturality.
2. lem-pur-mate-unit-compatibility and lem-amb-mate-unit-counit give the displayed
unit and counit identities, respectively, for these actual adjunctions.
3. Invert ScalarSixPullbackData.composition. Paste the resulting inverse squares
using lem-weil-pbc-mate-pasting (2). Change from composite adjunctions to those of
f followed by g using its clauses (3a), (3b) and def-weil-pbc-adjunction-conjugate.
The conjugates are exactly RootCoordinateFace.lowerComp, as specified by
def-sfb-test-map-derived-composition. This gives the geometric equation below.
4. Invert ScalarSixPullbackData.tower and apply mate pasting (1) for a and b.
Naturality of the last geometric unit moves s_Y through the mate formula;
naturality of s_X at the first counit moves s_X through the other end. The result
is the scalar-composition equation, with scalarSixTower as the tensor associator.
5. Every arrow is a morphism in the specified module-derived category. The
coefficient squares of sk-def-sfb-coefficient-change identify the actions under
the Cartesian pullback identifications. None of the calculations requires the
mate to be invertible, flat coefficients, bounds or constructibility. -/
theorem scalarDirectImageMateCoherence {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) :
    (∀ (K K' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
      (h : K ⟶ K'),
      (scalarSixChange a Y).map ((RootCoordinateFace.lower Λ.X f).map h) ≫
          (scalarDirectImageMate a f).app K' =
        (scalarDirectImageMate a f).app K ≫
          (RootCoordinateFace.lower Λ'.X f).map ((scalarSixChange a X).map h)) ∧
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X),
      (scalarDirectImageMate a (f ≫ g)).app K ≫
          (RootCoordinateFace.lowerComp Λ'.X f g).hom.app ((scalarSixChange a X).obj K) =
        (scalarSixChange a W).map ((RootCoordinateFace.lowerComp Λ.X f g).hom.app K) ≫
          (scalarDirectImageMate a g).app ((RootCoordinateFace.lower Λ.X f).obj K) ≫
          (RootCoordinateFace.lower Λ'.X g).map ((scalarDirectImageMate a f).app K)) ∧
    (∀ N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y),
      (scalarSixChange a Y).map ((RootCoordinateFace.adjunction Λ.X f).unit.app N) ≫
          (scalarDirectImageMate a f).app ((scalarSixPull Λ f).obj N) =
        (RootCoordinateFace.adjunction Λ'.X f).unit.app ((scalarSixChange a Y).obj N) ≫
          (RootCoordinateFace.lower Λ'.X f).map
            ((scalarDirectImagePullbackData.theta a f).inv.app N)) ∧
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X),
      (scalarSixPull Λ' f).map ((scalarDirectImageMate a f).app K) ≫
          (RootCoordinateFace.adjunction Λ'.X f).counit.app ((scalarSixChange a X).obj K) =
        (scalarDirectImagePullbackData.theta a f).inv.app
            ((RootCoordinateFace.lower Λ.X f).obj K) ≫
          (scalarSixChange a X).map ((RootCoordinateFace.adjunction Λ.X f).counit.app K)) ∧
    (∀ (Λ'' : ScalarSixRing.{u}) (b : Λ' ⟶ Λ'')
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)),
      (scalarSixTower a b Y).hom.app ((RootCoordinateFace.lower Λ.X f).obj K) ≫
          (scalarDirectImageMate (a ≫ b) f).app K =
        (scalarSixChange b Y).map ((scalarDirectImageMate a f).app K) ≫
          (scalarDirectImageMate b f).app ((scalarSixChange a X).obj K) ≫
          (RootCoordinateFace.lower Λ''.X f).map ((scalarSixTower a b X).hom.app K)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K K' h
    exact (scalarDirectImageMate a f).naturality h
  · intro K
    have ho (T : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :=
      IsIso.inv_eq_inv.mpr (scalarDirectImagePullbackData.composition a f g T)
    simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] at ho
    have hp (T : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :
        (scalarSixPull Λ' f).map
            ((scalarDirectImagePullbackData.theta a g).inv.app T) ≫
          (scalarDirectImagePullbackData.theta a f).inv.app ((scalarSixPull Λ g).obj T) =
        (scalarSixPullComp Λ' f g).inv.app ((scalarSixChange a W).obj T) ≫
          (scalarDirectImagePullbackData.theta a (f ≫ g)).inv.app T ≫
          (scalarSixChange a X).map ((scalarSixPullComp Λ f g).hom.app T) := by
      have ht := congrArg (fun z ↦ z ≫
        (scalarSixChange a X).map ((scalarSixPullComp Λ f g).hom.app T)) (ho T)
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at ht
      rw [(scalarSixChange a X).map_id
        ((scalarSixPull Λ g ⋙ scalarSixPull Λ f).obj T), Category.comp_id] at ht
      exact ht.symm
    have hm := scalarMate_comp
      (RootCoordinateFace.adjunction Λ.X g) (RootCoordinateFace.adjunction Λ.X f)
      (RootCoordinateFace.adjunction Λ'.X g) (RootCoordinateFace.adjunction Λ'.X f)
      (RootCoordinateFace.adjunction Λ.X (f ≫ g))
      (RootCoordinateFace.adjunction Λ'.X (f ≫ g))
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a g).inv)
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv)
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a (f ≫ g)).inv)
      (scalarSixPullComp Λ f g) (scalarSixPullComp Λ' f g) hp K
    change (scalarDirectImageMate a g).app ((RootCoordinateFace.lower Λ.X f).obj K) ≫
        (RootCoordinateFace.lower Λ'.X g).map ((scalarDirectImageMate a f).app K) ≫
        (RootCoordinateFace.lowerComp Λ'.X f g).inv.app ((scalarSixChange a X).obj K) =
      (scalarSixChange a W).map ((RootCoordinateFace.lowerComp Λ.X f g).inv.app K) ≫
        (scalarDirectImageMate a (f ≫ g)).app K at hm
    apply (cancel_epi ((scalarSixChange a W).map
      ((RootCoordinateFace.lowerComp Λ.X f g).inv.app K))).mp
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [← Category.assoc, ← hm]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [(scalarSixChange a W).map_id
      ((RootCoordinateFace.lower Λ.X f ⋙ RootCoordinateFace.lower Λ.X g).obj K)]
    simp only [Category.id_comp]
    exact congrArg (fun t ↦
      (scalarDirectImageMate a g).app ((RootCoordinateFace.lower Λ.X f).obj K) ≫ t)
      (Category.comp_id
        ((RootCoordinateFace.lower Λ'.X g).map ((scalarDirectImageMate a f).app K)))
  · intro N
    exact unit_mateEquiv (RootCoordinateFace.adjunction Λ.X f)
      (RootCoordinateFace.adjunction Λ'.X f)
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv) N
  · intro K
    exact mateEquiv_counit (RootCoordinateFace.adjunction Λ.X f)
      (RootCoordinateFace.adjunction Λ'.X f)
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv) K
  · intro Λ'' b K
    have ho (T : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :=
      IsIso.inv_eq_inv.mpr (scalarDirectImagePullbackData.tower a b f T)
    simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] at ho
    have hp (T : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
        (scalarDirectImagePullbackData.theta b f).inv.app ((scalarSixChange a Y).obj T) ≫
          (scalarSixChange b X).map ((scalarDirectImagePullbackData.theta a f).inv.app T) ≫
          (scalarSixTower a b X).hom.app ((scalarSixPull Λ f).obj T) =
        (scalarSixPull Λ'' f).map ((scalarSixTower a b Y).hom.app T) ≫
          (scalarDirectImagePullbackData.theta (a ≫ b) f).inv.app T := by
      have ht := congrArg (fun z ↦
        (scalarSixPull Λ'' f).map ((scalarSixTower a b Y).hom.app T) ≫ z ≫
          (scalarSixTower a b X).hom.app ((scalarSixPull Λ f).obj T)) (ho T)
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
        ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at ht
      rw [(scalarSixPull Λ'' f).map_id
        ((scalarSixChange a Y ⋙ scalarSixChange b Y).obj T), Category.id_comp] at ht
      exact ht.symm
    exact (scalarMate_coefficients
      (RootCoordinateFace.adjunction Λ.X f) (RootCoordinateFace.adjunction Λ'.X f)
      (RootCoordinateFace.adjunction Λ''.X f)
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv)
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta b f).inv)
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta (a ≫ b) f).inv)
      (scalarSixTower a b Y) (scalarSixTower a b X) hp K).symm

end AlgebraicGeometry.ProEtale.CondensedRing
