/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapTailNormalForm
import Sheaf.AlgebraicGeometry.PerfectOverlapStageObjectTail

/-! # Component factors of the stage object comparison -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] derivedPullback perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
set_option maxHeartbeats 1000000 in
-- Evaluate the constructed isomorphism once at the canonical component interface.
/-- Fully factorized component equation for the stage-object construction.
Source: Stacks Project, Tags 08DW and 0D5S. Factor off the inclusion inverse,
use the tail component formula, and evaluate whiskering and composition.
(blueprint: lem-pc-perfect-overlap-stage-object-factors). -/
theorem perfectOverlapStageObjectIso_hom_factors
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (q : T ⟶ S) (h : IsPullback g pX pY q)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (A : schemeDerivedCategory L.toScheme) :
    let i : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
    let j := X.homOfLE (leOfHom i)
    let t := j ≫ (g ∣_ L)
    let s := (U ⊓ V).ι ≫ pY
    let e : (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme ≅ pullback s q :=
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback
    let a := Y.homOfLE hWL
    let fac : e.inv ≫ t = pullback.fst s q ≫ a :=
      perfectOverlapTailStageProjection g pX pY q h U V L hWL
    (perfectOverlapStageObjectIso g pX pY q h U V L hWL).hom.app A =
      (derivedPullback e.inv).map
          ((overlapOpenInclusionPullbackIso X i).inv.app ((derivedPullback (g ∣_ L)).obj A)) ≫
        (derivedPullback e.inv).map ((perfectHomComposition j (g ∣_ L)).hom.app A) ≫
        (perfectHomComposition e.inv t).hom.app A ≫
        (eqToIso (congrArg (fun k ↦ derivedPullback k) fac)).hom.app A ≫
        (perfectHomComposition (pullback.fst s q) a).inv.app A := by
  intro i j t s e a fac
  have H := perfectOverlapStageObjectIso_hom_factor g pX pY q h U V L hWL A
  rw [perfectOverlapStageObjectTail_hom_app g pX pY q h U V L hWL A] at H
  simpa only [i, j, t, s, e, a, perfectOverlapStageEquivalence_map_eq, Iso.app_hom, Iso.app_inv,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Category.assoc] using H

end AlgebraicGeometry
