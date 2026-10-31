/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralRepresentingPairData

/-! # Transport of the actual support counit

Source: blueprint integral adjunction, coordinate Hom chain and actual counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

section Abstract
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]

private theorem presentation_counit (e : C₁ ≌ C₂) {R : C₂ ⥤ C₃} {T : C₃ ⥤ C₂}
    (a : R ⊣ T) (q : C₃ ≌ C₄) (V : C₃) (Z : C₄) (b : Z ⟶ q.functor.obj V) :
    q.functor.map (R.map (e.functor.map
        (e.inverse.map (T.map (q.inverse.map b ≫ q.unitIso.inv.app V))))) ≫
        q.functor.map (R.map (e.counitIso.hom.app (T.obj V)) ≫ a.counit.app V) =
      q.functor.map (R.map (e.counitIso.hom.app (T.obj (q.inverse.obj Z)))) ≫
        q.functor.map (a.counit.app (q.inverse.obj Z)) ≫ q.counitIso.hom.app Z ≫ b := by
  let t := q.inverse.map b ≫ q.unitIso.inv.app V
  have he := e.counit.naturality (T.map t)
  have ha := a.counit.naturality t
  change e.functor.map (e.inverse.map (T.map t)) ≫
    e.counitIso.hom.app (T.obj V) =
      e.counitIso.hom.app (T.obj (q.inverse.obj Z)) ≫ T.map t at he
  change R.map (T.map t) ≫ a.counit.app V =
    a.counit.app (q.inverse.obj Z) ≫ t at ha
  dsimp only [t] at he ha
  have ht : q.functor.map t = q.counitIso.hom.app Z ≫ b := by
    simpa only [t, Functor.map_comp, Equivalence.counit_app_functor] using
      q.counit_naturality b
  calc
    _ = q.functor.map (R.map (e.counitIso.hom.app (T.obj (q.inverse.obj Z))) ≫
        a.counit.app (q.inverse.obj Z) ≫ t) := by
      rw [← Functor.map_comp]
      apply congrArg q.functor.map
      rw [← R.map_comp_assoc, he, R.map_comp, Category.assoc, ha]
    _ = _ := by rw [Functor.map_comp, Functor.map_comp, ht]

end Abstract

/-- The fixed compact-support presentation carries the actual reduction counit
to the published alpha, as an equality in the system category.
Source: current blueprint sk-prop-sp-integral-adjunction, outer Hom comparisons
and the unit/counit paragraph (blueprint: lem-pur-support-presentation-alpha).

Proof: expand the composite adjunction counit. It is the coordinate functor applied
to the coefficient reduction of the coefficient-model counit, followed by the
reduction/limit counit and the coordinate-equivalence counit. The presentation map
is the total limit of beta followed by the inverse coordinate unit. Naturality of
the reduction/limit counit moves beta across it. Naturality of the coefficient-model
counit moves its inverse-coordinate-unit term across the coefficient presentation.
Finally the triangle identity for the coordinate equivalence cancels its unit and
counit. The remaining coefficient-model counit followed by the reduction/limit
counit is exactly limitPresentation followed by the published alpha. No faithfulness
of evaluation is used. -/
theorem supportPresentation_alpha
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R) :
    ∀ K : CondensedERealization.Integral l E X,
      (reduction l E Y (R Y)).map
          ((supportPresentation l E (R X) S G H D (beta l E S G H D)).hom.app K.obj) ≫
        (coordinates l E Y).functor.map
          ((CompactSupportCondensedRealization.alpha l E c R M).app K) =
      alpha l E (R X) (R Y) S G H D K.obj ≫
        (beta l E S G H D).hom.app
          ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)) := by
  intro K
  simpa only [supportPresentation, support, reduction, totalLimit, alpha, adjunction,
    CompactSupportCondensedRealization.reconstructedSystem, ObjectProperty.ι_obj,
    Equivalence.counit,
    CompactSupportCondensedRealization.alpha,
    CompactSupportCondensedRealization.limitPresentation,
    Adjunction.comp_counit_app, Equivalence.toAdjunction_counit,
    Functor.map_comp, Category.assoc, Functor.comp_map, Functor.comp_obj,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom] using
      presentation_counit (purCoefficientModel l E Y) (R Y).adjunction
        (coordinates l E Y)
        ((CompactSupportCondensedRealization.systemSupport l E c).obj
          ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)))
        (D.compact.functor.obj ((reduction l E X (R X)).obj K.obj))
        ((beta l E S G H D).hom.app
          ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)))

end WeilConjectures.PurIntegralRepresentingPair
