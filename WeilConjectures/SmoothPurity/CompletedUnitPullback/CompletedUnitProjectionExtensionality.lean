/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRealizationCoordinate
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure

/-! Extensionality for maps into the completed regular coefficient object. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section
variable (W : Scheme.{u})

private theorem coefficient_section_ext (V : W.ProEtᵒᵖ)
    (x y : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj V)
    (h : ∀ n, (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V x =
      (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V y) : x = y := by
  let T := sheafToPresheaf (ProEt.topology W) RingCat.{u + 1} ⋙
    (evaluation W.ProEtᵒᵖ RingCat.{u + 1}).obj V ⋙ forget RingCat.{u + 1}
  have ht := isLimitOfPreserves T (limit.isLimit (integralCoefficientSheafSystem l E W))
  apply (Types.isLimitEquivSections ht).injective
  apply Subtype.ext
  funext n
  exact h n.unop

private theorem regular_projection_ext
    (f g : integralConstantCoefficientObject l E W ⟶ integralConstantCoefficientObject l E W)
    (h : ∀ n, f ≫ (DerivedCategory.singleFunctor.{u + 2} _ 0).map
        (constantCoefficientProjection l E W n) =
      g ≫ (DerivedCategory.singleFunctor.{u + 2} _ 0).map
        (constantCoefficientProjection l E W n)) : f = g := by
  let S := DerivedCategory.singleFunctor.{u + 2} (scalarReductionSource l E W) 0
  let a := S.preimage f
  let b := S.preimage g
  suffices a = b by simpa only [a, b, Functor.map_preimage] using congrArg S.map this
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply coefficient_section_ext l E W V
  intro n
  have hc : a ≫ constantCoefficientProjection l E W n =
      b ≫ constantCoefficientProjection l E W n := by
    apply S.map_injective
    simpa only [Functor.map_comp, a, b, Functor.map_preimage] using h n
  have hx := congrArg (fun z ↦ z.val.app V x) hc
  have ha := quotientProjection_apply l E W n V (a.val.app V x)
  have hb := quotientProjection_apply l E W n V (b.val.app V x)
  exact ha.symm.trans (hx.trans hb)

end

/--
Finite quotient projections detect two maps into the completed regular object
once a fixed isomorphism identifies their source with that object.
Source: Bhatt--Scholze, Section 3.5 (the completed ring sheaf is the inverse limit of
its finite quotients); Stacks 0941.
(blueprint: new-lem-pur-completed-unit-projection-extensionality).

Proof: precompose both maps with q.inv. The single functor in degree zero is fully
faithful, so the resulting endomorphisms of the completed regular object are maps of
sheaves of modules; their values on each section are detected by the limit projections,
which are the sectionwise formulas of constantCoefficientProjection. Cancel the
epimorphism q.inv.
-/
theorem completedUnit_projection_extensionality
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (q : (integralDerivedPullback l E g).obj (integralConstantCoefficientObject l E Y) ≅
      integralConstantCoefficientObject l E X)
    (a b : (integralDerivedPullback l E g).obj (integralConstantCoefficientObject l E Y) ⟶
      integralConstantCoefficientObject l E X)
    (h : ∀ n, a ≫ (DerivedCategory.singleFunctor.{u + 2} _ 0).map
        (constantCoefficientProjection l E X n) =
      b ≫ (DerivedCategory.singleFunctor.{u + 2} _ 0).map
        (constantCoefficientProjection l E X n)) :
    a = b := by
  rw [← cancel_epi q.inv]
  apply regular_projection_ext l E X
  intro n
  simpa only [Category.assoc] using congrArg (fun t ↦ q.inv ≫ t) (h n)

end WeilConjectures.CompletedUnitPullback
