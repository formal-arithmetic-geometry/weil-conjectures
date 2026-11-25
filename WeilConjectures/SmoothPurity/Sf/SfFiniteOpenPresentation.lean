/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportTower
public import WeilConjectures.SmoothPurity.CompactSupportProperImageTower.CompactSupportProperImageTower
public import WeilConjectures.SmoothPurity.Sf.SfFiniteOpenCoefficientGenerators

/-! # Finite slice open extension and its coefficient square

## References

* Stacks Project, Tags 03DI, 03DJ, 098K and 0E8I.
* Bhatt--Scholze, *The pro-étale topology for schemes*, Definition 6.7.6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open Opposite CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

/-- Compatibility of a finite open presentation with the actual ordinary coefficient square.
This compares natural transformations before passage to complexes or derived categories. -/
def SfFiniteOpenPresentationCompatible
    (e : CompactSupportProperImageTower.OpenData l E j o)
    (ι : ∀ n : ℕ, IntegralOpenReduction.finiteExtension l E j o n ≅
      sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1))) : Prop :=
  ∀ n : ℕ,
    Functor.isoWhiskerLeft (normalizedDVRModuleRes l E X (Nat.le_succ n)) (ι (n + 1)) ≪≫
        Functor.isoWhiskerRight (sfFiniteOpenPresentationRestriction l E X n)
          (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 2))) ≪≫
        sfOpenRestriction j (Padic.coefficientExtensionTransition l E (n + 1)) =
      e.ordinary n ≪≫
        Functor.isoWhiskerRight (ι n) (normalizedDVRModuleRes l E Z (Nat.le_succ n)) ≪≫
        Functor.isoWhiskerLeft
          (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)))
          (sfFiniteOpenPresentationRestriction l E Z n)

private theorem finiteExtension_hom_ext (n : ℕ)
    (M : normalizedDVRModules l E X n) (N : normalizedDVRModules l E Z n)
    (f g : (IntegralOpenReduction.finiteExtension l E j o n).obj M ⟶ N)
    (h : ∀ (W : Z.ProEt) (a : W ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      f.val.app (op W) (IntegralOpenReduction.finiteExtensionSection l E j o n M W a x) =
        g.val.app (op W) (IntegralOpenReduction.finiteExtensionSection l E j o n M W a x)) :
    f = g := by
  classical
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  ext W x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of a x =>
    let t := (eqToIso (o.finiteFunctor n)).app M
    have ht : t.inv.val.app (op (Over.mk a))
        (t.hom.val.app (op (Over.mk a)) x) = x := by
      have hh := congrArg (fun k ↦ k.val.app (op (Over.mk a)) x) t.hom_inv_id
      simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
        ModuleCat.id_apply] using hh
    have hh := h W.unop a (t.hom.val.app (op (Over.mk a)) x)
    dsimp only [IntegralOpenReduction.finiteExtensionSection] at hh
    rw [show ((eqToHom (o.finiteFunctor n).symm).app M).val.app
        (op (Over.mk a)) (t.hom.val.app (op (Over.mk a)) x) = x from ht] at hh
    exact hh
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The finite open comparisons can be chosen to preserve the coefficient squares.
No derived tower, completion condition, proper map or constructibility is involved. -/
theorem sfFiniteOpenPresentation
    (e : CompactSupportProperImageTower.OpenData l E j o) :
    ∃ ι : ∀ n : ℕ, IntegralOpenReduction.finiteExtension l E j o n ≅
        sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)),
      SfFiniteOpenPresentationCompatible l E j o e ι := by
  classical
  have hr (n : ℕ) := (sfFiniteOpenRestriction_presentation l E j o n).exists
  choose r hr using hr
  let ι := fun n ↦ sfFiniteOpenLeftComparison l E j o n (r n)
  refine ⟨ι, ?_⟩
  intro n
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply finiteExtension_hom_ext l E j o (n + 1)
    ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M)
  intro W a x
  have hg₀ := sfFiniteOpenCoefficient_generator l E j o n
    (r n) (r (n + 1)) (hr n) (hr (n + 1)) M W a
  unfold SfFiniteOpenCoefficientGenerator at hg₀
  have hg := hg₀ x
  have he := sfNormalizedDVRSection_heq l E X Z n M
    ((IntegralOpenReduction.finiteExtension l E j o n).obj M)
    (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) (op W)
    (e.sections n M W a) x
  change
    ((sfFiniteOpenIntrinsicCoefficient l E j o n (r (n + 1))).hom.app M).val.app (op W)
      (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1)
        ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x) =
    ((sfFiniteOpenLowerCoefficient l E j o n (r n)).hom.app M).val.app (op W)
      (((e.ordinary n).hom.app M).val.app (op W)
        (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1)
          ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x))
  exact hg.trans (congrArg
    (fun z ↦ ((sfFiniteOpenLowerCoefficient l E j o n (r n)).hom.app M).val.app (op W) z)
    he).symm

end WeilConjectures
