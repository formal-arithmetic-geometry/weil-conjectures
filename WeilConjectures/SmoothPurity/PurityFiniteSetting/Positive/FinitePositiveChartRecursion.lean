/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteFirstRootChart
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts

import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation

/-! # Ordered ordinary positive charts

The charts are constructed by recursion from the zero chart, the given first chart,
and the existing signed products. Source: finite-reduction proof, Step 2, ordered
positive powers (expanded Step 8).
(blueprint: lem-pur-finite-positive-chart-recursion)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

/-- Construct the ordinary zero chart using the coefficient realization unit.
Source: finite-reduction proof Step 2, coefficient one at zero.
(blueprint: lem-pur-finite-positive-chart-recursion). -/
def finiteTensorOrdinaryZeroChart (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    P.finiteTensorFixedSheaf T 0 ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  (sfIntrinsicModuleEquivalence T P.Ring).inverse.mapIso
      (proEtaleConstantModuleUnit T P.Ring).symm ≪≫
    (sfIntrinsicModuleEquivalence T P.Ring).unitIso.symm.app
      (proEtaleFixedConstantModule T P.Ring)

/-- Ordered tensor recursion on actual sheaf isomorphisms, with the given first chart.
No existence theorem is used to select the positive charts.
Source: finite-reduction proof Step 2, ordered positive powers, expanded Step 8.
(blueprint: lem-pur-finite-positive-chart-recursion). -/
def finiteTensorOrdinaryChartRecursion (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (e₁ : P.finiteTensorFixedSheaf T 1 ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))) :
    (d : ℕ) → P.finiteTensorFixedSheaf T d ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
  | 0 => P.finiteTensorOrdinaryZeroChart T
  | 1 => e₁
  | n + 2 =>
    eqToIso (congrArg (P.finiteTensorFixedSheaf T)
      (show ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 by omega)) ≪≫
    (P.finiteTensorSheafProducts T ((n + 1 : ℕ) : ℤ) 1).symm ≪≫
    tensorIso (P.finiteTensorOrdinaryChartRecursion T e₁ (n + 1)) e₁ ≪≫
    λ_ _

private theorem section_bijective (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r : ℤ) (V : T.ProEt) : Function.Bijective (P.finiteTensorSection T r V) := by
  change Function.Bijective
    (sectionRealization P.Ring T (P.finiteTensorLine T r) (Opposite.op V))
  exact sectionRealization_bijective P.Ring T (P.finiteTensorLine T r) (Opposite.op V)

private theorem zero_chart_section (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (V : T.ProEt) :
    P.finiteTensorSection T 0 V
      ((P.finiteTensorOrdinaryZeroChart T).inv.hom.app (Opposite.op V)
        ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient))) =
      (1 : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V)) := by
  let E := sfIntrinsicModuleEquivalence T P.Ring
  let C := proEtaleFixedConstantModule T P.Ring
  let k := proEtaleConstantModuleUnit T P.Ring
  change sectionRealization P.Ring T (proEtaleConstantModule T P.Ring) _
    ((E.inverse.map k.hom).hom.app _
      ((E.unitIso.hom.app C).hom.app _ _)) = _
  rw [sectionRealization_naturality, sectionRealization_functor]
  change k.hom.val.app (Opposite.op V)
    (sfIntrinsicRealizationUnit T P.Ring C (Opposite.op V)
      ((E.unitIso.hom.app C ≫ E.unitIso.inv.app C).hom.app (Opposite.op V)
        ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V)
            (1 : P.Coefficient)))) = _
  rw [Iso.hom_inv_id_app]
  have hε : Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient)) =
      toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (ModuleCat.of P.Coefficient P.Coefficient)) := by
    change (sheafificationAdjunction (ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient)).homEquiv _ _ (𝟙 _) = _
    rw [Adjunction.homEquiv_unit]
    change toSheafify (ProEt.topology T) _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  rw [hε]
  change (proEtaleConstantModuleUnit T P.Ring).hom.val.app (Opposite.op V)
    (sfIntrinsicRealizationUnit T P.Ring (proEtaleFixedConstantModule T P.Ring)
      (Opposite.op V)
      ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (ModuleCat.of P.Coefficient P.Coefficient))).app (Opposite.op V)
          (1 : P.Coefficient))) = _
  have h := (proEtaleConstantModuleUnit_existsUnique T P.Ring).exists.choose_spec
    (Opposite.op V) (1 : P.Coefficient)
  dsimp only [proEtaleConstantModuleUnit, Coefficient, coefficientCommRing] at h ⊢
  simpa only [map_one] using h

private theorem section_cast (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (V : T.ProEt) (b : P.FiniteTensorFrame T V) (r s : ℤ) (h : r = s)
    (z : (P.finiteTensorFixedSheaf T s).obj.obj (Opposite.op V))
    (hz : P.finiteTensorSection T s V z = b.basis s 0) :
    P.finiteTensorSection T r V
      ((eqToIso (congrArg (P.finiteTensorFixedSheaf T) h)).inv.hom.app
        (Opposite.op V) z) = b.basis r 0 := by
  subst s
  simpa using hz

private theorem tensor_unit_section (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (V : T.ProEt)
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
    (f : M ⟶ 𝟙_ _) (g : N ⟶ 𝟙_ _)
    (x : M.obj.obj (Opposite.op V)) (y : N.obj.obj (Opposite.op V))
    (hf : f.hom.app (Opposite.op V) x =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient))
    (hg : g.hom.app (Opposite.op V) y =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient)) :
    ((f ⊗ₘ g) ≫ (λ_ (𝟙_ _)).hom).hom.app (Opposite.op V)
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient)) M N).app (Opposite.op V) (x ⊗ₜ y)) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient) := by
  let F := sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)
  let U := 𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
  have hn := ConcreteCategory.congr_hom
    (congr_app (Functor.LaxMonoidal.μ_natural F f g) (Opposite.op V)) (x ⊗ₜ y)
  change (Functor.LaxMonoidal.μ F U U).app (Opposite.op V)
      ((f.hom.app (Opposite.op V) x) ⊗ₜ (g.hom.app (Opposite.op V) y)) =
    (f ⊗ₘ g).hom.app (Opposite.op V)
      ((Functor.LaxMonoidal.μ F M N).app (Opposite.op V) (x ⊗ₜ y)) at hn
  rw [hf, hg] at hn
  change (λ_ U).hom.hom.app (Opposite.op V)
    ((f ⊗ₘ g).hom.app (Opposite.op V) _) = _
  rw [← hn]
  have hu := ConcreteCategory.congr_hom
    (congr_app (Functor.LaxMonoidal.left_unitality F U) (Opposite.op V))
      ((1 : P.Coefficient) ⊗ₜ
        ((Functor.LaxMonoidal.ε F).app (Opposite.op V) (1 : P.Coefficient)))
  change (1 : P.Coefficient) • ((Functor.LaxMonoidal.ε F).app (Opposite.op V)
      (1 : P.Coefficient)) =
    (λ_ U).hom.hom.app (Opposite.op V)
      ((Functor.LaxMonoidal.μ F U U).app (Opposite.op V)
        (((Functor.LaxMonoidal.ε F).app (Opposite.op V) (1 : P.Coefficient)) ⊗ₜ
          ((Functor.LaxMonoidal.ε F).app (Opposite.op V) (1 : P.Coefficient)))) at hu
  simpa only [one_smul] using hu.symm

/-- The explicit recursion sends every compatible ordered basis vector to one.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, compatibility with the
invertible twist by associativity; expanded Step 8 of the root-chart construction.
(blueprint: lem-pur-finite-positive-chart-recursion).
Proof: at zero the realization unit and counit identify the frame vector with the
coefficient-one section. At one the assertion is the hypothesis on the first chart.
For degree n+2 use the normalized signed product in degrees n+1 and 1. The positive
frame condition says its source basis tensor maps to the degree n+2 basis. Realization is an
isomorphism on section modules, so the inverse product takes the given basis to
that tensor. Apply the induction hypothesis and the first-chart hypothesis; tensor
naturality followed by the unit unitor sends the tensor of the two coefficient-one
sections to coefficient one. This works on every object of the site, including the
empty object, and proves the assertion by induction without choosing any frame. -/
theorem finiteTensorOrdinaryChartRecursion_normalized (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (e₁ : P.finiteTensorFixedSheaf T 1 ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) (V : T.ProEt) (b : P.FiniteTensorFrame T V)
    (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
    (x : (P.finiteTensorFixedSheaf T d).obj.obj (Opposite.op V))
    (hx₁ : HEq (P.finiteTensorSection T 1 V x₁) (P.finiteTensorFrameBasis T V b 1))
    (he₁ : e₁.hom.hom.app (Opposite.op V) x₁ =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient))
    (hx : HEq (P.finiteTensorSection T d V x) (P.finiteTensorFrameBasis T V b d)) :
    (P.finiteTensorOrdinaryChartRecursion T e₁ d).hom.hom.app (Opposite.op V) x =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient) := by
  have hx₁' : P.finiteTensorSection T 1 V x₁ = b.basis 1 0 := eq_of_heq hx₁
  have hx' : P.finiteTensorSection T d V x = b.basis d 0 := eq_of_heq hx
  induction d using Nat.twoStepInduction with
  | zero =>
    have hh : x = (P.finiteTensorOrdinaryZeroChart T).inv.hom.app (Opposite.op V)
        ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient)) :=
      (section_bijective P T 0 V).injective
        (hx'.trans (b.zero.trans (zero_chart_section P T V).symm))
    rw [hh]
    change (((P.finiteTensorOrdinaryZeroChart T).inv ≫
      (P.finiteTensorOrdinaryZeroChart T).hom).hom.app (Opposite.op V)) _ = _
    rw [Iso.inv_hom_id]
    rfl
  | one =>
    have hh : x = x₁ := (section_bijective P T 1 V).injective (hx'.trans hx₁'.symm)
    simpa [finiteTensorOrdinaryChartRecursion, hh] using he₁
  | more n ih₀ ih =>
    obtain ⟨y, hy⟩ := (section_bijective P T (n + 1) V).surjective (b.basis (n + 1) 0)
    have hey := ih y (heq_of_eq hy) hy
    have hp := (P.existsUnique_finiteTensorSheafProducts T).exists.choose_spec
      ((n + 1 : ℕ) : ℤ) 1 V b y x₁ hy hx₁'
    let p := P.finiteTensorSheafProducts T ((n + 1 : ℕ) : ℤ) 1
    let hindex : ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by omega
    let a := eqToIso (congrArg (P.finiteTensorFixedSheaf T) hindex)
    let z := P.finiteTensorSectionTmul T ((n + 1 : ℕ) : ℤ) 1 V y x₁
    have hcast := section_cast P T V b _ _ hindex
      (p.hom.hom.app (Opposite.op V) z) hp
    have hh : x = a.inv.hom.app (Opposite.op V)
        (p.hom.hom.app (Opposite.op V) z) :=
      (section_bijective P T _ V).injective (hx'.trans hcast.symm)
    rw [hh]
    have hc : a.inv ≫ (P.finiteTensorOrdinaryChartRecursion T e₁ (n + 2)).hom =
        p.inv ≫ ((P.finiteTensorOrdinaryChartRecursion T e₁ (n + 1)).hom ⊗ₘ e₁.hom) ≫
          (λ_ (𝟙_ _)).hom := by
      simp only [finiteTensorOrdinaryChartRecursion, Iso.trans_hom, tensorIso_hom]
      change a.inv ≫ a.hom ≫ _ = _
      exact a.inv_hom_id_assoc _
    change ((a.inv ≫ (P.finiteTensorOrdinaryChartRecursion T e₁ (n + 2)).hom).hom.app
      (Opposite.op V)) (p.hom.hom.app (Opposite.op V) z) = _
    rw [hc]
    have hcancel : p.hom ≫ (p.inv ≫
        ((P.finiteTensorOrdinaryChartRecursion T e₁ (n + 1)).hom ⊗ₘ e₁.hom) ≫
          (λ_ (𝟙_ _)).hom) =
        ((P.finiteTensorOrdinaryChartRecursion T e₁ (n + 1)).hom ⊗ₘ e₁.hom) ≫
          (λ_ (𝟙_ _)).hom := by simp
    change ((p.hom ≫ (p.inv ≫
        ((P.finiteTensorOrdinaryChartRecursion T e₁ (n + 1)).hom ⊗ₘ e₁.hom) ≫
          (λ_ (𝟙_ _)).hom)).hom.app (Opposite.op V)) z = _
    rw [hcancel]
    exact tensor_unit_section P T V _ _ _ _ y x₁ hey he₁

end WeilConjectures.PurityFiniteSetting
