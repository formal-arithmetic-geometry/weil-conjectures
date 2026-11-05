/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence

/-! # Scalar realizations of ordinary fixed-scalar coordinates

The explicit scalar realization of the fixed-scalar coordinates of a module sheaf is the
restriction of the module sheaf to the slice.

Source: Stacks Project, Tags 03CY, 03DA and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

section Associated

variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B : Type (t + 1)} [CommRing B] {R : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

end Associated

section Realization

set_option hygiene false in
local notation "𝓡" R => (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

variable (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
  (f : W ⟶ finitePerfectAdicChartObject V U)

variable {B : Type t} [CommRing B] (Rc : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
  (φ : adicConstantRing X B ⟶ Rc)
  (αW : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶ ((𝓡 Rc).over W).obj)

variable [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW]
  (hα : ∀ (Z : Over W) (c : ULift.{t + 1} B),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B).app (op Z.left) c) =
      αW.app (op Z) c)

variable {T : Sheaf (ProEt.topology X) RingCat.{t + 1}} (π : T ⟶ 𝓡 Rc)

end Realization

section Square

set_option hygiene false in
local notation "𝓡" R => (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

variable (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
  (f : W ⟶ finitePerfectAdicChartObject V U)
  {B₁ B₀ : Type t} [CommRing B₁] [CommRing B₀] (q : B₁ →+* B₀)
  {Rc₁ Rc₀ : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (s : Rc₁ ⟶ Rc₀)
  (φ₁ : adicConstantRing X B₁ ⟶ Rc₁) (φ₀ : adicConstantRing X B₀ ⟶ Rc₀)
  (αW₁ : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B₁)) ⟶ ((𝓡 Rc₁).over W).obj)
  (αW₀ : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B₀)) ⟶ ((𝓡 Rc₀).over W).obj)
  [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW₁]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW₁]
  [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW₀]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW₀]
  (hα₁ : ∀ (Z : Over W) (c : ULift.{t + 1} B₁),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ₁).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B₁).app (op Z.left) c) =
      αW₁.app (op Z) c)
  (hα₀ : ∀ (Z : Over W) (c : ULift.{t + 1} B₀),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ₀).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B₀).app (op Z.left) c) =
      αW₀.app (op Z) c)
  (p : (𝓡 Rc₁) ⟶ (𝓡 Rc₀))
  (hps : (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map s = p)
  (hαp : ∀ Z, αW₁.app Z ≫ (((ProEt.topology X).overPullback RingCat.{t + 1} W).map p).hom.app Z =
    RingCat.ofHom (RingHom.ulift q) ≫ αW₀.app Z)
  {T : Sheaf (ProEt.topology X) RingCat.{t + 1}} (π₁ : T ⟶ 𝓡 Rc₁) (π₀ : T ⟶ 𝓡 Rc₀)
  (hπ : π₁ ≫ (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
    s = π₀)
  (coh : sheafCompose (ProEt.topology U.left)
      (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q)) ⋙
      finitePerfectAdicRealizationModules X V U W f αW₁ π₁ ≅
    finitePerfectAdicRealizationModules X V U W f αW₀ π₀)
  (hcoh : ∀ G : Sheaf (ProEt.topology U.left) (ModuleCat.{t + 1} (ULift.{t + 1} B₀)),
    (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map (coh.hom.app G)) =
      (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
        ((finitePerfectAdicAssociatedCoherence αW₁ αW₀ (RingHom.ulift.{t + 1, t + 1} q)
          (((ProEt.topology X).overPullback RingCat.{t + 1} W).map p) hαp).hom.app
          ((finitePerfectAdicChartSlice X V U W f _).obj G))))
  {M₁ : SheafOfModules.{t + 1} (𝓡 Rc₁)} {M₀ : SheafOfModules.{t + 1} (𝓡 Rc₀)}
  (g : M₁ ⟶ (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      s)).obj M₀)
  (δ : (finiteCoefficientSliceRestriction X B₁ Rc₁ φ₁ V).obj M₁ ⟶
    (sheafCompose (ProEt.topology V.left)
      (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q))).obj
        ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀))
  (hδ : ∀ (U' : V.left.ProEt) x, δ.hom.app (op U') x =
    g.val.app (op (finitePerfectAdicChartObject V U')) x)

end Square

end AlgebraicGeometry.Scheme
