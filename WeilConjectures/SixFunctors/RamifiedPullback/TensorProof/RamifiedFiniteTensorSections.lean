/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Normalized scalar tensor sections and their adjunction unit

Source: Stacks Project, Tag 03EK. These are proved tensor-section helpers for
ramified finite pullback, separated to keep individual module compile times small.
(blueprint: lem-weil-ramified-finite-tensor-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback

namespace TensorProof
universe v r
section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
variable
  (F : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  (h : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
  (hm : ∀ {N N' : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : N ⟶ N'), F.map f = eqToHom (h N) ≫
    SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (h N').symm)

end
end TensorProof

attribute [local irreducible] HasDerivedCategory.standard scalarWitness

/-- The scalar adjunction transported through its actual sheafified tensor presentation.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections). -/
@[irreducible] noncomputable def scalarAdjunction {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :
    scalar.{t, u} c ⊣ SheafOfModules.restrictScalars
      ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c) :=
  (CategoryTheory.CochainPullback.extensionAdjunction c).ofNatIsoLeft
    (TensorProof.tensorPresentation c (scalar.{t, u} c) (scalarWitness.{t, u} c).choose_spec.choose
      (fun {A B : Mod.{t, u} R} (f : A ⟶ B) ↦
        (scalarWitness.{t, u} c).choose_spec.choose_spec.choose f)).symm

end WeilConjectures.RamifiedPullback
