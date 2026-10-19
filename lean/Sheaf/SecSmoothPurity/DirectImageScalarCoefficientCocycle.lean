/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
import Sheaf.SecSmoothPurity.PullbackScalarCoefficientCocycle

/-! # Coefficient associativity for canonical scalar comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md
(blueprint: lem-sp-direct-image-scalar-coefficient-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem scalarExtension_alias {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarExtensionFunctor φ T = directImageScalarExtension φ T := by
  unfold scalarExtensionFunctor
  rfl

private theorem scalarExtension_obj_alias {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (M : proEtaleDerivedCategory T A) :
    (scalarExtensionFunctor φ T).obj M = (directImageScalarExtension φ T).obj M := by
  unfold scalarExtensionFunctor
  rfl

attribute [defeq] scalarExtension_alias scalarExtension_obj_alias


set_option backward.defeqAttrib.useBackward true

private theorem mate_cocycle
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂]
    [Category* B₀] [Category* B₁] [Category* B₂]
    {L₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} (a₀ : L₀ ⊣ R₀)
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} (a₁ : L₁ ⊣ R₁)
    {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂} (a₂ : L₂ ⊣ R₂)
    (U₀₁ : A₀ ⥤ A₁) (U₁₂ : A₁ ⥤ A₂) (U₀₂ : A₀ ⥤ A₂)
    (T₀₁ : B₀ ⥤ B₁) (T₁₂ : B₁ ⥤ B₂) (T₀₂ : B₀ ⥤ B₂)
    (αA : U₀₁ ⋙ U₁₂ ⟶ U₀₂) (αB : T₀₁ ⋙ T₁₂ ⟶ T₀₂)
    (lm₀₁ : U₀₁ ⋙ L₁ ⟶ L₀ ⋙ T₀₁) (lm₁₂ : U₁₂ ⋙ L₂ ⟶ L₁ ⋙ T₁₂)
    (lm₀₂ : U₀₂ ⋙ L₂ ⟶ L₀ ⋙ T₀₂)
    (γ₀₁ : R₀ ⋙ U₀₁ ⟶ T₀₁ ⋙ R₁) (γ₁₂ : R₁ ⋙ U₁₂ ⟶ T₁₂ ⋙ R₂)
    (γ₀₂ : R₀ ⋙ U₀₂ ⟶ T₀₂ ⋙ R₂)
    (h₀₁ : ∀ N, L₁.map (γ₀₁.app N) ≫ a₁.counit.app (T₀₁.obj N) =
      lm₀₁.app (R₀.obj N) ≫ T₀₁.map (a₀.counit.app N))
    (h₁₂ : ∀ N, L₂.map (γ₁₂.app N) ≫ a₂.counit.app (T₁₂.obj N) =
      lm₁₂.app (R₁.obj N) ≫ T₁₂.map (a₁.counit.app N))
    (h₀₂ : ∀ N, L₂.map (γ₀₂.app N) ≫ a₂.counit.app (T₀₂.obj N) =
      lm₀₂.app (R₀.obj N) ≫ T₀₂.map (a₀.counit.app N))
    (hlm : ∀ K, L₂.map (αA.app K) ≫ lm₀₂.app K =
      lm₁₂.app (U₀₁.obj K) ≫ T₁₂.map (lm₀₁.app K) ≫ αB.app (L₀.obj K))
    (N : B₀) :
    αA.app (R₀.obj N) ≫ γ₀₂.app N =
      U₁₂.map (γ₀₁.app N) ≫ γ₁₂.app (T₀₁.obj N) ≫ R₂.map (αB.app N) := by
  apply (a₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [h₀₂]
  rw [← Category.assoc, hlm]
  simp only [Category.assoc]
  have hn := αB.naturality (a₀.counit.app N)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← hn]
  have hc := a₂.counit.naturality (αB.app N)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hc
  rw [hc]
  rw [← Category.assoc (L₂.map (γ₁₂.app _)), h₁₂]
  simp only [Category.assoc]
  have hl := lm₁₂.naturality (γ₀₁.app N)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hl
  rw [← Category.assoc (L₂.map (U₁₂.map (γ₀₁.app N))), hl]
  simp only [Category.assoc]
  simpa only [Functor.map_comp, Functor.comp_obj, Functor.id_obj, Category.assoc] using
    congrArg (fun t ↦ lm₁₂.app (U₀₁.obj (R₀.obj N)) ≫ T₁₂.map t ≫ αB.app N)
      (h₀₁ N).symm

private theorem mate_cocycle_from_left
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂]
    [Category* B₀] [Category* B₁] [Category* B₂]
    {L₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} (a₀ : L₀ ⊣ R₀)
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} (a₁ : L₁ ⊣ R₁)
    {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂} (a₂ : L₂ ⊣ R₂)
    (U₀₁ : A₀ ⥤ A₁) (U₁₂ : A₁ ⥤ A₂) (U₀₂ : A₀ ⥤ A₂)
    (T₀₁ : B₀ ⥤ B₁) (T₁₂ : B₁ ⥤ B₂) (T₀₂ : B₀ ⥤ B₂)
    (αA : U₀₁ ⋙ U₁₂ ⟶ U₀₂) (αB : T₀₁ ⋙ T₁₂ ⟶ T₀₂)
    (lm₀₁ : U₀₁ ⋙ L₁ ⟶ L₀ ⋙ T₀₁) (lm₁₂ : U₁₂ ⋙ L₂ ⟶ L₁ ⋙ T₁₂)
    (lm₀₂ : U₀₂ ⋙ L₂ ⟶ L₀ ⋙ T₀₂)
    (hlm : ∀ K, L₂.map (αA.app K) ≫ lm₀₂.app K =
      lm₁₂.app (U₀₁.obj K) ≫ T₁₂.map (lm₀₁.app K) ≫ αB.app (L₀.obj K))
    (N : B₀) :
    let γ₀₁ := (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ lm₀₁)).natTrans
    let γ₁₂ := (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ lm₁₂)).natTrans
    let γ₀₂ := (mateEquiv a₀ a₂ (TwoSquare.mk _ _ _ _ lm₀₂)).natTrans
    αA.app (R₀.obj N) ≫ γ₀₂.app N =
      U₁₂.map (γ₀₁.app N) ≫ γ₁₂.app (T₀₁.obj N) ≫ R₂.map (αB.app N) := by
  exact mate_cocycle a₀ a₁ a₂ U₀₁ U₁₂ U₀₂ T₀₁ T₁₂ T₀₂ αA αB lm₀₁ lm₁₂ lm₀₂
    _ _ _ (fun K ↦ mateEquiv_counit a₀ a₁ (TwoSquare.mk _ _ _ _ lm₀₁) K)
    (fun K ↦ mateEquiv_counit a₁ a₂ (TwoSquare.mk _ _ _ _ lm₁₂) K)
    (fun K ↦ mateEquiv_counit a₀ a₂ (TwoSquare.mk _ _ _ _ lm₀₂) K) hlm N

attribute [local irreducible] completedAdicDerivedChange completedAdicChange
  proEtaleRingModulePullback proEtaleRingModuleDirectImage

set_option maxHeartbeats 600000 in
-- Matching concrete scalar functor interfaces requires explicit alias reduction.
/-- The coefficient cocycle for the canonical direct-image counit mate.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-direct-image.proof.md, proper-map coefficient cocycle;
expanded node det-sp-reduction-direct-image, Step 10.
(blueprint: lem-sp-direct-image-scalar-coefficient-cocycle).

Proof: transpose both maps under the C-linear inverse-image/direct-image adjunction.
The transpose of the direct comparison is scalar extension of the A-counit, preceded
by the specified tensor/pullback identification. For the successive comparison,
naturality of that identification and the defining counit identity for the B-to-C
mate change the transpose to successive scalar extension of the A-counit.
The same identity for the A-to-B mate changes its remaining factor to that counit.
The coefficient associator identifies the resulting successive extension with direct
A-to-C extension: on flat-term K-flat representatives both pullback/associativity
routes send ((x tensor b) tensor c) to pullback(x) tensor psi(b)c. Pure tensors
locally generate, so the chain maps agree, and the canonical derived counits descend
this equality. Naturality of the associator at the A-counit reinserts precisely
the displayed alpha factors. The adjunction bijection is injective, so equal
transposes give the stated equality. This holds for every N and every map p;
properness and cohomological finiteness are not used in this coherence argument. -/
theorem directImageScalarCoefficientCocycle
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) (N : proEtaleDerivedCategory Z A) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((directImageConstantPush A p).obj N) ≫
      (directImageScalarComparison (ψ.comp φ) p).app N =
    (scalarExtensionFunctor ψ Y).map ((directImageScalarComparison φ p).app N) ≫
      (directImageScalarComparison ψ p).app ((scalarExtensionFunctor φ Z).obj N) ≫
        (directImageConstantPush C p).map
          ((scalarExtensionFunctor_composition φ ψ Z).hom.app N)  := by
  dsimp only [scalarExtensionFunctor]
  unfold directImageScalarComparison
  let adj (R : Type u) [CommRing R] :=
    proEtaleRingDerivedAdjunction p (proEtaleConstantRing Y R)
      (proEtaleConstantRing Z R) (proEtaleConstantRingComparison p R)
  have hcoh := directImageScalarPullbackCoefficientCocycle φ ψ p
  dsimp only [scalarExtensionFunctor, proEtaleConstantRingDerivedPullback,
    proEtaleConstantRingPullback] at hcoh
  have h := mate_cocycle_from_left
    (adj A) (adj B) (adj C)
    (directImageScalarExtension φ Y) (directImageScalarExtension ψ Y)
    (directImageScalarExtension (ψ.comp φ) Y)
    (directImageScalarExtension φ Z) (directImageScalarExtension ψ Z)
    (directImageScalarExtension (ψ.comp φ) Z)
    (scalarExtensionFunctor_composition φ ψ Y).hom
    (scalarExtensionFunctor_composition φ ψ Z).hom
    (directImageScalarPullbackIso φ p).hom
    (directImageScalarPullbackIso ψ p).hom
    (directImageScalarPullbackIso (ψ.comp φ) p).hom
    hcoh N
  exact h

end AlgebraicGeometry.ProEtale
