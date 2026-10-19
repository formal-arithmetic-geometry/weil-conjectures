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
sk-lem-sp-reduction-direct-image.proof.md (blueprint: lem-sp-open-scalar-coefficient-cocycle).
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

attribute [defeq] scalarExtension_alias

attribute [local irreducible] completedAdicDerivedChange completedAdicChange
  proEtaleRingModulePullback proEtaleRingModuleDirectImage

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mate_cocycle_converse
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
    (h₀₁ : ∀ K, U₀₁.map (a₀.unit.app K) ≫ γ₀₁.app (L₀.obj K) =
      a₁.unit.app (U₀₁.obj K) ≫ R₁.map (lm₀₁.app K))
    (h₁₂ : ∀ K, U₁₂.map (a₁.unit.app K) ≫ γ₁₂.app (L₁.obj K) =
      a₂.unit.app (U₁₂.obj K) ≫ R₂.map (lm₁₂.app K))
    (h₀₂ : ∀ K, U₀₂.map (a₀.unit.app K) ≫ γ₀₂.app (L₀.obj K) =
      a₂.unit.app (U₀₂.obj K) ≫ R₂.map (lm₀₂.app K))
    (hγ : ∀ N, αA.app (R₀.obj N) ≫ γ₀₂.app N =
      U₁₂.map (γ₀₁.app N) ≫ γ₁₂.app (T₀₁.obj N) ≫ R₂.map (αB.app N))
    (K : A₀) :
    L₂.map (αA.app K) ≫ lm₀₂.app K =
      lm₁₂.app (U₀₁.obj K) ≫ T₁₂.map (lm₀₁.app K) ≫ αB.app (L₀.obj K) := by
  apply (a₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hu := a₂.unit.naturality (αA.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hu
  rw [← Category.assoc, ← hu]
  simp only [Category.assoc]
  rw [← h₀₂]
  have hn := αA.naturality (a₀.unit.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [hγ]
  rw [← Category.assoc (U₁₂.map (U₀₁.map (a₀.unit.app K))), ← U₁₂.map_comp, h₀₁]
  simp only [Functor.map_comp, Category.assoc]
  have hg := γ₁₂.naturality (lm₀₁.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hg
  rw [← Category.assoc (U₁₂.map (R₁.map (lm₀₁.app K))), hg]
  rw [← Category.assoc, ← Category.assoc, h₁₂]
  simp only [Category.assoc]


private theorem inverse_square_cocycle
    {D₀ D₁ D₂ E₀ E₁ E₂ : Type*}
    [Category* D₀] [Category* D₁] [Category* D₂]
    [Category* E₀] [Category* E₁] [Category* E₂]
    (P₀ : E₀ ⥤ D₀) (P₁ : E₁ ⥤ D₁) (P₂ : E₂ ⥤ D₂)
    (S₀₁ : D₀ ⥤ D₁) (S₁₂ : D₁ ⥤ D₂) (S₀₂ : D₀ ⥤ D₂)
    (T₀₁ : E₀ ⥤ E₁) (T₁₂ : E₁ ⥤ E₂) (T₀₂ : E₀ ⥤ E₂)
    (αD : S₀₁ ⋙ S₁₂ ≅ S₀₂) (αE : T₀₁ ⋙ T₁₂ ≅ T₀₂)
    (e₀₁ : T₀₁ ⋙ P₁ ≅ P₀ ⋙ S₀₁) (e₁₂ : T₁₂ ⋙ P₂ ≅ P₁ ⋙ S₁₂)
    (e₀₂ : T₀₂ ⋙ P₂ ≅ P₀ ⋙ S₀₂)
    (h : ∀ N, P₂.map (αE.hom.app N) ≫ e₀₂.hom.app N =
      e₁₂.hom.app (T₀₁.obj N) ≫ S₁₂.map (e₀₁.hom.app N) ≫ αD.hom.app (P₀.obj N))
    (N : E₀) :
    αD.hom.app (P₀.obj N) ≫ e₀₂.inv.app N =
      S₁₂.map (e₀₁.inv.app N) ≫ e₁₂.inv.app (T₀₁.obj N) ≫ P₂.map (αE.hom.app N) := by
  apply (cancel_mono (e₀₂.hom.app N)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← S₁₂.map_comp_assoc, Iso.inv_hom_id_app, S₁₂.map_id, Category.id_comp]
  exact Category.comp_id _


private lemma uniq_eq_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L M : C ⥤ D} {R S : D ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (r : S ≅ R) :
    a.leftAdjointUniq (b.ofNatIsoRight r) =
      (conjugateIsoEquiv b a).symm r := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

set_option maxHeartbeats 600000 in
-- The iterated mate formula compares two composite adjunctions.
private lemma open_mate
    {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {J₀ : A ⥤ B} {P₀ : B ⥤ A} (a₀ : J₀ ⊣ P₀)
    {J₁ : C ⥤ D} {P₁ : D ⥤ C} (a₁ : J₁ ⊣ P₁)
    {S : A ⥤ C} {U : C ⥤ A} (s : S ⊣ U)
    {T : B ⥤ D} {V : D ⥤ B} (t : T ⊣ V)
    (r : P₁ ⋙ U ≅ V ⋙ P₀) :
    (mateEquiv a₀ a₁
      ((a₀.comp t).leftAdjointUniq ((s.comp a₁).ofNatIsoRight r)).inv).natTrans =
      ((mateEquiv t s).symm r.inv).natTrans := by
  let e := (a₀.comp t).leftAdjointUniq ((s.comp a₁).ofNatIsoRight r)
  have he : conjugateIsoEquiv (s.comp a₁) (a₀.comp t) e = r := by
    dsimp only [e]
    rw [uniq_eq_conjugate]
    exact Equiv.apply_symm_apply _ _
  have hi := congrArg Iso.inv he
  have h := iterated_mateEquiv_conjugateEquiv a₀ a₁ s t
    (TwoSquare.mk _ _ _ _ e.inv)
  change _ = conjugateEquiv (a₀.comp t) (s.comp a₁) e.inv at h
  change conjugateEquiv (a₀.comp t) (s.comp a₁) e.inv = r.inv at hi
  rw [hi] at h
  apply (TwoSquare.equivNatTrans _ _ _ _).symm.injective
  apply (mateEquiv t s).injective
  apply TwoSquare.ext
  intro X
  exact (congr_app h X).trans (congrArg (fun z ↦ z.app X)
    ((mateEquiv t s).apply_symm_apply (TwoSquare.mk _ _ _ _ r.inv))).symm


private theorem open_cocycle_of_pullback
    {D₀ D₁ D₂ E₀ E₁ E₂ : Type*}
    [Category* D₀] [Category* D₁] [Category* D₂]
    [Category* E₀] [Category* E₁] [Category* E₂]
    {J₀ : D₀ ⥤ E₀} {P₀ : E₀ ⥤ D₀} (a₀ : J₀ ⊣ P₀)
    {J₁ : D₁ ⥤ E₁} {P₁ : E₁ ⥤ D₁} (a₁ : J₁ ⊣ P₁)
    {J₂ : D₂ ⥤ E₂} {P₂ : E₂ ⥤ D₂} (a₂ : J₂ ⊣ P₂)
    (S₀₁ : D₀ ⥤ D₁) (S₁₂ : D₁ ⥤ D₂) (S₀₂ : D₀ ⥤ D₂)
    (T₀₁ : E₀ ⥤ E₁) (T₁₂ : E₁ ⥤ E₂) (T₀₂ : E₀ ⥤ E₂)
    (αD : S₀₁ ⋙ S₁₂ ≅ S₀₂) (αE : T₀₁ ⋙ T₁₂ ≅ T₀₂)
    (e₀₁ : J₀ ⋙ T₀₁ ≅ S₀₁ ⋙ J₁) (e₁₂ : J₁ ⋙ T₁₂ ≅ S₁₂ ⋙ J₂)
    (e₀₂ : J₀ ⋙ T₀₂ ≅ S₀₂ ⋙ J₂)
    (lam₀₁ : T₀₁ ⋙ P₁ ≅ P₀ ⋙ S₀₁) (lam₁₂ : T₁₂ ⋙ P₂ ≅ P₁ ⋙ S₁₂)
    (lam₀₂ : T₀₂ ⋙ P₂ ≅ P₀ ⋙ S₀₂)
    (h₀₁ : (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ e₀₁.inv)).natTrans = lam₀₁.inv)
    (h₁₂ : (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ e₁₂.inv)).natTrans = lam₁₂.inv)
    (h₀₂ : (mateEquiv a₀ a₂ (TwoSquare.mk _ _ _ _ e₀₂.inv)).natTrans = lam₀₂.inv)
    (hcomp : ∀ N, P₂.map (αE.hom.app N) ≫ lam₀₂.hom.app N =
      lam₁₂.hom.app (T₀₁.obj N) ≫ S₁₂.map (lam₀₁.hom.app N) ≫ αD.hom.app (P₀.obj N))
    (M : D₀) :
    αE.hom.app (J₀.obj M) ≫ e₀₂.hom.app M =
      T₁₂.map (e₀₁.hom.app M) ≫ e₁₂.hom.app (S₀₁.obj M) ≫ J₂.map (αD.hom.app M) := by
  apply inverse_square_cocycle J₀ J₁ J₂ T₀₁ T₁₂ T₀₂ S₀₁ S₁₂ S₀₂
    αE αD e₀₁.symm e₁₂.symm e₀₂.symm
  intro K
  apply mate_cocycle_converse a₀ a₁ a₂ S₀₁ S₁₂ S₀₂ T₀₁ T₁₂ T₀₂
    αD.hom αE.hom e₀₁.inv e₁₂.inv e₀₂.inv lam₀₁.inv lam₁₂.inv lam₀₂.inv
  · intro K
    rw [← h₀₁]
    exact unit_mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ e₀₁.inv) K
  · intro K
    rw [← h₁₂]
    exact unit_mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ e₁₂.inv) K
  · intro K
    rw [← h₀₂]
    exact unit_mateEquiv a₀ a₂ (TwoSquare.mk _ _ _ _ e₀₂.inv) K
  · exact inverse_square_cocycle P₀ P₁ P₂ S₀₁ S₁₂ S₀₂ T₀₁ T₁₂ T₀₂
      αD αE lam₀₁ lam₁₂ lam₀₂ hcomp

private theorem transport_cocycle
    {D₀ D₁ D₂ E₀ E₁ E₂ : Type*}
    [Category* D₀] [Category* D₁] [Category* D₂]
    [Category* E₀] [Category* E₁] [Category* E₂]
    {J₀ K₀ : D₀ ⥤ E₀} {J₁ K₁ : D₁ ⥤ E₁} {J₂ K₂ : D₂ ⥤ E₂}
    (m₀ : J₀ ≅ K₀) (m₁ : J₁ ≅ K₁) (m₂ : J₂ ≅ K₂)
    (S₀₁ : D₀ ⥤ D₁) (S₁₂ : D₁ ⥤ D₂) (S₀₂ : D₀ ⥤ D₂)
    (T₀₁ : E₀ ⥤ E₁) (T₁₂ : E₁ ⥤ E₂) (T₀₂ : E₀ ⥤ E₂)
    (αD : S₀₁ ⋙ S₁₂ ⟶ S₀₂) (αE : T₀₁ ⋙ T₁₂ ⟶ T₀₂)
    (e₀₁ : K₀ ⋙ T₀₁ ≅ S₀₁ ⋙ K₁) (e₁₂ : K₁ ⋙ T₁₂ ≅ S₁₂ ⋙ K₂)
    (e₀₂ : K₀ ⋙ T₀₂ ≅ S₀₂ ⋙ K₂)
    (M : D₀)
    (h : αE.app (K₀.obj M) ≫ e₀₂.hom.app M =
      T₁₂.map (e₀₁.hom.app M) ≫ e₁₂.hom.app (S₀₁.obj M) ≫ K₂.map (αD.app M)) :
    αE.app (J₀.obj M) ≫
        (T₀₂.map (m₀.hom.app M) ≫ e₀₂.hom.app M ≫ m₂.inv.app (S₀₂.obj M)) =
      T₁₂.map (T₀₁.map (m₀.hom.app M) ≫ e₀₁.hom.app M ≫
          m₁.inv.app (S₀₁.obj M)) ≫
        (T₁₂.map (m₁.hom.app (S₀₁.obj M)) ≫ e₁₂.hom.app (S₀₁.obj M) ≫
          m₂.inv.app (S₁₂.obj (S₀₁.obj M))) ≫ J₂.map (αD.app M) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← T₁₂.map_comp_assoc (m₁.inv.app (S₀₁.obj M)),
    m₁.inv_hom_id_app, T₁₂.map_id, Category.id_comp]
  have ha := αE.naturality (m₀.hom.app M)
  dsimp only [Functor.comp_map] at ha
  rw [← Category.assoc, ← ha]
  simp only [Category.assoc]
  rw [← Category.assoc (αE.app _), h]
  simp only [Category.assoc]
  rw [m₂.inv.naturality]


private theorem openScalar_mate
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (mateEquiv
      (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison j A))
      (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z B)
        (proEtaleConstantRing X B) (proEtaleConstantRingComparison j B))
      (TwoSquare.mk _ _ _ _ (openScalarIso φ j).inv)).natTrans =
        (directImageScalarPullbackIso φ j).inv := by
  exact open_mate
    (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison j A))
    (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z B)
      (proEtaleConstantRing X B) (proEtaleConstantRingComparison j B))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
    (proEtaleRingRestrictionDerivedPullback j
      (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap (T := Z) φ) (proEtaleConstantRingMap (T := X) φ)
      (proEtaleConstantRingComparison j A) (proEtaleConstantRingComparison j B)
      (proEtaleConstantInverseImageMap_naturality j
        (CommRingCat.ofHom (RingHom.ulift φ))).symm)

set_option maxHeartbeats 600000 in
-- Concrete scalar aliases require extra elaboration when applying the mate identity.
private theorem openScalar_cocycle
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleDerivedCategory X A) :
    (scalarExtensionFunctor_composition φ ψ Z).hom.app
        ((openExtension (A := A) j).obj M) ≫
      (openScalarIso (ψ.comp φ) j).hom.app M =
    (scalarExtensionFunctor ψ Z).map ((openScalarIso φ j).hom.app M) ≫
      (openScalarIso ψ j).hom.app ((scalarExtensionFunctor φ X).obj M) ≫
        (openExtension (A := C) j).map
          ((scalarExtensionFunctor_composition φ ψ X).hom.app M) := by
  exact open_cocycle_of_pullback
    (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison j A))
    (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z B)
      (proEtaleConstantRing X B) (proEtaleConstantRingComparison j B))
    (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z C)
      (proEtaleConstantRing X C) (proEtaleConstantRingComparison j C))
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor ψ X)
    (scalarExtensionFunctor (ψ.comp φ) X)
    (scalarExtensionFunctor φ Z) (scalarExtensionFunctor ψ Z)
    (scalarExtensionFunctor (ψ.comp φ) Z)
    (scalarExtensionFunctor_composition φ ψ X) (scalarExtensionFunctor_composition φ ψ Z)
    (openScalarIso φ j) (openScalarIso ψ j) (openScalarIso (ψ.comp φ) j)
    (directImageScalarPullbackIso φ j) (directImageScalarPullbackIso ψ j)
    (directImageScalarPullbackIso (ψ.comp φ) j)
    (openScalar_mate φ j) (openScalar_mate ψ j) (openScalar_mate (ψ.comp φ) j)
    (directImageScalarPullbackCoefficientCocycle φ ψ j) M

/-- Coefficient associativity for the intrinsic, unit-normalized open tensor map.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-direct-image.proof.md, open coefficient cocycle calculation;
expanded node det-sp-reduction-direct-image, Step 11.
(blueprint: lem-sp-open-scalar-coefficient-cocycle).

Proof: extension by zero preserves flat-term K-flat complexes: the ordinary open
projection identity identifies its tensor with Q with extension of the tensor with
j^*Q, which is acyclic whenever Q is acyclic. Exactness gives flat terms as well.
Thus all scalar extensions may be computed on such representatives. Restrict the
two composites to the open. The normalization of the open scalar comparison gives
the identity on the restricted tensor; the normalization of the coefficient
associator gives ((m tensor b) tensor c) to m tensor psi(b)c on both routes.
The open-extension/restriction unit is an isomorphism, so restriction is faithful
on morphisms between extensions by zero. The source of both composites is itself
an extension by zero, by the two open scalar isomorphisms. Therefore equality after
restriction proves the displayed equality. The coordinate isomorphisms
reductionOpenModel preserve the same unit; their intermediate inverse pairs cancel.
Finally naturality and K-flat localization give the equality for every M. -/
theorem reductionOpenScalarCoefficientCocycle
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleDerivedCategory X A) :
    (scalarExtensionFunctor_composition φ ψ Z).hom.app
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M) ≫
      (reductionOpenScalarIso (ψ.comp φ) j).hom.app M =
    (scalarExtensionFunctor ψ Z).map ((reductionOpenScalarIso φ j).hom.app M) ≫
      (reductionOpenScalarIso ψ j).hom.app ((scalarExtensionFunctor φ X).obj M) ≫
        (sfIntrinsicExtensionByZero j C).mapDerivedCategory.map
          ((scalarExtensionFunctor_composition φ ψ X).hom.app M) := by
  dsimp only [reductionOpenScalarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact transport_cocycle (reductionOpenModel A j) (reductionOpenModel B j)
    (reductionOpenModel C j)
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor ψ X)
    (scalarExtensionFunctor (ψ.comp φ) X)
    (scalarExtensionFunctor φ Z) (scalarExtensionFunctor ψ Z)
    (scalarExtensionFunctor (ψ.comp φ) Z)
    (scalarExtensionFunctor_composition φ ψ X).hom
    (scalarExtensionFunctor_composition φ ψ Z).hom
    (openScalarIso φ j) (openScalarIso ψ j) (openScalarIso (ψ.comp φ) j)
    M (openScalar_cocycle φ ψ j M)

end AlgebraicGeometry.ProEtale
