/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.ModuleCupHomologyEvaluation
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Bijectivity of canonical homology evaluation

Source: Stacks Project, Tag 064B, Lemma 13.19.8.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

-- Projective-source vanishing, with a strictly bounded-above representative.
private theorem projective_single_to_lower_eq_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (n : ℤ) (E : DerivedCategory C) [E.IsLE (n - 1)]
    (f : (DerivedCategory.singleFunctor C n).obj P ⟶ E) : f = 0 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E (n - 1)
  let := hK
  have h : f ≫ e.hom = 0 :=
    DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
      (f ≫ e.hom) (n - 1) (by omega)
  simpa using (cancel_mono e.hom).1 (by simpa using h)

-- Truncation removes the lower tail without changing maps from P[-n] or H^n.
set_option backward.isDefEq.respectTransparency false in
private theorem projective_single_homology_bijective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (E : DerivedCategory C) (n : ℤ) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor C n).obj P ⟶ E ↦
      (DerivedCategory.homologyFunctor C n).map f) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let S := (DerivedCategory.singleFunctor C n).obj P
  let T := (t.triangleLTGE n).obj E
  have hT := t.triangleLTGE_distinguished n E
  have : t.IsLE T.obj₁ (n - 1) := by
    change t.IsLE ((t.truncLT n).obj E) (n - 1)
    infer_instance
  have hv (f : S ⟶ T.obj₁) : f = 0 := projective_single_to_lower_eq_zero P n _ f
  have hv' (f : S ⟶ T.obj₁⟦(1 : ℤ)⟧) : f = 0 := by
    have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (n - 1) := by
      have := t.isLE_shift T.obj₁ (n - 1) 1 (n - 2) (by omega)
      exact t.isLE_of_le _ (n - 2) (n - 1) (by omega)
    exact projective_single_to_lower_eq_zero P n _ f
  have hpost : Function.Bijective (fun f : S ⟶ E ↦ f ≫ T.mor₂) := by
    constructor
    · intro f g h
      obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT (f - g) (by simp [h])
      rw [hv a, Limits.zero_comp] at ha
      exact sub_eq_zero.mp ha
    · intro g
      obtain ⟨f, hf⟩ := T.coyoneda_exact₃ hT g (hv' (g ≫ T.mor₃))
      exact ⟨f, hf.symm⟩
  let H := DerivedCategory.homologyFunctor C n
  have hH : Function.Bijective (fun f : S ⟶ T.obj₃ ↦ H.map f) :=
    DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n
  have hπ : IsIso (H.map T.mor₂) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E n n le_rfl
  constructor
  · intro f g h
    apply hpost.1
    apply hH.1
    simpa only [Functor.map_comp] using
      congrArg (fun a ↦ a ≫ H.map T.mor₂) h
  · intro g
    obtain ⟨a, ha⟩ := hH.2 (g ≫ H.map T.mor₂)
    obtain ⟨f, hf⟩ := hpost.2 a
    refine ⟨f, (cancel_mono (H.map T.mor₂)).1 ?_⟩
    change f ≫ T.mor₂ = a at hf
    change H.map a = g ≫ H.map T.mor₂ at ha
    rw [← H.map_comp, hf, ha]

variable (k : Type u) [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

/-- The canonical evaluation map is bijective on every derived object.
Source: Stacks Project, Tag 064B, Lemma 13.19.8.
(blueprint: lem-sc-module-cup-homology-evaluation-bijective)
Proof: for a projective object P, maps from P[-n] to objects with homology
strictly below n vanish. Choose a strictly bounded-above representative and use
Mathlib's projective-source vanishing theorem. In the canonical truncation triangle
τ<n(A) → A → τ≥n(A), maps from P[-n] to the first term and its shift by 1 vanish.
The exact Hom sequence makes postcomposition with A → τ≥n(A) bijective. Homology
is bijective on maps P[-n] → τ≥n(A) by the source-library shifted-heart comparison,
and H^n(A) → H^n(τ≥n(A)) is an isomorphism. The resulting commutative square proves
that H^n is bijective on maps P[-n] → A. Specialize to the projective free module k,
precompose with the inverse of the canonical H^n(k[-n]) ≅ k, and evaluate at 1
using the linear-map equivalence. Unfolding the explicitly constructed generator
shows that this composite is exactly cupHomologyEvaluation. The argument is the
all-degree version of the proved private calculation in
Sheaf.Algebra.Homology.DerivedFreeModuleHomology. No boundedness on A is used;
the argument includes the zero ring. -/
theorem cupHomologyEvaluation_bijective
    (A : DerivedCategory (ModuleCat.{u} k)) (n : ℤ) :
    Function.Bijective (cupHomologyEvaluation k A n) := by
  let C := ModuleCat.{u} k
  let P := ModuleCat.of k k
  let S := (HomologicalComplex.single C (.up ℤ) n).obj P
  let H := DerivedCategory.homologyFunctor C n
  let ε : H.obj (DerivedCategory.Q.obj S) ≅ P :=
    (DerivedCategory.homologyFunctorFactors C n).app S ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n P
  have hH : Function.Bijective
      (H.map : (DerivedCategory.Q.obj S ⟶ A) → (H.obj (DerivedCategory.Q.obj S) ⟶
        H.obj A)) := projective_single_homology_bijective P A n
  let e : (H.obj (DerivedCategory.Q.obj S) ⟶ H.obj A) ≃ H.obj A :=
    (Iso.homCongr ε (Iso.refl _)).trans
      (ModuleCat.homAddEquiv.trans
        (LinearMap.ringLmapEquivSelf k ℤ (H.obj A)).toAddEquiv).toEquiv
  have he := e.bijective.comp hH
  have heval (f : DerivedCategory.Q.obj S ⟶ A) :
      e (H.map f) = cupHomologyEvaluation k A n f := by
    change (ε.inv ≫ H.map f ≫ 𝟙 _) (1 : k) = _
    rw [Category.comp_id]
    rfl
  simpa only [Function.comp_def, heval] using he

end
end AlgebraicGeometry.Scheme.Modules
