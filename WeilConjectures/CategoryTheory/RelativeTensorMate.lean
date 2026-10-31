/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.HomCongr

/-!
# Invertibility of a mate on a restricted adjunction domain

Source: the current blueprint lem-pur-coprojection, test-object Hom calculation
(blueprint: lem-pur-relative-tensor-mate-isomorphism).
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory

/-- A counit-normalized comparison is invertible if tensor equivalences transport its
restricted representing Hom bijections.
Source: blueprint lem-pur-coprojection.proof.md, test-object Hom calculation and Yoneda
(blueprint: lem-pur-relative-tensor-mate-isomorphism).

Proof: For a test object E(A), compose full faithfulness of E, the first representing
bijection, full faithfulness of T, precomposition by alpha, and the inverse second
representing bijection. Naturality of alpha and the normalization of b identify this
composite with postcomposition by b. For an arbitrary test object B in P, use the counit
E(E.inverse(B)) isomorphic to B and preservation of P by E.inverse. Surjectivity at S gives
an inverse c, and injectivity at E(R) proves the other inverse equation. -/
theorem relativeTensorMate_isIso
    {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (F : C ⥤ D) (E : C ≌ C) (T : D ⥤ D) [T.Full] [T.Faithful]
    (α : E.functor ⋙ F ≅ F ⋙ T)
    (R S : C) (K : D) (ε : F.obj R ⟶ K) (ε' : F.obj S ⟶ T.obj K)
    (hS : P S) (hER : P (E.functor.obj R))
    (hInv : ∀ A, P A → P (E.inverse.obj A))
    (h : ∀ A, P A → Function.Bijective (fun f : A ⟶ R ↦ F.map f ≫ ε))
    (h' : ∀ A, P A → Function.Bijective (fun f : A ⟶ S ↦ F.map f ≫ ε'))
    (b : E.functor.obj R ⟶ S)
    (hb : F.map b ≫ ε' = α.hom.app R ≫ T.map ε) : IsIso b := by
  have h₁ (A : C) (hA : P A) (hEA : P (E.functor.obj A)) :
      Function.Bijective (fun f : E.functor.obj A ⟶ E.functor.obj R ↦ f ≫ b) := by
    let e : (E.functor.obj A ⟶ E.functor.obj R) ≃ (E.functor.obj A ⟶ S) :=
      (Functor.FullyFaithful.ofFullyFaithful E.functor).homEquiv.symm |>.trans
        ((Equiv.ofBijective _ (h A hA)).trans
          ((Functor.FullyFaithful.ofFullyFaithful T).homEquiv.trans
            ((Iso.homCongr (α.app A).symm (Iso.refl _)).trans
              (Equiv.ofBijective _ (h' _ hEA)).symm)))
    have he (f : E.functor.obj A ⟶ E.functor.obj R) : e f = f ≫ b := by
      obtain ⟨t, rfl⟩ := E.functor.map_surjective f
      apply (Equiv.ofBijective _ (h' _ hEA)).injective
      dsimp only [e, Equiv.trans_apply]
      erw [Equiv.apply_symm_apply]
      simp only [Functor.FullyFaithful.homEquiv_apply,
        Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.preimage_map,
        Equiv.ofBijective_apply]
      rw [F.map_comp, Category.assoc, hb]
      have ht := α.hom.naturality t
      dsimp only [Functor.comp_map] at ht
      rw [← Category.assoc, ht]
      change α.hom.app A ≫ T.map (F.map t ≫ ε) ≫ 𝟙 _ = _
      simp only [Functor.map_comp, Category.comp_id, Category.assoc]
    simpa only [← he] using e.bijective
  have h₂ (A : C) (hA : P A) : Function.Bijective (fun f : A ⟶ E.functor.obj R ↦ f ≫ b) := by
    let u := E.counitIso.app A
    have hEA : P (E.functor.obj (E.inverse.obj A)) := P.prop_of_iso u.symm hA
    let e : (A ⟶ E.functor.obj R) ≃ (A ⟶ S) :=
      (Iso.homCongr u.symm (Iso.refl _)).trans
        ((Equiv.ofBijective _ (h₁ _ (hInv A hA) hEA)).trans
          (Iso.homCongr u (Iso.refl _)))
    have he : ⇑e = (fun f : A ⟶ E.functor.obj R ↦ f ≫ b) := by
      funext f
      simp [e, Iso.homCongr_apply, Category.assoc]
    exact he ▸ e.bijective
  obtain ⟨c, hc⟩ := (h₂ S hS).2 (𝟙 S)
  refine ⟨⟨c, ?_, hc⟩⟩
  apply (h₂ _ hER).1
  simp only [Category.assoc, hc, Category.comp_id, Category.id_comp]

end CategoryTheory
