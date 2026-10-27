/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Detecting monoidal natural transformations on tensor models

Source: the localization universal property and naturality of the tensor comparison.

(blueprint: lem-pur-u2-monoidal-descent).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory

/-- A natural transformation is monoidal if it is monoidal after a lax tensor-model
functor whose unit and tensor maps on a family of representatives are invertible.
The unit follows by naturality and cancellation of the localized unit. The tensor
square on two representatives follows by naturality and cancellation of the localized
tensor map. Naturality transports that square along the representative isomorphisms.
Source: literature/stacks-project/categories.tex; Tags 04VG and 04VK; naturality, cancellation,
and the monoidal natural-transformation equations.
(blueprint: lem-pur-u2-monoidal-descent). -/
theorem monoidal_of_tensor_models {A D E : Type*}
    [Category* A] [Category* D] [Category* E]
    [MonoidalCategory A] [MonoidalCategory D] [MonoidalCategory E]
    (Q : A ⥤ D) [Q.LaxMonoidal] (W : A → Prop)
    [IsIso (ε Q)] (hμ : ∀ a b, W b → IsIso (μ Q a b))
    (hmodels : ∀ X : D, ∃ a, W a ∧ Nonempty (Q.obj a ≅ X))
    {F G : D ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] (τ : F ⟶ G)
    [NatTrans.IsMonoidal (Functor.whiskerLeft Q τ)] : NatTrans.IsMonoidal τ where
  unit := by
    apply (cancel_mono (G.map (ε Q))).1
    rw [Category.assoc, ← τ.naturality]
    simpa only [Functor.LaxMonoidal.comp_ε, Functor.whiskerLeft_app,
      Category.assoc] using NatTrans.IsMonoidal.unit (τ := Functor.whiskerLeft Q τ)
  tensor X Y := by
    have hm (a b : A) (hb : W b) :
        μ F (Q.obj a) (Q.obj b) ≫ τ.app (Q.obj a ⊗ Q.obj b) =
          (τ.app (Q.obj a) ⊗ₘ τ.app (Q.obj b)) ≫ μ G (Q.obj a) (Q.obj b) := by
      have := hμ a b hb
      apply (cancel_mono (G.map (μ Q a b))).1
      rw [Category.assoc, ← τ.naturality]
      simpa only [Functor.LaxMonoidal.comp_μ, Functor.whiskerLeft_app,
        Category.assoc] using NatTrans.IsMonoidal.tensor (τ := Functor.whiskerLeft Q τ) a b
    obtain ⟨a, _, ⟨ia⟩⟩ := hmodels X
    obtain ⟨b, hb, ⟨ib⟩⟩ := hmodels Y
    apply (cancel_epi (F.map ia.hom ⊗ₘ F.map ib.hom)).1
    rw [μ_natural_assoc, τ.naturality, ← Category.assoc, hm a b hb]
    simp only [Category.assoc, ← μ_natural]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, τ.naturality]

/-- A unit comparison is monoidal after localization if its factorization is
monoidal and its comparison before localization is monoidal.
Source: literature/stacks-project/categories.tex; Tags 04VG and 04VK; naturality, cancellation,
and the monoidal natural-transformation equations.
(blueprint: lem-pur-u2-monoidal-descent). -/
theorem monoidal_identity_of_factors {A D : Type*} [Category* A] [Category* D]
    [MonoidalCategory A] [MonoidalCategory D]
    (Q : A ⥤ D) (F : A ⥤ A) (DF : D ⥤ D)
    [Q.LaxMonoidal] [F.LaxMonoidal] [DF.LaxMonoidal]
    (a : Q ⋙ DF ≅ F ⋙ Q) (γ : F ≅ 𝟭 A) (δ : DF ≅ 𝟭 D)
    [NatTrans.IsMonoidal a.hom] [NatTrans.IsMonoidal γ.hom]
    (h : ∀ X, δ.hom.app (Q.obj X) = a.hom.app X ≫ Q.map (γ.hom.app X)) :
    NatTrans.IsMonoidal (Functor.whiskerLeft Q δ.hom) := by
  have he : Functor.whiskerLeft Q δ.hom =
      a.hom ≫ Functor.whiskerRight γ.hom Q ≫ Q.leftUnitor.hom ≫ Q.rightUnitor.inv := by
    ext X
    simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app]
    erw [Category.comp_id, Category.comp_id]
    exact h X
  rw [he]
  infer_instance

/-- Monoidality of a compositor is reflected from a pasting of three monoidal
factorization isomorphisms and a monoidal compositor before localization.
Cancel the third factorization; the remaining pasting consists of associators,
whiskerings and the given comparisons, all of which are monoidal.
Source: literature/stacks-project/categories.tex; Tags 04VG and 04VK; naturality, cancellation,
and the monoidal natural-transformation equations.
(blueprint: lem-pur-u2-monoidal-descent). -/
theorem monoidal_compositor_of_factors
    {A B C D E V : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* V]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C]
    [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory V]
    (Q : A ⥤ D) (L : B ⥤ E) (M : C ⥤ V)
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    (DF : D ⥤ E) (DG : E ⥤ V) (DH : D ⥤ V)
    [Q.LaxMonoidal] [L.LaxMonoidal] [M.LaxMonoidal]
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    [DF.LaxMonoidal] [DG.LaxMonoidal] [DH.LaxMonoidal]
    (a : Q ⋙ DF ≅ F ⋙ L) (b : L ⋙ DG ≅ G ⋙ M) (c : Q ⋙ DH ≅ H ⋙ M)
    (γ : F ⋙ G ≅ H) (δ : DF ⋙ DG ≅ DH)
    [NatTrans.IsMonoidal a.hom] [NatTrans.IsMonoidal b.hom]
    [NatTrans.IsMonoidal c.hom] [NatTrans.IsMonoidal γ.hom]
    (h : ∀ X, δ.hom.app (Q.obj X) ≫ c.hom.app X =
      DG.map (a.hom.app X) ≫ b.hom.app (F.obj X) ≫ M.map (γ.hom.app X)) :
    NatTrans.IsMonoidal (Functor.whiskerLeft Q δ.hom) := by
  have he : Functor.whiskerLeft Q δ.hom =
      (Functor.associator Q DF DG).inv ≫
        Functor.whiskerRight a.hom DG ≫ (Functor.associator F L DG).hom ≫
        Functor.whiskerLeft F b.hom ≫ (Functor.associator F G M).inv ≫
        Functor.whiskerRight γ.hom M ≫ c.inv := by
    ext X
    apply (cancel_mono (c.hom.app X)).1
    simpa only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using h X
  rw [he]
  infer_instance

end CategoryTheory
