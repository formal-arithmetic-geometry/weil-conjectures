/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Comparing functors computed by the same resolving models

Source: Stacks Project, Derived Categories, Tags 06XN and 05SE.
(blueprint: lem-pbc-resolving-model-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u v w uD vD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- Natural computations on a resolving class determine a functor on the derived category.
Source: Stacks Project, Derived Categories, Tags 06XN and 05SE.
(blueprint: lem-pbc-resolving-model-comparison).

Proof: the first comparison and its invertibility on the resolving class show that F
inverts quasi-isomorphisms between members of that class. The resolving-class theorem
supplies a universal left-derived pair L, with invertible counit on the same class.
Its universal property gives a transformation from each proposed functor to L.
The factorization equation makes this transformation invertible on the resolving class.
Resolve any homotopy object; naturality along the localized resolution, an isomorphism,
makes the transformation invertible there too. The homotopy localization is essentially
surjective, so both transformations are natural isomorphisms everywhere. Compose the
first with the inverse of the second. This argument also applies to the zero category
and imposes no boundedness condition on the resolving objects. -/
theorem nonempty_iso_of_resolving_models
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (D : Type uD) [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : HomotopyCategory A (.up ℤ) ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (L₁ L₂ : DerivedCategory A ⥤ D)
    (α₁ : DerivedCategory.Qh ⋙ L₁ ⟶ F)
    (α₂ : DerivedCategory.Qh ⋙ L₂ ⟶ F)
    (h₁ : ∀ X, X ∈ P → IsIso (α₁.app X))
    (h₂ : ∀ X, X ∈ P → IsIso (α₂.app X)) : Nonempty (L₁ ≅ L₂) := by
  classical
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  have hinv : ∀ X Y : HomotopyCategory A (.up ℤ), ∀ s : X ⟶ Y,
      X ∈ P → Y ∈ P → W s → IsIso (F.map s) := by
    intro X Y s hX hY hs
    have := h₁ X hX
    have := h₁ Y hY
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    have hn := α₁.naturality s
    rw [← isIso_comp_left_iff (α₁.app X), ← hn]
    change IsIso (L₁.map (Q.map s) ≫ α₁.app Y)
    infer_instance
  obtain ⟨_, L, ε, hL, _, hε⟩ := leftDerived_from_resolvingClass A D F P hres hinv
  let := hL
  have compare (G : DerivedCategory A ⥤ D) (α : Q ⋙ G ⟶ F)
      (hα : ∀ X, X ∈ P → IsIso (α.app X)) : Nonempty (G ≅ L) := by
    let τ := L.leftDerivedLift ε W G α
    have hτ (X : HomotopyCategory A (.up ℤ)) : IsIso (τ.app (Q.obj X)) := by
      obtain ⟨Y, s, hY, hs⟩ := hres X
      have := hε Y hY
      have := hα Y hY
      have hf : τ.app (Q.obj Y) ≫ ε.app Y = α.app Y :=
        L.leftDerived_fac_app ε W G α Y
      have : IsIso (τ.app (Q.obj Y)) := by
        have heq : τ.app (Q.obj Y) = α.app Y ≫ CategoryTheory.inv (ε.app Y) := by
          rw [← hf]
          simp
        rw [heq]
        infer_instance
      have : IsIso (Q.map s) := Localization.inverts Q W s hs
      rw [← isIso_comp_left_iff (G.map (Q.map s)), τ.naturality]
      infer_instance
    have : ∀ X, IsIso ((whiskerLeft Q τ).app X) := hτ
    have : IsIso (whiskerLeft Q τ) := NatIso.isIso_of_isIso_app _
    have : Q.EssSurj := Localization.essSurj Q W
    have : IsIso (((whiskeringLeft _ _ D).obj Q).map τ) :=
      inferInstanceAs (IsIso (whiskerLeft Q τ))
    have : IsIso τ := isIso_of_reflects_iso τ ((whiskeringLeft _ _ D).obj Q)
    exact ⟨asIso τ⟩
  obtain ⟨e₁⟩ := compare L₁ α₁ h₁
  obtain ⟨e₂⟩ := compare L₂ α₂ h₂
  exact ⟨e₁ ≪≫ e₂.symm⟩

end CategoryTheory.Functor
