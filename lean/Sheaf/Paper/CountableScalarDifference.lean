/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.Paper.ExactEndomorphismIsoClosure

/-! # The repeated-scalar product differential

Source: Bhatt--Scholze, Lemma 3.4.14 and Proposition 3.1.11.
(blueprint: lem-sfb-countable-scalar-difference-closure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CountableScalarDifference

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

/-- The countable power functor, with its actual categorical product.
Source: Bhatt--Scholze, Proposition 3.1.11
(blueprint: lem-sfb-countable-scalar-difference-closure). -/
def power : A ⥤ A where
  obj M := ∏ᶜ (fun _ : ℕ ↦ M)
  map f := Limits.Pi.map (fun _ : ℕ ↦ f)
  map_id M := by simp
  map_comp f g := by simp only [← Limits.Pi.map_comp_map]

private def powerIso : (Functor.const (Discrete ℕ) : A ⥤ _) ⋙ lim ≅ power :=
  NatIso.ofComponents
    (fun M ↦ HasLimit.isoOfNatIso (Discrete.natIsoFunctor
      (F := (Functor.const (Discrete ℕ)).obj M))) (by
      intro M N f
      apply limit.hom_ext
      rintro ⟨n⟩
      dsimp only [Functor.comp_map, power]
      simp only [Category.assoc, Limits.Pi.map_π,
        HasLimit.isoOfNatIso_hom_π_assoc, Discrete.natIsoFunctor_hom_app]
      rw [HasLimit.isoOfNatIso_hom_π]
      change limMap ((Functor.const (Discrete ℕ)).map f) ≫
          limit.π ((Functor.const (Discrete ℕ)).obj N) ⟨n⟩ ≫ 𝟙 N =
        limit.π ((Functor.const (Discrete ℕ)).obj M) ⟨n⟩ ≫ 𝟙 M ≫ f
      rw [limMap_π_assoc]
      simp)

/-- The repeated-scalar shift has coordinate `n` equal to the scalar times coordinate
`n+1`. Source: Bhatt--Scholze, Lemma 3.4.14
(blueprint: lem-sfb-countable-scalar-difference-closure). -/
def scalarShift (a : 𝟭 A ⟶ 𝟭 A) : power (A := A) ⟶ power where
  app M := Limits.Pi.lift (f := fun _ : ℕ ↦ M)
    (fun n : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ M) (n + 1) ≫ a.app M)
  naturality {M N} f := by
    apply Limits.Pi.hom_ext
    intro n
    change (Limits.Pi.map (fun _ : ℕ ↦ f) ≫
        Limits.Pi.lift (f := fun _ : ℕ ↦ N)
          (fun k : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ N) (k + 1) ≫ a.app N)) ≫
          Limits.Pi.π (fun _ : ℕ ↦ N) n =
      (Limits.Pi.lift (f := fun _ : ℕ ↦ M)
          (fun k : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ M) (k + 1) ≫ a.app M) ≫
        Limits.Pi.map (fun _ : ℕ ↦ f)) ≫ Limits.Pi.π (fun _ : ℕ ↦ N) n
    have hN := Limits.Pi.lift_π (f := fun _ : ℕ ↦ N)
      (fun k : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ N) (k + 1) ≫ a.app N) n
    have hM := Limits.Pi.lift_π (f := fun _ : ℕ ↦ M)
      (fun k : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ M) (k + 1) ≫ a.app M) n
    simp only [Category.assoc, Limits.Pi.map_π]
    rw [hN, reassoc_of% hM, Limits.Pi.map_π_assoc]
    exact congrArg (fun k ↦ Limits.Pi.π (fun _ : ℕ ↦ M) (n + 1) ≫ k)
      (a.naturality f)


/-- The actual two-term Roos differential `1 - scalar shift`.
Source: Bhatt--Scholze, Proposition 3.1.11 and Lemma 3.4.14
(blueprint: lem-sfb-countable-scalar-difference-closure). -/
def difference (a : 𝟭 A ⟶ 𝟭 A) : power (A := A) ⟶ power :=
  𝟙 power - scalarShift a

/-- If countable products preserve epimorphisms, invertibility of the repeated-scalar
product differential is closed under kernels, cokernels, images and extensions.

Source: Bhatt--Scholze, Proposition 3.1.11 and Lemma 3.4.14, printed pp.17,23.
(blueprint: lem-sfb-countable-scalar-difference-closure).

Proof: Countable power preserves limits, hence kernels. The stated product-of-epis
hypothesis says it preserves epimorphisms, so it preserves homology and finite
colimits as well. Its natural endomorphism `1 - scalar shift` therefore satisfies
the exact-functor invertibility-locus lemma. This only uses exactness of products,
not surjectivity or injectivity of the scalar on the modules. -/
theorem iso_closure (a : 𝟭 A ⟶ 𝟭 A)
    (hE : ∀ (M N : A) (f : M ⟶ N), Epi f →
      Epi (Limits.Pi.map (fun _ : ℕ ↦ f))) :
    (∀ (M N : A) (g : M ⟶ N), IsIso ((difference a).app M) →
      IsIso ((difference a).app N) → IsIso ((difference a).app (kernel g)) ∧
      IsIso ((difference a).app (cokernel g)) ∧ IsIso ((difference a).app (image g))) ∧
    (∀ S : ShortComplex A, S.ShortExact → IsIso ((difference a).app S.X₁) →
      IsIso ((difference a).app S.X₃) → IsIso ((difference a).app S.X₂)) := by
  let G : A ⥤ A := power
  have : PreservesFiniteLimits G := by
    have : PreservesFiniteLimits ((Functor.const (Discrete ℕ) : A ⥤ _) ⋙ lim) :=
      inferInstance
    exact preservesFiniteLimits_of_natIso powerIso
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : G.PreservesEpimorphisms := ⟨fun {M N} f hf ↦ by
    change Epi (Limits.Pi.map (fun _ : ℕ ↦ f))
    exact hE M N f hf⟩
  have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
  have : PreservesFiniteColimits G :=
    Functor.preservesFiniteColimits_of_preservesHomology G
  exact exactEndomorphism_iso_closure G (difference a)

end CategoryTheory.CountableScalarDifference
