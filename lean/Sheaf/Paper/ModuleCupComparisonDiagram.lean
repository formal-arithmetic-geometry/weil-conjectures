module

public import Mathlib.CategoryTheory.Monoidal.Category

/-! # Transport of a monoidal comparison diagram

Source: Stacks Project, Tag 0FKU, the comparison square in Lemma 20.31.3.
(blueprint: new-module-cup-comparison-diagram)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe v
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme.Modules

private theorem transport_natural_pairing
    {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]
    (R : C ⥤ E)
    (μ : ∀ A B : C, R.obj A ⊗ R.obj B ⟶ R.obj (A ⊗ B))
    (hn : ∀ (A A' B B' : C) (f : A ⟶ A') (g : B ⟶ B'),
      (R.map f ⊗ₘ R.map g) ≫ μ A' B' = μ A B ≫ R.map (f ⊗ₘ g))
    {A B K L M N : C} (a : A ⟶ K) (b : B ⟶ L) [IsIso a] [IsIso b]
    {U V : E} (x : U ⟶ R.obj K) (y : V ⟶ R.obj L)
    (m : K ⊗ L ⟶ M) (t : M ⟶ N) :
    ((x ≫ R.map (inv a)) ⊗ₘ (y ≫ R.map (inv b))) ≫ μ A B ≫
      R.map ((a ⊗ₘ b) ≫ m ≫ t) =
    (x ⊗ₘ y) ≫ μ K L ≫ R.map m ≫ R.map t := by
  rw [← tensorHom_comp_tensorHom, Category.assoc,
    reassoc_of% (hn K A L B (inv a) (inv b))]
  simp only [Functor.map_comp]
  rw [← R.map_comp_assoc, tensorHom_comp_tensorHom]
  simp

/-- Transport of a monoidal comparison diagram through a functor.
Source: Stacks Project, Tag 0FKU, the comparison square in the proof of
Lemma 20.31.3.  The proof is the formal associativity and naturality chase.
(blueprint: new-module-cup-comparison-diagram)
Proof: rewrite `d` using `hd`, apply naturality of `μ` to the two inverse
augmentation maps, then append `R.map f` and `R.map w` to `hdiag`; use
`hcomp` to replace `Q.map g ≫ γ` by `β ≫ R.map f`.
-/
theorem moduleCup_comparison_diagram
    {C E C₀ : Type v} [Category C] [Category E] [Category C₀]
    [MonoidalCategory C] [MonoidalCategory E]
    (R : C ⥤ E) (Q : C₀ ⥤ E)
    (μ : ∀ A B : C, R.obj A ⊗ R.obj B ⟶ R.obj (A ⊗ B))
    (hn : ∀ (A A' B B' : C) (f : A ⟶ A') (g : B ⟶ B'),
      (R.map f ⊗ₘ R.map g) ≫ μ A' B' = μ A B ≫ R.map (f ⊗ₘ g))
    {A B K L M N O : C} (a : A ⟶ K) (b : B ⟶ L) [IsIso a] [IsIso b]
    {U V : E} (x : U ⟶ R.obj K) (y : V ⟶ R.obj L)
    (m : K ⊗ L ⟶ M) (f : M ⟶ N) (w : N ⟶ O)
    (d : A ⊗ B ⟶ O) (hd : d = (a ⊗ₘ b) ≫ m ≫ f ≫ w)
    {P T Z : C₀} (c : U ⊗ V ⟶ Q.obj P) (ν : P ⟶ T) (g : T ⟶ Z)
    (β : Q.obj T ⟶ R.obj M) (γ : Q.obj Z ⟶ R.obj N)
    (hdiag : (x ⊗ₘ y) ≫ μ K L ≫ R.map m = c ≫ Q.map ν ≫ β)
    (hcomp : Q.map g ≫ γ = β ≫ R.map f) :
    ((x ≫ R.map (inv a)) ⊗ₘ (y ≫ R.map (inv b))) ≫ μ A B ≫ R.map d =
      c ≫ Q.map (ν ≫ g) ≫ γ ≫ R.map w := by
  rw [hd, transport_natural_pairing R μ hn]
  simp only [Functor.map_comp, Category.assoc]
  have h := congrArg (fun s ↦ s ≫ R.map f ≫ R.map w) hdiag
  simp only [Category.assoc] at h
  rw [← reassoc_of% hcomp] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
