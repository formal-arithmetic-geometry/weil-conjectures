module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Componentwise surjectivity on maps out of an object implies surjectivity on a
finite coproduct of targets in an additive category.

Source: the finite biproduct argument in Krause, Localization theory, Section 6.2.
The finite coproduct is a biproduct, so a map into it is the finite sum of its
components; lift each component and reassemble the sum.
(blueprint: new-sfb-derived-perfect-small-class-finite-lifting)
-/
theorem derived_finite_coproduct_surjective
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (I : Type v) (X Y : I → DerivedCategory A) (f : ∀ i, X i ⟶ Y i)
    (J : Type v) [Finite J] (a : J → I) (U : DerivedCategory A)
    (hf : ∀ j, Function.Surjective
      (fun g : U ⟶ X (a j) ↦ g ≫ f (a j))) :
    Function.Surjective
      (fun g : U ⟶ ∐ fun j ↦ X (a j) ↦
        g ≫ Limits.Sigma.map (fun j ↦ f (a j))) := by
  classical
  intro g
  let eX := biproduct.isoCoproduct (fun j ↦ X (a j))
  let eY := biproduct.isoCoproduct (fun j ↦ Y (a j))
  choose q hq using fun j ↦ hf j (g ≫ Sigma.π (fun j ↦ Y (a j)) j)
  refine ⟨biproduct.lift q ≫ eX.hom, ?_⟩
  apply (cancel_mono eY.inv).1
  have hy (j : J) : Sigma.desc (biproduct.ι (fun j ↦ Y (a j))) ≫
      biproduct.π (fun j ↦ Y (a j)) j = Sigma.π (fun j ↦ Y (a j)) j := by
    apply Sigma.hom_ext
    intro k
    by_cases h : k = j
    · subst h; simp [Sigma.π]
    · simp [Sigma.π, h]
  have hpi (j : J) : Limits.Sigma.map (fun j ↦ f (a j)) ≫
      Sigma.π (fun j ↦ Y (a j)) j =
        Sigma.π (fun j ↦ X (a j)) j ≫ f (a j) := by
    apply Sigma.hom_ext
    intro k
    by_cases h : k = j
    · subst h; simp [Sigma.π]
    · simp [Sigma.π, h]
  have hx (j : J) : biproduct.desc (Sigma.ι (fun j ↦ X (a j))) ≫
      Sigma.π (fun j ↦ X (a j)) j = biproduct.π (fun j ↦ X (a j)) j := by
    apply biproduct.hom_ext'
    intro k
    by_cases h : k = j
    · subst h; simp [Sigma.π]
    · simp [Sigma.π, h]
  have hmap : eX.hom ≫ Limits.Sigma.map (fun j ↦ f (a j)) ≫ eY.inv =
      biproduct.map (fun j ↦ f (a j)) := by
    apply biproduct.hom_ext
    intro j
    simp only [eX, eY, biproduct.isoCoproduct_hom, biproduct.isoCoproduct_inv]
    simp only [Category.assoc]
    rw [hy, hpi, ← Category.assoc, hx]
    exact (biproduct.map_π (fun j ↦ f (a j)) j).symm
  simp only [Category.assoc]
  rw [hmap]
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc]
  change biproduct.lift q ≫ biproduct.map (fun j ↦ f (a j)) ≫
      biproduct.π (fun j ↦ Y (a j)) j =
    g ≫ eY.inv ≫ biproduct.π (fun j ↦ Y (a j)) j
  rw [biproduct.map_π, biproduct.lift_π_assoc]
  rw [show eY.inv = Sigma.desc (biproduct.ι (fun j ↦ Y (a j))) by
    simp [eY, biproduct.isoCoproduct_inv]]
  rw [hy]
  exact hq j

end CategoryTheory
