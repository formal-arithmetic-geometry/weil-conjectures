/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Finite powers and the two coordinates of the strict Roos cone

Source: Stacks Project, Cohomology on Sites, Tag 0941;
Bhatt--Scholze, Lemma 3.4.12.
(blueprint: lem-pur-finite-power-roos-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v vA vB
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {A : Type u} {B : Type v} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

private theorem finitePowerRoos_additive : (roosF (A := B)).Additive := by
  constructor
  intro X Y f g
  have hP : roosPmap (f + g) = roosPmap f + roosPmap g := by
    apply Pi.hom_ext
    intro n
    ext k
    simp [roosPmap, HomologicalComplex.add_f_apply, Preadditive.add_comp,
      Preadditive.comp_add]
  apply HomologicalComplex.Hom.ext
  funext k
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono (roosχ Y p).hom).mp
  rw [HomologicalComplex.add_f_apply, Preadditive.add_comp,
    roosF_map_χ, roosF_map_χ, roosF_map_χ, hP]
  apply biprod.hom_ext <;>
    simp [HomologicalComplex.add_f_apply, Preadditive.comp_add]

private theorem finitePowerRoos_product_projection
    {D E : Type*} [Category* D] [Category* E] (G : D ⥤ E) (d : ℕ)
    {X Y : D} [HasProduct (fun _ : Fin d ↦ Y)]
    [HasProduct (fun _ : Fin d ↦ G.obj Y)]
    [PreservesLimit (Discrete.functor (fun _ : Fin d ↦ Y)) G]
    (e : X ≅ ∏ᶜ fun _ : Fin d ↦ Y) (i : Fin d) :
    (G.mapIso e ≪≫ PreservesProduct.iso G (fun _ : Fin d ↦ Y)).hom ≫
        Pi.π (fun _ : Fin d ↦ G.obj Y) i =
      G.map (e.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom,
    Category.assoc, piComparison_comp_π, ← G.map_comp]

/-- Transport through a strict tower isomorphism to a finite power, retaining both
Roos coordinates.

Source: Stacks Project, sites-cohomology.tex, Tag 0941; the product-reindexing
calculation in the proof of Bhatt--Scholze, Lemma 3.4.12.
(blueprint: lem-pur-finite-power-roos-comparison)

Proof: The additive-functor comparison moves F through the product cone. The strict
isomorphism induces an isomorphism of cones. The Roos functor is additive and thus
preserves finite products, giving the last isomorphism. Projecting to each finite
factor and each tower level reduces both coordinate formulas to the normalized
additive-functor comparison and the diagonal coordinate formula for strict maps.
No exactness or derived-category hypothesis is needed. The empty finite power is
included because additive functors preserve the zero object. -/
theorem finitePowerRoosComparison
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (d : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (τ : ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
      (.up ℤ)).obj X) ≅ ∏ᶜ fun _ : Fin d ↦ Y) :
    let E (n : ℕ) := ((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)
    let θ (n : ℕ) := (E n).mapIso τ ≪≫ PreservesProduct.iso (E n)
      (fun _ : Fin d ↦ Y)
    ∃ β : (F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ≅
        ∏ᶜ fun _ : Fin d ↦ roosF.obj Y,
      (∀ (p : ℤ) (n : ℕ) (i : Fin d),
        (β.hom ≫ Pi.π (fun _ : Fin d ↦ roosF.obj Y) i).f (p + 1) ≫
          (roosχ Y p).hom ≫ biprod.fst ≫
            (Pi.π (fun n : ℕ ↦ Y.asFunctor.obj (op n)) n).f p =
        F.map ((roosχ X p).hom ≫ biprod.fst ≫
          (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p) ≫
          ((θ n).hom ≫ Pi.π (fun _ : Fin d ↦ Y.asFunctor.obj (op n)) i).f p) ∧
      (∀ (p : ℤ) (n : ℕ) (i : Fin d),
        (β.hom ≫ Pi.π (fun _ : Fin d ↦ roosF.obj Y) i).f (p + 1) ≫
          (roosχ Y p).hom ≫ biprod.snd ≫
            (Pi.π (fun n : ℕ ↦ Y.asFunctor.obj (op n)) n).f (p + 1) =
        F.map ((roosχ X p).hom ≫ biprod.snd ≫
          (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f (p + 1)) ≫
          ((θ n).hom ≫ Pi.π (fun _ : Fin d ↦ Y.asFunctor.obj (op n)) i).f (p + 1)) := by
  classical
  dsimp only
  let E (n : ℕ) := ((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)
  let θ (n : ℕ) := (E n).mapIso τ ≪≫ PreservesProduct.iso (E n)
    (fun _ : Fin d ↦ Y)
  have hθ (n : ℕ) (i : Fin d) (p : ℤ) :
      ((θ n).hom ≫ Pi.π (fun _ : Fin d ↦ Y.asFunctor.obj (op n)) i).f p =
        ((τ.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i).f p).app (op n) :=
    congrArg (fun f ↦ f.f p) (finitePowerRoos_product_projection (E n) d τ i)
  let : (roosF (A := B)).Additive := finitePowerRoos_additive
  obtain ⟨ρ, hρ, _, _⟩ := strictRoosAdditiveComparison F (fun _ ↦ inferInstance)
  have hcoord (p : ℤ) := hρ X p
  change ∀ p : ℤ, (ρ X).hom.f (p + 1) ≫
      (roosχ ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
        (.up ℤ)).obj X) p).hom =
    F.map (roosχ X p).hom ≫
      F.biprodComparison ((roosP X).X p) ((roosP X).X (p + 1)) ≫
      biprod.map ((piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
        ((piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1)) at hcoord
  let β := ρ X ≪≫ (roosF (A := B)).mapIso τ ≪≫
    PreservesProduct.iso (roosF (A := B)) (fun _ : Fin d ↦ Y)
  have hβ (i : Fin d) :
      β.hom ≫ Pi.π (fun _ : Fin d ↦ roosF.obj Y) i =
        (ρ X).hom ≫ roosF.map (τ.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i) := by
    simp [β, PreservesProduct.iso_hom, Category.assoc, ← Functor.map_comp]
  refine ⟨β, ?_, ?_⟩
  · intro p n i
    rw [hθ]
    rw [hβ]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [reassoc_of% roosF_map_χ (τ.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i) p]
    erw [biprod.map_fst_assoc]
    rw [← Category.assoc, hcoord p]
    simp only [Category.assoc]
    erw [biprod.map_fst_assoc, Functor.biprodComparison_fst_assoc]
    change F.map (roosχ X p).hom ≫ F.map biprod.fst ≫
      (piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p ≫ _ = _
    simp only [Functor.map_comp, Category.assoc]
    congr 2
    have hm := congrArg (fun f ↦ f.f p)
      (Pi.map_π (fun n : ℕ ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (τ.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i)).app (op n)) n)
    simp only [HomologicalComplex.comp_f] at hm
    erw [hm]
    have hc := congrArg (fun f ↦ f.f p)
      (piComparison_comp_π (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n)) n)
    simp only [HomologicalComplex.comp_f] at hc
    erw [← Category.assoc, hc]
    rfl
  · intro p n i
    rw [hθ]
    rw [hβ]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [reassoc_of% roosF_map_χ (τ.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i) p]
    erw [biprod.map_snd_assoc]
    rw [← Category.assoc, hcoord p]
    simp only [Category.assoc]
    erw [biprod.map_snd_assoc, Functor.biprodComparison_snd_assoc]
    change F.map (roosχ X p).hom ≫ F.map biprod.snd ≫
      (piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1) ≫ _ = _
    simp only [Functor.map_comp, Category.assoc]
    congr 2
    have hm := congrArg (fun f ↦ f.f (p + 1))
      (Pi.map_π (fun n : ℕ ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (τ.hom ≫ Pi.π (fun _ : Fin d ↦ Y) i)).app (op n)) n)
    simp only [HomologicalComplex.comp_f] at hm
    erw [hm]
    have hc := congrArg (fun f ↦ f.f (p + 1))
      (piComparison_comp_π (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n)) n)
    simp only [HomologicalComplex.comp_f] at hc
    erw [← Category.assoc, hc]
    rfl

end CategoryTheory
