/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Abelian.InjectiveSESBoundaryLift

/-!
# The derived unit on a short exact sequence of bounded below injective complexes

Source: Stacks Project, Derived Categories, Tags 014Q, 0159 and 015B.
(blueprint: lem-sc-p1-right-derived-injective-boundary).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
  [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

private lemma inverse_shifted_naturality
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] {X Y : C}
    [IsIso (τ.app X)] [IsIso (τ.app Y)] (f : X ⟶ Y⟦(1 : ℤ)⟧) :
    ShiftedHom.map f G ≫ (inv (τ.app Y))⟦(1 : ℤ)⟧' =
      inv (τ.app X) ≫ ShiftedHom.map f F := by
  have h := ShiftedHom.map_naturality f τ
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  apply (cancel_epi (τ.app X)).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% h, ← Functor.map_comp]
  simp

/-- The inverse derived unit on a bounded below injective complex, followed by
localization's quotient factorization.

Source: Stacks Project, Derived Categories, Tag 015B.
(blueprint: lem-sc-p1-right-derived-injective-boundary). -/
noncomputable def boundedBelowInjectiveComparison
    (v : A ⥤ B) [v.Additive] (K : CochainComplex.Plus A)
    [∀ n : ℤ, Injective (K.obj.X n)] :
    (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj
        (DerivedCategory.Plus.Q.obj K) ⟶
      DerivedCategory.Q.obj ((v.mapHomologicalComplex (.up ℤ)).obj K.obj) :=
  DerivedCategory.Plus.ι.map
      (inv (v.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj K))) ≫
    (DerivedCategory.quotientCompQhIso B).hom.app _

/-- Lift the canonical SES boundary through the full inclusion of the bounded
below derived category, after the quotient factorization on its endpoints.

Source: Stacks Project, Derived Categories, Tag 014Q.
(blueprint: lem-sc-p1-right-derived-injective-boundary). -/
noncomputable def boundedBelowSESBoundary (H : ShortComplex (CochainComplex.Plus A))
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact) :
    DerivedCategory.Plus.Q.obj H.X₃ ⟶ (DerivedCategory.Plus.Q.obj H.X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage
    ((DerivedCategory.quotientCompQhIso A).hom.app H.X₃.obj ≫
      DerivedCategory.triangleOfSESδ hH ≫
      ((DerivedCategory.quotientCompQhIso A).inv.app H.X₁.obj)⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        (DerivedCategory.Plus.Q.obj H.X₁))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse derived units carry the boundary of an injective-complex SES to
that of its termwise image. This is a resolution-level assertion: it does not
involve augmentations, single objects or comparisons with chosen resolutions.

Source: Stacks Project, Derived Categories, Tags 014Q, 0159 and 015B;
fixed-horseshoe comparison Steps 1 and 3.
(blueprint: lem-sc-p1-right-derived-injective-boundary).

Proof: Split each degree row using injectivity of its first object. The proved
DerivedCategory.triangleOfSESδ_eq_degreewiseSplit identifies the source boundary
with localization of CochainComplex.homOfDegreewiseSplit. Apply the additive
functor to the splittings. Its image connecting chain map agrees with the image
of the source connecting chain map followed by the termwise shift comparison:
in each degree both maps are section, image differential, retraction. The same
proved boundary comparison identifies the image SES boundary with this map.
Lift the source connecting map to the bounded below complexes, whose shift is
again bounded below. Naturality of the derived unit at this map, followed by its
shift compatibility, gives the boundary square for the units. The endpoint
units are isomorphisms because the endpoint complexes have injective terms;
invert them. Finally use quotient-factorization naturality and shift
compatibility to obtain exactly the equation with the displayed definitions.
This argument works for zero rows and any common lower bound.
-/
theorem rightDerived_injectiveComplex_boundary
    (v : A ⥤ B) [v.Additive] (H : ShortComplex (CochainComplex.Plus A))
    [∀ n : ℤ, Injective (H.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H.X₃.obj.X n)]
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (hvH : ((H.map (CochainComplex.plus A).ι).map
      (v.mapHomologicalComplex (.up ℤ))).ShortExact) :
    (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (boundedBelowSESBoundary H hH) ≫
      ((v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Plus.Q.obj H.X₁) ≫
      (boundedBelowInjectiveComparison v H.X₁)⟦(1 : ℤ)⟧' =
    boundedBelowInjectiveComparison v H.X₃ ≫ DerivedCategory.triangleOfSESδ hvH := by
  let q := HomotopyCategory.Plus.quotient A
  let F := (v.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ DerivedCategory.Plus.ι
  let G := (DerivedCategory.Plus.Qh ⋙ v.rightDerivedFunctorPlus) ⋙ DerivedCategory.Plus.ι
  let τ : F ⟶ G := Functor.whiskerRight v.rightDerivedFunctorPlusUnit
    DerivedCategory.Plus.ι
  have hτ : NatTrans.CommShift τ ℤ := by
    dsimp [τ, F, G]
    infer_instance
  have hi (K : CochainComplex.Plus A) [∀ n : ℤ, Injective (K.obj.X n)] :
      IsIso (τ.app (q.obj K)) := by
    dsimp [τ, q]
    infer_instance
  obtain ⟨f, hf, hvf⟩ := injective_ses_homotopy_boundary_lift v H hH hvH
  have hd : ShiftedHom.map f DerivedCategory.Plus.Qh =
      boundedBelowSESBoundary H hH := by
    apply DerivedCategory.Plus.ι.map_injective
    unfold boundedBelowSESBoundary
    rw [Functor.map_preimage]
    have hs := hf
    rw [ShiftedHom.comp_map] at hs
    dsimp only [ShiftedHom.map] at hs
    apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
      (DerivedCategory.Plus.Q.obj H.X₁))).1
    dsimp only [DerivedCategory.Plus.Q, Functor.comp_obj]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app]
    apply (cancel_mono
      (((DerivedCategory.quotientCompQhIso A).hom.app H.X₁.obj)⟦(1 : ℤ)⟧')).1
    simp only [Category.assoc]
    erw [Category.id_comp
      (((DerivedCategory.quotientCompQhIso A).hom.app H.X₁.obj)⟦(1 : ℤ)⟧')]
    erw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]
    convert hs using 1 <;>
      simp only [ShiftedHom.map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
        Functor.comp_obj, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    all_goals
      repeat first | erw [Category.id_comp] | erw [Category.comp_id] |
        erw [Functor.map_id]
  have hn :
      ShiftedHom.map (ShiftedHom.map f DerivedCategory.Plus.Qh)
          (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) ≫
        (DerivedCategory.Plus.ι.map
          (inv (v.rightDerivedFunctorPlusUnit.app (q.obj H.X₁)) ))⟦(1 : ℤ)⟧' =
      DerivedCategory.Plus.ι.map
          (inv (v.rightDerivedFunctorPlusUnit.app (q.obj H.X₃))) ≫
        ShiftedHom.map f F := by
    have hn := inverse_shifted_naturality τ f
    simpa only [ShiftedHom.map, F, G, τ, Functor.whiskerRight_app,
      Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.map_comp,
      Functor.comp_obj, Functor.map_inv, Category.assoc] using hn
  have hn' := congrArg (fun k ↦ k ≫
    ((DerivedCategory.quotientCompQhIso B).hom.app
      ((v.mapHomologicalComplex (.up ℤ)).obj H.X₁.obj))⟦(1 : ℤ)⟧') hn
  simp only [Category.assoc] at hn'
  erw [hvf] at hn'
  rw [← hd]
  simp only [ShiftedHom.map, boundedBelowInjectiveComparison, Functor.map_comp,
    Category.assoc] at hn' ⊢
  convert hn' using 1 <;> rfl

end CategoryTheory
