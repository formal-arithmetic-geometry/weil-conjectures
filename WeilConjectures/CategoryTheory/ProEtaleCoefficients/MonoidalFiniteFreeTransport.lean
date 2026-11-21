/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!
# Additive monoidal transport of a finite free internal module

The biproducts are taken in the existing category of internal modules. Their actions
are componentwise, as constructed in `CategoryTheory.ModuleObjects.Abelian`.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

-- Mathlib exposes this finite-to-binary conversion as a theorem, not an instance.
attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.Functor

/-- An additive strong monoidal functor transports a specified finite free basis,
including its coordinate maps and the Kronecker and finite-sum identities. -/
theorem monoidalFiniteFreeTransport
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [MonoidalCategory C]
    [HasFiniteBiproducts C] [MonoidalPreadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [MonoidalCategory D]
    [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (P : C ⥤ D) [P.Additive] [P.Monoidal] (R : C) [MonObj R]
    (M : Mod C R) (n : ℕ) (θ : (⨁ fun _ : Fin n => Mod.regular R) ≅ M) :
    ∃ α : (⨁ fun _ : Fin n => Mod.regular (P.obj R)) ≅ (P.mapMod R).obj M,
      (∀ i : Fin n,
        (biproduct.ι (fun _ : Fin n => Mod.regular (P.obj R)) i).hom ≫ α.hom.hom =
          P.map ((biproduct.ι (fun _ : Fin n => Mod.regular R) i).hom ≫ θ.hom.hom)) ∧
      (∀ i : Fin n,
        α.inv.hom ≫ (biproduct.π (fun _ : Fin n => Mod.regular (P.obj R)) i).hom =
          P.map (θ.inv.hom ≫ (biproduct.π (fun _ : Fin n => Mod.regular R) i).hom)) ∧
      (∀ i j : Fin n,
        P.map ((biproduct.ι (fun _ : Fin n => Mod.regular R) j).hom ≫ θ.hom.hom) ≫
            P.map (θ.inv.hom ≫ (biproduct.π (fun _ : Fin n => Mod.regular R) i).hom) =
          if i = j then 𝟙 (P.obj R) else 0) ∧
      (∑ i : Fin n,
        P.map (θ.inv.hom ≫ (biproduct.π (fun _ : Fin n => Mod.regular R) i).hom) ≫
          P.map ((biproduct.ι (fun _ : Fin n => Mod.regular R) i).hom ≫ θ.hom.hom)) =
        𝟙 (P.obj M.X) := by
  classical
  let F := P.mapMod R
  let e : (⨁ fun _ : Fin n => Mod.regular (P.obj R)) ≅ F.obj M :=
    (F.mapBiproduct (fun _ : Fin n => Mod.regular R)).symm ≪≫ F.mapIso θ
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i
    change ((biproduct.ι (fun _ : Fin n => Mod.regular (P.obj R)) i) ≫ e.hom).hom = _
    simp [e, F]
  · intro i
    have h : e.inv ≫ biproduct.π _ i = F.map (θ.inv ≫ biproduct.π _ i) := by
      change ((F.mapIso θ).inv ≫ (F.mapBiproduct _).hom) ≫ _ = _
      rw [Category.assoc, mapBiproduct_hom]
      erw [biproduct.lift_π]
      exact (F.map_comp _ _).symm
    exact congrArg Mod.Hom.hom h
  · intro i j
    have h : (biproduct.ι (fun _ : Fin n => Mod.regular R) j ≫ θ.hom) ≫
        (θ.inv ≫ biproduct.π _ i) =
        if i = j then 𝟙 (Mod.regular R) else 0 := by
      by_cases hij : i = j
      · subst j
        simp
      · simp [Category.assoc, hij, Ne.symm hij]
    calc
      _ = P.map (((biproduct.ι (fun _ : Fin n => Mod.regular R) j ≫ θ.hom) ≫
          (θ.inv ≫ biproduct.π _ i)).hom) := by rw [← P.map_comp]; rfl
      _ = _ := by rw [h]; split_ifs <;> simp [Mod.regular]
  · have h : (∑ i : Fin n, (θ.inv ≫ biproduct.π _ i) ≫
        (biproduct.ι (fun _ : Fin n => Mod.regular R) i ≫ θ.hom)) = 𝟙 M := by
      calc
        _ = θ.inv ≫ (∑ i : Fin n, biproduct.π _ i ≫
            biproduct.ι (fun _ : Fin n => Mod.regular R) i) ≫ θ.hom := by
          simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        _ = _ := by rw [biproduct.total, Category.id_comp, θ.inv_hom_id]
    let G := Mod.forget R ⋙ P
    calc
      _ = G.map (∑ i : Fin n, (θ.inv ≫ biproduct.π _ i) ≫
          (biproduct.ι (fun _ : Fin n => Mod.regular R) i ≫ θ.hom)) := by
        rw [G.map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        change P.map (_ ≫ _) ≫ P.map (_ ≫ _) = P.map _
        rw [← P.map_comp]
        rfl
      _ = _ := by rw [h, G.map_id]; rfl

end CategoryTheory.Functor
