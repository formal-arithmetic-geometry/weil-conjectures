/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleEventualHomLift
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekConstantConstructible

/-!
# Descent of arrows between finite sums of affine etale free module sheaves

Source: Stacks Project, Tags 09YU (3), 09YQ, 095N and 03S6.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An arrow between finite sums of affine etale free sheaves descends to an arrow
between constructible module sheaves at a common stage
(Stacks, Tags 09YU, 095N, 09YQ, 03S6). -/
theorem exists_affine_free_etaleModule_arrow_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (n m : ℕ) (U : Fin n → c.pt.Etale) (V : Fin m → c.pt.Etale)
    (hU : ∀ k : Fin n, IsAffine (U k).left)
    (hV : ∀ k : Fin m, IsAffine (V k).left) :
    let P : c.pt.Etale → Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      fun W => (presheafToSheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∀ f : (∐ fun j : Fin m => P (V j)) ⟶ (∐ fun k : Fin n => P (U k)),
      ∃ (i : I)
        (A B : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (a : A ⟶ B),
        IsConstructibleEtaleModuleSheaf A ∧ IsConstructibleEtaleModuleSheaf B ∧
        ∃ (eA : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj A ≅
            (∐ fun j : Fin m => P (V j)))
          (eB : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj B ≅
            (∐ fun k : Fin n => P (U k))),
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).map a ≫ eB.hom =
            eA.hom ≫ f := by
  classical
  intro P f
  obtain ⟨i, WU, WV, hWU, hWV, ⟨eB⟩, ⟨eA⟩⟩ :=
    exists_affine_free_etaleModule_family_models D c hc Λ n m U V hU hV
  let Q : (D.obj (op i)).Etale →
      Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun W ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))
  let A₀ := ∐ fun k : Fin m ↦ Q (WV k)
  let B₀ := ∐ fun k : Fin n ↦ Q (WU k)
  obtain ⟨j, h, a, ha⟩ := exists_affine_free_etaleModule_eventual_hom_lift
    D c hc Λ i m WV hWV B₀ (eA.hom ≫ f ≫ eB.inv)
  let t := Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)
  let E := Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
    (D.map (homOfLE h).op) (c.π.app (op i)) (c.w (homOfLE h).op).symm
  have : ∀ k, IsAffine (WU k).left := hWU
  have : ∀ k, IsAffine (WV k).left := hWV
  have hQ (W : (D.obj (op i)).Etale) [IsAffine W.left] :
      IsConstructibleEtaleModuleSheaf (Q W) :=
    isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
      (X := D.obj (op i)) (U := W.left) W.hom (ModuleCat.of Λ Λ)
  have hQA (k : Fin m) : IsConstructibleSheaf (Q (WV k)) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hQ (WV k))
  have hQB (k : Fin n) : IsConstructibleSheaf (Q (WU k)) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hQ (WU k))
  have : HasFiniteBiproducts
      (Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    Abelian.hasFiniteBiproducts
  have : IsConstructibleSheaf (⨁ fun k : Fin m ↦ Q (WV k)) :=
    IsConstructibleSheaf.biproduct _
  have : IsConstructibleSheaf (⨁ fun k : Fin n ↦ Q (WU k)) :=
    IsConstructibleSheaf.biproduct _
  have hA₀ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) A₀ :=
    IsConstructibleSheaf.of_iso (biproduct.isoCoproduct _)
      (F := ⨁ fun k : Fin m ↦ Q (WV k))
  have hB₀ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) B₀ :=
    IsConstructibleSheaf.of_iso (biproduct.isoCoproduct _)
      (F := ⨁ fun k : Fin n ↦ Q (WU k))
  have hAj : IsConstructibleEtaleModuleSheaf (t.obj A₀) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.upperStar (D.map (homOfLE h).op) A₀)
  have hBj : IsConstructibleEtaleModuleSheaf (t.obj B₀) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.upperStar (D.map (homOfLE h).op) B₀)
  refine ⟨j, t.obj A₀, t.obj B₀, a, hAj, hBj,
    (E.app A₀).symm ≪≫ eA, (E.app B₀).symm ≪≫ eB, ?_⟩
  change _ ≫ (E.inv.app B₀ ≫ eB.hom) = (E.inv.app A₀ ≫ eA.hom) ≫ f
  rw [← Category.assoc, ha]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl


end AlgebraicGeometry.Scheme
