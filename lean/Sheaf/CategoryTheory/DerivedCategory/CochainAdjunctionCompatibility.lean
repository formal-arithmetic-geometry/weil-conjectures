/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Derived adjunction normalization on cochain representatives

Source: Stacks 0FND, compatibility of a derived adjunction with its original adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a av b bv da db
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- A normalized Hom formula on homotopy representatives gives the corresponding formula
on complexes, with the prescribed cochain comparison. Source: Stacks 0FND
(blueprint: lem-pur-cochain-adjunction-compatibility).
Proof: apply the homotopy formula to the images of the two complexes and the chain map.
The homotopy adjunction unit on a complex is the quotient of the termwise adjunction unit,
so the strict transposes agree after quotienting. The comparison between Qh and Q has
identity components. The exact right functor's two localization comparisons therefore
also have the same components. Substitution gives the cochain formula. -/
theorem adjunction_cochain_transpose
    (a : E ⊣ R) (T : DerivedCategory A ⥤ DerivedCategory B)
    (εc : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : ∀ P : CochainComplex A ℤ,
      ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) = εc.app P)
    (d : T ⊣ R.mapDerivedCategory)
    (hd : ∀ (M : HomotopyCategory A (.up ℤ)) (N : HomotopyCategory B (.up ℤ))
      (f : (E.mapHomotopyCategory (.up ℤ)).obj M ⟶ N),
      d.homEquiv _ _ (ε.app M ≫ DerivedCategory.Qh.map f) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv M N f) ≫
          R.mapDerivedCategoryFactorsh.inv.app N) :
    ∀ (P : CochainComplex A ℤ) (K : CochainComplex B ℤ)
      (f : (E.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      d.homEquiv _ _ (εc.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          R.mapDerivedCategoryFactors.inv.app K := by
  intro P K f
  let qA := HomotopyCategory.quotient A (.up ℤ)
  let qB := HomotopyCategory.quotient B (.up ℤ)
  have ht := hd (qA.obj P) (qB.obj K) (qB.map f)
  have haeq : (a.mapHomotopyCategory (.up ℤ)).homEquiv (qA.obj P) (qB.obj K)
    (qB.map f) = qA.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P K f) := by
    rw [Adjunction.homEquiv_unit, Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.homEquiv_unit, qA.map_comp]
    rfl
  rw [haeq, hε P] at ht
  let R₀ := R
  have hf : R₀.mapDerivedCategoryFactorsh.inv.app (qB.obj K) =
    R₀.mapDerivedCategoryFactors.inv.app K := by
    apply (cancel_epi (R₀.mapDerivedCategoryFactorsh.hom.app (qB.obj K))).1
    rw [Iso.hom_inv_id_app, R₀.mapDerivedCategoryFactorsh_hom_app]
    simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    simp only [Functor.comp_obj, Quotient.lift.isLift_hom, Functor.map_id,
      Category.comp_id, Category.assoc]
    change 𝟙 _ = R₀.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj K)) ≫
    R₀.mapDerivedCategoryFactors.hom.app K ≫
      𝟙 (DerivedCategory.Q.obj ((R₀.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      R₀.mapDerivedCategoryFactors.inv.app K
    erw [R₀.mapDerivedCategory.map_id, Category.id_comp, Category.id_comp,
    Iso.hom_inv_id_app]
    rfl
  rw [hf] at ht
  exact ht
end CategoryTheory
