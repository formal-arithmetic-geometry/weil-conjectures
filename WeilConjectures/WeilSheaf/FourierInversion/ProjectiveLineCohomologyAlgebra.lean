/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Cohomology of the two projective-line summands -/

@[expose] public section
set_option autoImplicit false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- A degree-zero sheaf plus a degree-two flat twist has the expected degree-zero
cohomology and no other non-top positive cohomology.
Source: current blueprint, `thm-amb-p1-decomposition.proof.md`, final tensor calculation.
(blueprint: lem-pur-projective-line-cohomology-algebra).

Proof: a flat sheaf in degree zero has Tor amplitude [0,0], so its derived tensor with
M[0] lies in the heart. Shifting by -2 puts that summand in degree two. Cohomology is
additive: degree zero is M plus zero, and in a positive degree other than two both
summands vanish. These arguments include the zero object and all integer degrees.
-/
theorem cohomology_single_biprod_flat_shift
    (P M : C) (hP : ObjectProperty.flat P) (K : DerivedCategory C)
    (e : K ≅ (singleFunctor C 0).obj M ⊞
      ((singleFunctor C 0).obj P ⊗ (singleFunctor C 0).obj M)⟦(-2 : ℤ)⟧) :
    Nonempty ((homologyFunctor C 0).obj K ≅ M) ∧
      ∀ i : ℤ, 0 < i → i ≠ 2 → IsZero ((homologyFunctor C i).obj K) := by
  let N := (singleFunctor C 0).obj M
  let T := (singleFunctor C 0).obj P ⊗ N
  have hT := torAmplitudeIn_singleFunctor_obj_of_flat hP M
  have : T.IsGE 0 := hT.1
  have : T.IsLE 0 := hT.2
  have : (T⟦(-2 : ℤ)⟧).IsGE 2 := TStructure.t.isGE_shift T 0 (-2) 2 (by norm_num)
  have : (T⟦(-2 : ℤ)⟧).IsLE 2 := TStructure.t.isLE_shift T 0 (-2) 2 (by norm_num)
  have hvan (i : ℤ) (hi : i ≠ 2) :
      IsZero ((homologyFunctor C i).obj (T⟦(-2 : ℤ)⟧)) := by
    rcases hi.lt_or_gt with h | h
    · exact (isGE_iff _ 2).mp inferInstance i h
    · exact (isLE_iff _ 2).mp inferInstance i h
  refine ⟨⟨(homologyFunctor C 0).mapIso e ≪≫
    (homologyFunctor C 0).mapBiprod N (T⟦(-2 : ℤ)⟧) ≪≫
    (isoBiprodZero (hvan 0 (by norm_num))).symm ≪≫
    (singleFunctorCompHomologyFunctorIso C 0).app M⟩, ?_⟩
  intro i hi hi2
  have hN : IsZero ((homologyFunctor C i).obj N) :=
    (isLE_iff N 0).mp inferInstance i hi
  exact ((biprod_isZero_iff _ _).mpr ⟨hN, hvan i hi2⟩).of_iso
    ((homologyFunctor C i).mapIso e ≪≫
      (homologyFunctor C i).mapBiprod N (T⟦(-2 : ℤ)⟧))

end DerivedCategory
