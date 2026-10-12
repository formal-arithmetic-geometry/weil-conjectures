/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Functors and adjunctions on commutative ring objects

A braided monoidal functor `F : C ⥤ D` between cartesian monoidal categories (e.g. a
finite-product-preserving functor, with the structure `Functor.Braided.ofChosenFiniteProducts`)
takes commutative ring objects to commutative ring objects (`Functor.mapCommRingObj`), and an
adjunction `F ⊣ G` of such functors lifts to an adjunction
`F.mapCommRingObj ⊣ G.mapCommRingObj` (`Adjunction.mapCommRingObj`) whose unit and counit
have the unit and counit of `F ⊣ G` as underlying morphisms.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory Functor.LaxMonoidal Functor.Monoidal
open scoped MonObj AddMonObj Functor.Obj

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [CartesianMonoidalCategory E]
  [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]

namespace Functor

section

variable (F : C ⥤ D) [F.Braided]

/-- The image of a commutative additive monoid object under a braided functor is
commutative. -/
instance isCommAddMonObj_obj {M : C} [AddMonObj M] [IsCommAddMonObj M] :
    IsCommAddMonObj (F.obj M) where
  add_comm := by
    dsimp
    rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommAddMonObj.add_comm]

lemma obj_mul_add (R : C) [RingObj R] :
    F.obj R ◁ σ ≫ μ = lift ((F.obj R ◁ fst _ _) ≫ μ) ((F.obj R ◁ snd _ _) ≫ μ) ≫ σ := by
  calc F.obj R ◁ σ ≫ μ
      = (F.obj R ◁ LaxMonoidal.μ F R R) ≫ LaxMonoidal.μ F R (R ⊗ R) ≫
          F.map (R ◁ σ ≫ μ) := by
        simp [μ_natural_right_assoc]
    _ = (F.obj R ◁ LaxMonoidal.μ F R R) ≫ LaxMonoidal.μ F R (R ⊗ R) ≫
          F.map (lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ) := by
        rw [RingObj.mul_add R]
    _ = _ := by
        rw [Functor.map_comp, ← lift_μ]
        simp [μ_natural_right_assoc]

lemma obj_add_mul (R : C) [RingObj R] :
    σ ▷ F.obj R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ := by
  calc σ ▷ F.obj R ≫ μ
      = (LaxMonoidal.μ F R R ▷ F.obj R) ≫ LaxMonoidal.μ F (R ⊗ R) R ≫
          F.map (σ ▷ R ≫ μ) := by
        simp [μ_natural_left_assoc]
    _ = (LaxMonoidal.μ F R R ▷ F.obj R) ≫ LaxMonoidal.μ F (R ⊗ R) R ≫
          F.map (lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ) := by
        rw [RingObj.add_mul R]
    _ = _ := by
        rw [Functor.map_comp, ← lift_μ]
        simp [μ_natural_left_assoc]

/-- The image of a ring object under a braided functor of cartesian monoidal categories is a
ring object. -/
abbrev ringObjObj (R : C) [RingObj R] : RingObj (F.obj R) where
  mul_add := F.obj_mul_add R
  add_mul := F.obj_add_mul R

/-- The image of a commutative ring object under a braided functor of cartesian monoidal
categories is a commutative ring object. -/
abbrev commRingObjObj (R : C) [CommRingObj R] : CommRingObj (F.obj R) where
  __ := F.ringObjObj R

attribute [local instance] ringObjObj commRingObjObj

instance map_isRingHom {R₁ R₂ : C} [RingObj R₁] [RingObj R₂] (f : R₁ ⟶ R₂) [IsRingHom f] :
    IsRingHom (F.map f) where

/-- A braided functor between cartesian monoidal categories takes commutative ring objects to
commutative ring objects. -/
@[simps]
def mapCommRingObj : CommRingObjCat C ⥤ CommRingObjCat D where
  obj R := .mk (F.obj R.X)
  map f := { hom := F.map f.hom }

end

end Functor

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Braided] [G.Braided]

attribute [local instance] Functor.ringObjObj Functor.commRingObjObj


instance unit_app_isRingHom (X : C) [RingObj X] : IsRingHom (adj.unit.app X) where
  one_hom := by
    have h := NatTrans.IsMonoidal.unit (τ := adj.unit)
    simp only [Functor.LaxMonoidal.id_ε, Category.id_comp, Functor.LaxMonoidal.comp_ε] at h
    simp [← adj.unit_naturality, reassoc_of% h]
  mul_hom := by
    have h := NatTrans.IsMonoidal.tensor (τ := adj.unit) X X
    simp only [Functor.LaxMonoidal.id_μ, Category.id_comp, Functor.LaxMonoidal.comp_μ] at h
    simp [← adj.unit_naturality, reassoc_of% h]
  zero_hom := by
    have h := NatTrans.IsMonoidal.unit (τ := adj.unit)
    simp only [Functor.LaxMonoidal.id_ε, Category.id_comp, Functor.LaxMonoidal.comp_ε] at h
    simp [← adj.unit_naturality, reassoc_of% h]
  add_hom := by
    have h := NatTrans.IsMonoidal.tensor (τ := adj.unit) X X
    simp only [Functor.LaxMonoidal.id_μ, Category.id_comp, Functor.LaxMonoidal.comp_μ] at h
    simp [← adj.unit_naturality, reassoc_of% h]

end Adjunction

end CategoryTheory
