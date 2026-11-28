/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison

/-! # Roos comparisons of functors preserving countable products

An additive functor between abelian categories that preserves countable products carries the
strict Roos cocone of a tower to the strict Roos cocone of the image tower
(`RoosComparison.ofPreservesProducts`).

## Implementation details

The comparison is the additive Roos map `scalarRoosMap`, whose two cocone coordinates are the
product comparison of the functor. It is invertible degreewise because the functor preserves the
binary biproduct decomposition of the cocone and the countable products.

## References

* [Stacks, Tag 0941](https://stacks.math.columbia.edu/tag/0941)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex
universe a b c d
namespace WeilConjectures.OpenProjectionRoos

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]

/-- The biproduct coordinates of a degree of a mapping cocone. -/
private def coconeCoordinates {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i : ℤ) :
    (mappingCocone φ).X i ≅ K.X i ⊞ L.X (i - 1) where
  hom := biprod.lift ((mappingCocone.fst φ).f i)
    ((mappingCocone.snd φ).v i (i - 1) (by omega))
  inv := biprod.desc ((mappingCocone.inl φ).v i i (by omega))
    ((mappingCocone.inr φ).1.v (i - 1) i (by omega))
  hom_inv_id := by simpa using mappingCocone.id_X φ i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- The additive Roos map is invertible when the functor preserves the products of the tower. -/
theorem scalarRoosMap_isIso (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    [hpc : IsIso (piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)))] :
    IsIso (scalarRoosMap F C) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc : G.obj (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ G.obj (C.obj (op n)) :=
    piComparison G (fun n : ℕ ↦ C.obj (op n))
  obtain ⟨hf, hs⟩ := podReindexingRoosCoordinates F C
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hpcf (i : ℤ) : IsIso (pc.f i) := inferInstance
  have hi (i : ℤ) : IsIso ((scalarRoosMap F C).f i) := by
    let eY := coconeCoordinates (scalarRoosBoundary C) i
    let eX := coconeCoordinates (scalarRoosBoundary (C ⋙ G)) i
    have he : F.map eY.hom ≫
        (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom =
        biprod.lift (F.map ((mappingCocone.fst (scalarRoosBoundary C)).f i))
          (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
            i (i - 1) (by omega))) :=
      biprod.map_lift_mapBiprod F _ _ _ _
    have hm : (scalarRoosMap F C).f i ≫ eX.hom =
        F.map eY.hom ≫ (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
            ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom ≫
          biprod.map (pc.f i) (pc.f (i - 1)) := by
      rw [← Category.assoc, he]
      apply biprod.hom_ext
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        exact congrArg (fun f ↦ f.f i) hf
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        exact hs i
    have : IsIso ((scalarRoosMap F C).f i ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (asIso (pc.f i)) (asIso (pc.f (i - 1)))).hom)
      infer_instance
    exact IsIso.of_isIso_comp_right _ eX.hom
  exact HomologicalComplex.Hom.isIso_of_components _

section Products

variable (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]

omit [HasCountableProducts B] in
/-- Termwise application of a functor preserving countable products preserves them. -/
theorem mapHomologicalComplex_preservesCountableProducts :
    PreservesLimitsOfShape (Discrete ℕ) (F.mapHomologicalComplex (.up ℤ)) :=
  HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun n ↦ by
    change PreservesLimitsOfShape (Discrete ℕ) (HomologicalComplex.eval _ (.up ℤ) n ⋙ F)
    infer_instance)

/-- The product comparison of the termwise functor on a tower is invertible. -/
instance isIso_piComparison_mapHomologicalComplex (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    IsIso (piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ T.obj (op n))) := by
  have := mapHomologicalComplex_preservesCountableProducts F
  infer_instance

omit [PreservesLimitsOfShape (Discrete ℕ) F] in
/-- The shifted coordinate of the additive Roos map, for an arbitrary target degree. -/
theorem scalarRoosMap_shifted (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i k : ℤ) (h : i + -1 = k) :
    (scalarRoosMap F T).f i ≫
        (mappingCocone.snd (scalarRoosBoundary (T ⋙ F.mapHomologicalComplex (.up ℤ)))).v
          i k h =
      F.map ((mappingCocone.snd (scalarRoosBoundary T)).v i k h) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ T.obj (op n))).f k := by
  obtain rfl : k = i - 1 := by omega
  exact (podReindexingRoosCoordinates F T).2 i

/-- The Roos comparison of an additive functor preserving countable products: the product
comparison and the additive Roos map, with their coordinate and augmentation laws. -/
def RoosComparison.ofPreservesProducts : RoosComparison F where
  products T := asIso (piComparison (F.mapHomologicalComplex (.up ℤ))
    (fun n : ℕ ↦ T.obj (op n)))
  projections T n := piComparison_comp_π _ _ n
  iso := NatIso.ofComponents
    (fun T ↦ haveI := scalarRoosMap_isIso F T; asIso (scalarRoosMap F T))
    (fun f ↦ podReindexingRoosNaturality F f)
  first T := (podReindexingRoosCoordinates F T).1
  shifted T i k h := scalarRoosMap_shifted F T i k h
  augmentations T P a := by
    let G := F.mapHomologicalComplex (.up ℤ)
    have hφ : Pi.lift (fun n : ℕ ↦ a.app (op n)) ≫ boundary T = 0 := by
      apply Pi.hom_ext
      intro n
      have h := (towerTransitionEndomorphism_eq_iff (integralOperationsTowerStep T)
        (boundary T)).mp rfl n
      rw [Category.assoc, h, zero_comp, Preadditive.comp_sub, Pi.lift_comp_π,
        ← Category.assoc, Pi.lift_comp_π]
      dsimp only [integralOperationsTowerStep]
      have hn := a.naturality (homOfLE (Nat.le_succ n)).op
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hn
      exact sub_eq_zero.mpr hn
    let b : P ⟶ integralOperationsRoos T :=
      mappingCocone.lift (boundary T) (Pi.lift (fun n : ℕ ↦ a.app (op n))) 0
        (by rw [hφ]; simp)
    refine ⟨b, G.map b ≫ scalarRoosMap F T, mappingCocone.lift_fst _ _ _ _, ?_, ?_, ?_, rfl⟩
    · intro i k h
      simp [b]
    · have hf := (podReindexingRoosCoordinates F T).1
      rw [Category.assoc]
      erw [hf]
      rw [← Category.assoc, ← G.map_comp]
      apply Pi.hom_ext
      intro n
      erw [mappingCocone.lift_fst]
      rw [Category.assoc]
      erw [piComparison_comp_π]
      rw [← G.map_comp, Pi.lift_comp_π]
      exact (Pi.lift_comp_π (f := fun n : ℕ ↦ ((onTowers F).obj T).obj (op n))
        (fun n ↦ G.map (a.app (op n))) n).symm
    · intro i k h
      rw [HomologicalComplex.comp_f, Category.assoc]
      erw [scalarRoosMap_shifted F T i k h]
      change F.map (b.f i) ≫ _ = 0
      rw [← Category.assoc, ← F.map_comp]
      simp [b]

end Products

end WeilConjectures.OpenProjectionRoos
