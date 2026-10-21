/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! The derived-limit triangle for a Roos complex given by signed coordinates.
Source: Stacks Project, Derived Categories, Tags 07KC and 08TC. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.HomComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]

private def signedCoconeXIso {V : CochainComplex C ℤ} (s : V ⟶ V) (i : ℤ) :
    (mappingCocone s).X i ≅ V.X i ⊞ V.X (i - 1) where
  hom := biprod.lift ((mappingCocone.fst s).f i)
    (-(mappingCocone.snd s).v i (i - 1) (by omega))
  inv := biprod.desc ((mappingCocone.inl s).v i i (by omega))
    (-(mappingCocone.inr s).1.v (i - 1) i (by omega))
  hom_inv_id := by
    simpa using mappingCocone.id_X s i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

private def coordinatesSecond (V L : CochainComplex C ℤ)
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1)) : Cochain L V (-1) :=
  Cochain.mk fun i j hij ↦
    -(e i).hom ≫ biprod.snd ≫ eqToHom (congrArg V.X (by omega : i - 1 = j))

private theorem coordinatesSecond_delta
    (V L : CochainComplex C ℤ) (s : V ⟶ V)
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ s.f i ≫
          eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1)))
    (p : L ⟶ V) (hp : ∀ i, p.f i = (e i).hom ≫ biprod.fst) :
    δ (-1) 0 (coordinatesSecond V L e) + Cochain.ofHom (p ≫ s) = 0 := by
  ext i
  rw [Cochain.add_v, δ_v (-1) 0 (by omega) _ i i (by omega)
    (i - 1) (i + 1) rfl rfl]
  simp only [coordinatesSecond, Cochain.mk_v, Int.negOnePow_zero, one_smul,
    eqToHom_refl, Category.comp_id, Cochain.ofHom_v, HomologicalComplex.comp_f,
    Cochain.zero_v, hp, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
  rw [← Category.assoc (L.d i (i + 1)), hd]
  simp [Category.assoc, Preadditive.comp_sub]
  abel

private def coordinatesCoconeIso
    (V L : CochainComplex C ℤ) (s : V ⟶ V)
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ s.f i ≫
          eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1)))
    (p : L ⟶ V) (hp : ∀ i, p.f i = (e i).hom ≫ biprod.fst) :
    L ≅ mappingCocone s := by
  let f := mappingCocone.lift s p (coordinatesSecond V L e)
    (coordinatesSecond_delta V L s e hd p hp)
  have hf (i : ℤ) : f.f i ≫ (signedCoconeXIso s i).hom = (e i).hom := by
    apply biprod.hom_ext
    · simp [f, signedCoconeXIso, hp]
    · simp [f, signedCoconeXIso, coordinatesSecond, Category.assoc]
  have (i : ℤ) : IsIso (f.f i) := by
    have : IsIso (f.f i ≫ (signedCoconeXIso s i).hom) := by
      rw [hf]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (signedCoconeXIso s i).hom
  have := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

private theorem coordinatesCoconeIso_fst
    (V L : CochainComplex C ℤ) (s : V ⟶ V)
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ s.f i ≫
          eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1)))
    (p : L ⟶ V) (hp : ∀ i, p.f i = (e i).hom ≫ biprod.fst) :
    (coordinatesCoconeIso V L s e hd p hp).hom ≫ mappingCocone.fst s = p := by
  exact mappingCocone.lift_fst s p (coordinatesSecond V L e)
    (coordinatesSecond_delta V L s e hd p hp)

/-- A signed Roos coordinate model gives the derived-limit triangle with its actual
product projections.

Source: Stacks Project, Derived Categories, Tags 07KC and 08TC
(blueprint: lem-sbc-roos-coordinates-derived-limit).

Proof: The negative second coordinate and the first projection define a map to
Mathlib's mapping cocone of one minus the shift. The displayed differential says
exactly that this map is a chain map; its coordinate matrix is invertible. Localize
its mapping-cocone triangle. Exact countable products identify the localized product
with the product of the localized complexes. Their projections identify the
localized endomorphism with one minus the localized shift. Transport the triangle
across these isomorphisms. The first-arrow equation follows by composing with each
product projection. This also applies to zero towers and arbitrary transitions. -/
theorem derivedLimitTriangle_of_roos_coordinates
    [HasCountableProducts C] [CountableAB4Star C] [HasDerivedCategory.{w} C]
    (K : ℕ → CochainComplex C ℤ) (f : ∀ n, K (n + 1) ⟶ K n)
    (L : CochainComplex C ℤ)
    (e : ∀ i : ℤ, L.X i ≅ (∏ᶜ K : CochainComplex C ℤ).X i ⊞
      (∏ᶜ K : CochainComplex C ℤ).X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift
        (biprod.fst ≫ (∏ᶜ K : CochainComplex C ℤ).d i (i + 1))
        (biprod.fst ≫ (towerTransitionEndomorphism f).f i ≫
          eqToHom (congrArg (∏ᶜ K : CochainComplex C ℤ).X
            (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ (∏ᶜ K : CochainComplex C ℤ).d (i - 1) ((i + 1) - 1)))
    (p : L ⟶ ∏ᶜ K) (hp : ∀ i, p.f i = (e i).hom ≫ biprod.fst) :
    ∃ _hP : HasProduct (fun n ↦ DerivedCategory.Q.{w}.obj (K n)),
      ∃ (q : DerivedCategory.Q.{w}.obj L ⟶ ∏ᶜ (fun n ↦ DerivedCategory.Q.{w}.obj (K n)))
        (δ : (∏ᶜ (fun n ↦ DerivedCategory.Q.{w}.obj (K n))) ⟶
          (DerivedCategory.Q.{w}.obj L)⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (fun n ↦ DerivedCategory.Q.{w}.map (f n))
          (DerivedCategory.Q.{w}.obj L) q δ ∧
        ∀ n, q ≫ Pi.π _ n = DerivedCategory.Q.{w}.map (p ≫ Pi.π K n) := by
  let B : CochainComplex C ℤ := ∏ᶜ K
  let s := towerTransitionEndomorphism f
  let t := coordinatesCoconeIso B L s e hd p hp
  let Q := DerivedCategory.Q.{w} (C := C)
  have hlim := (derivedCategory_termwiseProduct_isLimit C ℕ K).some
  let hfan : IsLimit (Fan.mk (Q.obj B) (fun n ↦ Q.map (Pi.π K n))) :=
    isLimitMapConeFanMkEquiv Q K _ hlim
  let hP : HasProduct (fun n ↦ Q.obj (K n)) := ⟨⟨_, hfan⟩⟩
  let := hP
  let c : Q.obj B ≅ ∏ᶜ (fun n ↦ Q.obj (K n)) :=
    hfan.conePointUniqueUpToIso (productIsProduct _)
  have hc (n : ℕ) : c.hom ≫ Pi.π _ n = Q.map (Pi.π K n) :=
    IsLimit.conePointUniqueUpToIso_hom_comp hfan (productIsProduct _) ⟨n⟩
  have hs : Q.map s ≫ c.hom = c.hom ≫
      towerTransitionEndomorphism (K := fun n ↦ Q.obj (K n))
        (fun n ↦ Q.map (f n)) := by
    apply Pi.hom_ext
    intro n
    have hsπ := (towerTransitionEndomorphism_eq_iff f s).1 rfl n
    have hDπ := (towerTransitionEndomorphism_eq_iff
      (K := fun n ↦ Q.obj (K n)) (fun n ↦ Q.map (f n))
      (towerTransitionEndomorphism (K := fun n ↦ Q.obj (K n))
        (fun n ↦ Q.map (f n)))).1 rfl n
    calc
      (Q.map s ≫ c.hom) ≫ Pi.π _ n = Q.map (s ≫ Pi.π K n) := by
        rw [Category.assoc, hc, Q.map_comp]
      _ = Q.map (Pi.π K n) - Q.map (Pi.π K (n + 1)) ≫ Q.map (f n) := by
        rw [hsπ, Q.map_sub, Q.map_comp]
      _ = (c.hom ≫ towerTransitionEndomorphism (K := fun n ↦ Q.obj (K n))
        (fun n ↦ Q.map (f n))) ≫
          Pi.π _ n := by
        rw [Category.assoc, hDπ, Preadditive.comp_sub, ← Category.assoc, hc, hc]
  let T := Q.mapTriangle.obj (mappingCocone.triangle s)
  let q := Q.map p ≫ c.hom
  let δ := c.inv ≫ T.mor₃ ≫ (CategoryTheory.shiftFunctor (DerivedCategory.{w} C) (1 : ℤ)).map
    (Q.mapIso t).inv
  refine ⟨hP, q, δ, ?_, ?_⟩
  · apply isomorphic_distinguished T (DerivedCategory.mappingCocone_triangle_distinguished s)
    refine Triangle.isoMk _ _ (Q.mapIso t) c.symm c.symm ?_ ?_ ?_
    · change (Q.map p ≫ c.hom) ≫ c.inv =
        Q.map t.hom ≫ Q.map (mappingCocone.fst s)
      rw [Category.assoc, c.hom_inv_id, Category.comp_id, ← Q.map_comp]
      exact congrArg Q.map (coordinatesCoconeIso_fst B L s e hd p hp).symm
    · change towerTransitionEndomorphism (K := fun n ↦ Q.obj (K n))
        (fun n ↦ Q.map (f n)) ≫ c.inv = c.inv ≫ Q.map s
      apply (cancel_epi c.hom).1
      simpa [Category.assoc] using congrArg (fun a ↦ a ≫ c.inv) hs.symm
    · change (c.inv ≫ T.mor₃ ≫
          (CategoryTheory.shiftFunctor (DerivedCategory.{w} C) (1 : ℤ)).map
            (Q.mapIso t).inv) ≫
        (CategoryTheory.shiftFunctor (DerivedCategory.{w} C) (1 : ℤ)).map
          (Q.mapIso t).hom = c.inv ≫ T.mor₃
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
      change c.inv ≫ T.mor₃ ≫
        (CategoryTheory.shiftFunctor (DerivedCategory.{w} C) (1 : ℤ)).map
          (𝟙 (Q.obj (mappingCocone s))) = c.inv ≫ T.mor₃
      exact (congrArg (fun a ↦ c.inv ≫ T.mor₃ ≫ a)
        ((CategoryTheory.shiftFunctor (DerivedCategory.{w} C) (1 : ℤ)).map_id
          (Q.obj (mappingCocone s)))).trans
          (congrArg (fun a ↦ c.inv ≫ a) (Category.comp_id T.mor₃))
  · intro n
    change (Q.map p ≫ c.hom) ≫ Pi.π (fun n ↦ Q.obj (K n)) n =
      Q.map (p ≫ Pi.π K n)
    rw [Category.assoc, hc, Q.map_comp]

end CochainComplex
