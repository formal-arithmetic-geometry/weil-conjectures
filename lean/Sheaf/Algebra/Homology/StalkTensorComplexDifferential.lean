/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Differential compatibility of the stalk tensor comparison

Source: Stacks Project, Cohomology, Tag 06YB, tensor-stalk identification
(blueprint: lem-pc-stalk-tensor-complex-differential).
-/

@[expose] public section

universe u₁

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

variable (X : RingedSpace.{u₁}) (x : X)

set_option hygiene false in
local notation "O" => (sheafCompose (Opens.grothendieckTopology (X : Type u₁))
  (forget₂ CommRingCat.{u₁} RingCat.{u₁})).obj X.sheaf
set_option hygiene false in
local notation "S" => (RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)

noncomputable local instance stalkTensorDifferentialMonoidal :
    MonoidalCategory (SheafOfModules.{u₁} O) :=
  SheafOfModules.monoidalCategory X.sheaf

-- The simultaneous total tensor constructions require extra elaboration heartbeats.
set_option maxHeartbeats 1500000 in
-- Elaborating both total tensor coproducts exceeds the default heartbeat budget.
/-- Source: Stacks Project, Cohomology, Tag 06YB, tensor-stalk identification,
third step (blueprint: lem-pc-stalk-tensor-complex-differential).

Proof: conjugating by the degree isomorphism reduces equality to equality after each
stalked summand injection, since the target degree is a coproduct and the component
comparisons are isomorphisms. The total differential is the sum of its horizontal
and vertical parts. On a summand these are the maps induced by `F.d` and `K.d`,
followed by the next summand injection, with the total-complex signs. Naturality
of the tensor comparison with respect to `F.d` and the identity identifies the
horizontal part; naturality with respect to the identity and `K.d` identifies the
vertical part. The additive functor preserves sums and multiplication by the
integer signs. The formula for injections also applies to zero injections when
the degree condition fails, because the functor preserves zero maps. Thus both
parts agree on every summand, proving the claimed differential compatibility. -/
theorem stalk_tensor_degree_differential
    [(RingedSpace.moduleStalkFunctor X x).Additive]
    (φ : ∀ A B : SheafOfModules.{u₁} O,
      (RingedSpace.moduleStalkFunctor X x).obj (A ⊗ B) ≅
        (RingedSpace.moduleStalkFunctor X x).obj A ⊗
          (RingedSpace.moduleStalkFunctor X x).obj B)
    (hφ : ∀ (A B A' B' : SheafOfModules.{u₁} O) (f : A ⟶ A') (g : B ⟶ B'),
      (RingedSpace.moduleStalkFunctor X x).map (f ⊗ₘ g) ≫ (φ A' B').hom =
        (φ A B).hom ≫ ((RingedSpace.moduleStalkFunctor X x).map f ⊗ₘ
          (RingedSpace.moduleStalkFunctor X x).map g))
    (e : ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (n : ℤ),
      ((S).obj (mapBifunctor F K (curriedTensor _))).X n ≅
        (mapBifunctor ((S).obj F) ((S).obj K) (curriedTensor _)).X n)
    (he : ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ)
        (p q n : ℤ) (h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n),
      (RingedSpace.moduleStalkFunctor X x).map
          (HomologicalComplex.ιMapBifunctor F K (curriedTensor _) (.up ℤ) p q n h) ≫
        (e F K n).hom = (φ (F.X p) (K.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
          ((S).obj F) ((S).obj K) (curriedTensor _) (.up ℤ) p q n h)
    (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (n m : ℤ) :
    (e F K n).hom ≫ (mapBifunctor ((S).obj F) ((S).obj K) (curriedTensor _)).d n m =
      ((S).obj (mapBifunctor F K (curriedTensor _))).d n m ≫ (e F K m).hom := by
  let T := RingedSpace.moduleStalkFunctor X x
  have hφ₁ (A B A' : SheafOfModules.{u₁} O) (f : A ⟶ A') :
      T.map (f ▷ B) ≫ (φ A' B).hom =
        (φ A B).hom ≫ (T.map f ▷ T.obj B) := by
    have hh := hφ A B A' B f (𝟙 B)
    rw [(RingedSpace.moduleStalkFunctor X x).map_id, tensorHom_id, tensorHom_id] at hh
    exact hh
  have hφ₂ (A B B' : SheafOfModules.{u₁} O) (g : B ⟶ B') :
      T.map (A ◁ g) ≫ (φ A B').hom =
        (φ A B).hom ≫ (T.obj A ◁ T.map g) := by
    have hh := hφ A B A B' (𝟙 A) g
    rw [(RingedSpace.moduleStalkFunctor X x).map_id, id_tensorHom, id_tensorHom] at hh
    exact hh
  have he0 (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (p q n : ℤ) :
      T.map (HomologicalComplex.ιMapBifunctorOrZero F K (curriedTensor _) (.up ℤ)
        p q n) ≫ (e F K n).hom = (φ (F.X p) (K.X q)).hom ≫
          HomologicalComplex.ιMapBifunctorOrZero ((S).obj F) ((S).obj K)
            (curriedTensor _) (.up ℤ) p q n := by
    by_cases h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n
    · simpa only [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h] using
        he F K p q n h
    · simp only [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h,
        Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  have h_ext (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (n : ℤ)
      (M : ModuleCat.{u₁} (X.presheaf.stalk x))
      (a b : ((S).obj (mapBifunctor F K (curriedTensor _))).X n ⟶ M)
      (h : ∀ p q (hpq : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n),
        T.map (HomologicalComplex.ιMapBifunctor F K (curriedTensor _) (.up ℤ)
          p q n hpq) ≫ a = T.map (HomologicalComplex.ιMapBifunctor F K
            (curriedTensor _) (.up ℤ) p q n hpq) ≫ b) : a = b := by
    apply (cancel_epi (e F K n).inv).1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply (cancel_epi (φ (F.X p) (K.X q)).hom).1
    simp only [← Category.assoc]
    rw [← he F K p q n hpq]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h p q hpq
  apply h_ext F K n
  intro p q hpq
  rw [← Category.assoc, he, Category.assoc]
  change _ = T.map (HomologicalComplex.ιMapBifunctor F K (curriedTensor _)
    (.up ℤ) p q n hpq) ≫ T.map _ ≫ _
  rw [← Functor.map_comp_assoc]
  simp only [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    Functor.map_add, Preadditive.add_comp]
  rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ (show
      (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ p (show
      (ComplexShape.up ℤ).Rel q (q + 1) from rfl),
    HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ (show
      (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ p (show
      (ComplexShape.up ℤ).Rel q (q + 1) from rfl)]
  simp only [Units.smul_def, Functor.map_zsmul, Functor.map_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc, he0]
  apply congrArg₂ (· + ·)
  · apply congrArg (fun a ↦ ((ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q)) : ℤ) • a)
    change (φ (F.X p) (K.X q)).hom ≫ (T.map (F.d p (p + 1)) ▷ T.obj (K.X q)) ≫ _ =
      T.map (F.d p (p + 1) ▷ K.X q) ≫ (φ (F.X (p + 1)) (K.X q)).hom ≫ _
    rw [← Category.assoc, ← hφ₁, Category.assoc]
  · apply congrArg (fun a ↦ ((ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q)) : ℤ) • a)
    change (φ (F.X p) (K.X q)).hom ≫ (T.obj (F.X p) ◁ T.map (K.d q (q + 1))) ≫ _ =
      T.map (F.X p ◁ K.d q (q + 1)) ≫ (φ (F.X p) (K.X (q + 1))).hom ≫ _
    rw [← Category.assoc, ← hφ₂, Category.assoc]

end CochainComplex
