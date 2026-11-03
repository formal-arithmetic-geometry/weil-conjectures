/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CoinducedSequence.CoinducedSequenceProducts
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Functorial coinduced products and their additive Hom equivalences

Source: Stacks 0941 and 015F, the functorial coinduced resolution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v w z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CoinducedSequence

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {D : ℕ → Type w} [∀ n, Category.{z} (D n)] [∀ n, Preadditive (D n)]
  (E : ∀ n, A ⥤ D n) (R : ∀ n, D n ⥤ A) (a : ∀ n, E n ⊣ R n)
  (S : ∀ n, D n ⥤ D (n + 1)) (t : ∀ n, E (n + 1) ⟶ E n ⋙ S n)
  [∀ n, (E n).Additive] [∀ n, (R n).Additive] [∀ n, (S n).Additive]
  [HasCountableProducts A]

attribute [local implicit_reducible] product relations

/-- The sign convention whose components are source transition minus target transition.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
def defect (N : A) : product E R N ⟶ relations E R S N :=
  -difference E R a S t N

/-- The first coinduced product acts by the actual derived functors on each factor.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
def productFunctor : A ⥤
    A where
  obj := product E R
  map f := Limits.Pi.map (fun n ↦ (R n).map ((E n).map f))
  map_id _ := by
    apply Pi.hom_ext
    intro n
    simp [product]
  map_comp _ _ := by
    apply Pi.hom_ext
    intro n
    simp [Functor.map_comp, product]

/-- The second coinduced product acts by evaluation, restriction and coinduction.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
def relationsFunctor : A ⥤
    A where
  obj := relations E R S
  map f := Limits.Pi.map (fun n ↦ (R (n + 1)).map
    ((S n).map ((E n).map f)))
  map_id _ := by
    apply Pi.hom_ext
    intro n
    simp [relations]
  map_comp _ _ := by
    apply Pi.hom_ext
    intro n
    simp [Functor.map_comp, relations]

attribute [local implicit_reducible] productFunctor relationsFunctor

/-- Projection from the first product is natural.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
def productProjection (n : ℕ) : productFunctor E R ⟶ E n ⋙ R n where
  app N := Pi.π _ n
  naturality {M N} f := by
    dsimp only [productFunctor, Functor.comp_map]
    simpa only [product, relations] using
      (Pi.map_π (fun k ↦ (R k).map ((E k).map f)) n)

/-- Projection from the relation product is natural.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
def relationsProjection (n : ℕ) : relationsFunctor E R S ⟶ E n ⋙ S n ⋙ R (n + 1) where
  app N := Pi.π _ n
  naturality {M N} f := by
    dsimp only [relationsFunctor, Functor.comp_map]
    simpa only [relations] using
      (Pi.map_π (fun k ↦ (R (k + 1)).map ((S k).map ((E k).map f))) n)

/-- The product universal property and the specified derived adjunction, additively.
Source: Stacks 0941, 015F
(blueprint: def-sf-coinduced-sequence-functoriality). -/
def productHomEquiv (M N : A) :
    (M ⟶ product E R N) ≃+ (∀ n, (E n).obj M ⟶
      (E n).obj N) where
  toFun f n := ((a n).homAddEquiv _ _).symm (f ≫ Pi.π _ n)
  invFun f := Pi.lift (fun n ↦ (a n).homAddEquiv _ _ (f n))
  left_inv f := by
    apply Pi.hom_ext
    intro n
    simp
  right_inv f := by
    funext n
    simp
  map_add' f g := by
    funext n
    simp [Preadditive.add_comp]

/-- The analogous additive adjunction for the relation product.
Source: Stacks 0941, 015F
(blueprint: def-sf-coinduced-sequence-functoriality). -/
def relationsHomEquiv (M N : A) :
    (M ⟶ relations E R S N) ≃+ (∀ n, (E (n + 1)).obj M ⟶
      (S n).obj ((E n).obj N)) where
  toFun f n := ((a (n + 1)).homAddEquiv _ _).symm (f ≫ Pi.π _ n)
  invFun f := Pi.lift (fun n ↦ (a (n + 1)).homAddEquiv _ _ (f n))
  left_inv f := by
    apply Pi.hom_ext
    intro n
    simp
  right_inv f := by
    funext n
    simp
  map_add' f g := by
    funext n
    simp [Preadditive.add_comp]

/-- The augmentation is killed by the chosen sign of the adjacent difference.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
theorem augmentation_defect (N : A) :
    augmentation E R a N ≫ defect E R a S t N = 0 := by
  simp only [defect, Preadditive.comp_neg,
    CoinducedSequence.augmentation_difference, neg_zero]

/-- Projecting the augmentation recovers evaluation on maps.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
theorem productHomEquiv_augmentation {M N : A}
    (g : M ⟶ N) : productHomEquiv E R a M N (g ≫ augmentation E R a N) =
      fun n ↦ (E n).map g := by
  funext n
  exact CoinducedSequence.components_augmentation E
    R a g n

/-- Under the actual adjunction the difference is the adjacent compatibility defect.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
theorem relationsHomEquiv_defect {M N : A}
    (b : M ⟶ product E R N) (n : ℕ) :
    relationsHomEquiv E R a S M N (b ≫ defect E R a S t N) n =
      (t n).app M ≫
        (S n).map (productHomEquiv E R a M N b n) -
      (show (E (n + 1)).obj M ⟶ (S n).obj ((E n).obj N) from
        productHomEquiv E R a M N b (n + 1) ≫ (t n).app N) := by
  change ((a (n + 1)).homAddEquiv _ _).symm
    ((b ≫ (-CoinducedSequence.difference _ _ _ _ _ N)) ≫ Pi.π _ n) = _
  rw [Preadditive.comp_neg, Preadditive.neg_comp, map_neg]
  have h := CoinducedSequence.difference_component E
    R a S
    t b n
  change ((a (n + 1)).homAddEquiv _ _).symm
    (b ≫ CoinducedSequence.difference _ _ _ _ _ N ≫ Pi.π _ n) = _ at h
  rw [Category.assoc, h, neg_sub]
  rfl

/-- The vertex adjunction is natural in both variables.
Source: Stacks 0941, 015F
(blueprint: def-sf-coinduced-sequence-functoriality). -/
theorem productHomEquiv_natural {M M' N N' : A}
    (f : M' ⟶ M) (g : N ⟶ N') (b : M ⟶ product E R N) (n : ℕ) :
    productHomEquiv E R a M' N' (f ≫ b ≫ (productFunctor E R).map g) n =
      (E n).map f ≫ productHomEquiv E R a M N b n ≫
        (E n).map g := by
  simp only [productHomEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Adjunction.homAddEquiv_symm_apply, productFunctor, Category.assoc, Pi.map_π]
  rw [← Category.assoc b,
    (a n).homEquiv_naturality_left_symm,
    (a n).homEquiv_naturality_right_symm]

/-- The edge adjunction is natural in both variables.
Source: Stacks 0941, 015F
(blueprint: def-sf-coinduced-sequence-functoriality). -/
theorem relationsHomEquiv_natural {M M' N N' : A}
    (f : M' ⟶ M) (g : N ⟶ N') (b : M ⟶ relations E R S N) (n : ℕ) :
    relationsHomEquiv E R a S M' N' (f ≫ b ≫ (relationsFunctor E R S).map g) n =
      (E (n + 1)).map f ≫ relationsHomEquiv E R a S M N b n ≫
        (S n).map ((E n).map g) := by
  simp only [relationsHomEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Adjunction.homAddEquiv_symm_apply, relationsFunctor, Category.assoc, Pi.map_π]
  rw [← Category.assoc b,
    (a (n + 1)).homEquiv_naturality_left_symm,
    (a (n + 1)).homEquiv_naturality_right_symm]

/-- The augmentation is a natural transformation.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
def augmentationNat : 𝟭 _ ⟶ productFunctor E R where
  app := augmentation E R a
  naturality {M N} f := by
    apply Pi.hom_ext
    intro n
    simp only [Functor.id_map, augmentation, productFunctor,
      Category.assoc, Pi.lift_π, Pi.map_π]
    rw [← Category.assoc, Pi.lift_π]
    exact (a n).unit.naturality f

/-- The compatibility defect is a natural transformation.
Source: Stacks 0941 (blueprint: def-sf-coinduced-sequence-functoriality). -/
def differenceNat : productFunctor E R ⟶ relationsFunctor E R S where
  app := defect E R a S t
  naturality {M N} g := by
    apply (relationsHomEquiv E R a S (product E R M) N).injective
    funext n
    have h := relationsHomEquiv_natural E R a S (𝟙 (product E R M)) g (defect E R a S t M) n
    simp only [Category.id_comp, Functor.map_id] at h
    rw [h, relationsHomEquiv_defect]
    have hp (k : ℕ) := productHomEquiv_natural E R a
      (𝟙 (product E R M)) g (𝟙 (product E R M)) k
    simp only [Functor.map_id, Category.id_comp] at hp
    rw [hp n, hp (n + 1)]
    have hd := relationsHomEquiv_defect E R a S t (𝟙 (product E R M)) n
    simp only [Category.id_comp] at hd
    rw [hd]
    simp only [Preadditive.sub_comp, Functor.map_comp, Category.assoc]
    have ht := (t n).naturality g
    change (E (n + 1)).map g ≫
      (t n).app N =
      (t n).app M ≫
        (S n).map ((E n).map g) at ht
    simp only [ht]

end CategoryTheory.CoinducedSequence
