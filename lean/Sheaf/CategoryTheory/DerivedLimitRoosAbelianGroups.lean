/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Category.Grp.Abelian
public import Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism
import Sheaf.CategoryTheory.RoosPositiveDerivedLimit
import Sheaf.CategoryTheory.InjectiveTowerEmbedding
import Sheaf.CategoryTheory.InjectiveSplitTower

/-!
# Roos computation of derived limits of abelian groups

Source: Stacks Project, More on Algebra, Lemma 15.88.1, Tag 07KW
(blueprint: lem-pc-derived-limit-roos-abelian-groups).

## Main statements

- `roosTowerEnoughInjectives`: the tower category has enough injectives.
- `roosLimitAdditive`: inverse limit is additive.
- `derivedLimitRoosAbelianGroups`: inverse limit is left exact, naturally the kernel of
  the Roos map; its first right derived functor is naturally the cokernel and higher
  right derived functors vanish.

We use the Mathlib functor category for towers, reindexing positive integers by `n + 1`.
All groups lie in an arbitrary universe `u`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The displayed map `1 - s` of Stacks Project, Tag 07KW, Lemma 15.88.1:
the transition endomorphism `towerTransitionEndomorphism` (Tag 08TC) of the tower `A`,
whose `n`th coordinate is `x n - f n (x (n + 1))`, with `f n` the transition of `A`
(blueprint: lem-pc-derived-limit-roos-abelian-groups). -/
noncomputable abbrev roosMap (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (∏ᶜ fun n : ℕ => A.obj (Opposite.op n)) ⟶
      (∏ᶜ fun n : ℕ => A.obj (Opposite.op n)) :=
  towerTransitionEndomorphism (K := fun n : ℕ => A.obj (Opposite.op n))
    (fun n => A.map (homOfLE (Nat.le_succ n)).op)

/-- The enough-injectives clause of Stacks Project, Tag 07KW, Lemma 15.88.1 setup
(blueprint: lem-pc-derived-limit-roos-abelian-groups).

Proof (node step 1): apply `lem-pc-tower-enough-injectives` to the abelian tower
category of `lem-pc-tower-abelian`. Every tower embeds in a tower of injective
abelian groups with split-surjective transitions; compatible lifts are constructed
successively, extending at each stage into the injective kernel of the transition.
Thus every tower admits a monomorphism to an injective tower. -/
theorem roosTowerEnoughInjectives : EnoughInjectives (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) := by
  constructor
  intro A
  obtain ⟨I, i, hi, hI, hp⟩ := tower_injective_embedding A
  exact ⟨⟨I, injective_of_injective_split_tower I hI hp, i, hi⟩⟩

attribute [local instance] roosTowerEnoughInjectives

/-- The additivity clause of Stacks Project, Tag 07KW, Lemma 15.88.1 setup
(blueprint: lem-pc-derived-limit-roos-abelian-groups).

Proof (node step 1): use `lem-pc-tower-limit-left-exact`. Finite biproducts of towers
are levelwise, and compatible tuples in a finite biproduct are pairs of compatible
tuples. Inverse limit therefore preserves finite biproducts, hence is additive. -/
theorem roosLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive := by
  constructor
  intro A B f g
  apply limit.hom_ext
  intro n
  simp only [lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
    Preadditive.comp_add]

attribute [local instance] roosLimitAdditive

private noncomputable def roosInclusion (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    limit A ⟶ ∏ᶜ (fun n : ℕ => A.obj (Opposite.op n)) :=
  Pi.lift (fun n => limit.π A (Opposite.op n))

private theorem roosInclusion_zero (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    roosInclusion A ≫ roosMap A = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [roosMap, towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.assoc, Pi.lift_π, roosInclusion, zero_comp]
  simp only [← Category.assoc, Pi.lift_π]
  rw [limit.w A (homOfLE (Nat.le_succ n)).op, sub_self]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def roosKernelCone (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Cone A where
  pt := kernel (roosMap A)
  π := NatTrans.ofOpSequence
    (fun n => kernel.ι (roosMap A) ≫ Pi.π _ n)
    (by
      intro n
      change (𝟙 (kernel (roosMap A))) ≫ (kernel.ι _ ≫ Pi.π _ n) =
        (kernel.ι _ ≫ Pi.π _ (n + 1)) ≫ A.map (homOfLE (Nat.le_succ n)).op
      simp only [Category.id_comp, Category.assoc]
      have h := congrArg (fun f => f ≫ Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n)
        (kernel.condition (roosMap A))
      have hp : roosMap A ≫ Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n =
          Pi.π _ n - Pi.π _ (n + 1) ≫ A.map (homOfLE (Nat.le_succ n)).op := by
        simp [roosMap, towerTransitionEndomorphism, towerProductShift,
          Preadditive.sub_comp]
      rw [Category.assoc, hp, Preadditive.comp_sub] at h
      simp only [zero_comp] at h
      have hc := sub_eq_zero.mp h
      simpa only [Category.id_comp, Category.assoc] using hc)

private noncomputable def roosKernelIso (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    limit A ≅ kernel (roosMap A) where
  hom := kernel.lift _ (roosInclusion A) (roosInclusion_zero A)
  inv := limit.lift A (roosKernelCone A)
  hom_inv_id := by
    apply limit.hom_ext
    intro n
    simp only [Category.assoc, limit.lift_π, roosKernelCone,
      NatTrans.ofOpSequence_app]
    change kernel.lift _ _ _ ≫ (kernel.ι _ ≫ Pi.π _ n.unop) = _
    rw [← Category.assoc, kernel.lift_ι]
    simp [roosInclusion]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (roosMap A))).mp
    simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
    apply Pi.hom_ext
    intro n
    simp [roosInclusion, roosKernelCone, NatTrans.ofOpSequence_app]

private theorem roosKernelIso_naturality (A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (φ : A ⟶ B)
    (h : roosMap A ≫ Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) =
      Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) ≫ roosMap B) :
    limMap φ ≫ (roosKernelIso B).hom = (roosKernelIso A).hom ≫
      kernel.map (roosMap A) (roosMap B)
        (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)))
        (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n))) h := by
  apply (cancel_mono (kernel.ι (roosMap B))).mp
  simp only [roosKernelIso, Category.assoc, kernel.lift_ι, kernel.map, kernel.lift_ι]
  rw [← Category.assoc, kernel.lift_ι]
  apply Pi.hom_ext
  intro n
  simp [roosInclusion]

/-- Roos computation, naturally in the tower, of Stacks Project, Tag 07KW,
Lemma 15.88.1 (blueprint: lem-pc-derived-limit-roos-abelian-groups).

Proof, following the node:
1. The tower category is abelian (`lem-pc-tower-abelian`, here Mathlib's functor-category
instance), has enough injectives (`lem-pc-tower-enough-injectives`), and inverse limit
is additive and left exact (`lem-pc-tower-limit-left-exact`). Its right derived functors
are those of `def-sp-left-exact-additive`.
2. Compatible tuples are exactly the kernel of `1 - s`; this identification is natural.
3. Following Tag 07KW, form `B_n = A_n ⊕ ... ⊕ A_1` and
`C_n = A_{n-1} ⊕ ... ⊕ A_1`, with projection transitions and `C_1 = 0`.
The successive-transition embedding `A_n → B_n` and the difference map `B_n → C_n`
form a levelwise short exact sequence. Injectivity is checked at the first coordinate;
the kernel consists of successive-transition tuples; surjectivity follows by downward
recursion starting with `x_n = 0`. The levelwise universal properties give a short exact
sequence of towers. Both limits are the product of the `A_n`, and the induced map is
`1 - s`. Tower morphisms act componentwise on this construction.
4. The towers `B` and `C` have surjective transitions and so are limit-acyclic by
`lem-pc-tower-surjective-lim-acyclic`. Apply the long exact sequence of
`lem-weil-pbc-horseshoe-delta-functor`, using `R⁰ lim = lim` from
`def-sp-left-exact-additive`: its beginning identifies `R¹ lim A` with the cokernel
of `1 - s`, and its higher terms give `R^q lim A = 0` for `q ≥ 2`.
Naturality follows from the componentwise construction and natural connecting maps.

The witnesses `e₀` and `e₁` are chosen for all towers before the naturality condition.
The witness `h` is the commutative square defining the induced kernel/cokernel maps. -/
theorem derivedLimitRoosAbelianGroups :
    PreservesFiniteLimits
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) ∧
    ∃ (e₀ : ∀ A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}, limit A ≅ kernel (roosMap A))
      (e₁ : ∀ A : ℕᵒᵖ ⥤ AddCommGrpCat.{u},
        ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj A ≅
          cokernel (roosMap A)),
      (∀ (A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (φ : A ⟶ B),
        ∃ h : roosMap A ≫ Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) =
            Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) ≫ roosMap B,
          limMap φ ≫ (e₀ B).hom = (e₀ A).hom ≫
            kernel.map (roosMap A) (roosMap B)
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)))
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n))) h ∧
          ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).map φ ≫
              (e₁ B).hom = (e₁ A).hom ≫
            cokernel.map (roosMap A) (roosMap B)
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)))
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n))) h) ∧
      ∀ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℕ), 2 ≤ q →
        IsZero (((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived q).obj A) := by
  obtain ⟨e₁, hn, hz⟩ := roosPositiveDerivedLimit.{u}
  refine ⟨inferInstance, roosKernelIso, e₁, ?_, hz⟩
  intro A B φ
  obtain ⟨h, hc⟩ := hn A B φ
  exact ⟨h, roosKernelIso_naturality A B φ h, hc⟩

end CategoryTheory
