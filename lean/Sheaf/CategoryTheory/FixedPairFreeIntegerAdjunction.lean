/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Integer-orbit free fixed pairs and their explicit adjunction

Source: WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean, namespace Free,
obj, objSucc, str, map, functor and adjunction
(blueprint: lem-sf-fixed-pair-free-integer-adjunction).

The constructions are the existing upstream ones, using the chosen quasi-inverse `F.inv`
and its counit. No second fixed-pair category or orbit-sum construction is introduced.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- Integer-orbit induction, with its carrier, shift, recursive extension, natural
zeroth-summand adjunction and inherited additivity.

Source: WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean, Free, lines 120--360;
additive calculation from Stacks Tag 00ZY
(blueprint: lem-sf-fixed-pair-free-integer-adjunction).

Proof:
1. Use Free.obj and Free.objMap for positive iterates of F and negative iterates of
   its chosen quasi-inverse. Free.objSucc is identity at nonnegative indices and the
   counit at negative indices. Counit naturality gives compatibility with objMap.
2. The equivalence preserves coproducts (lem-galois-equivalence-preserves-limits).
   The coproduct universal property (def-weil-pbc-category-colimit) gives the shift
   from its displayed injection equation. The inverse shifts backwards and uses
   the inverse counit; checking both composites on injections proves invertibility
   and uniqueness.
3. Coproduct maps of objMap commute with this shift by step 1. The fixed-pair
   morphism equation (def-weil-endofunctor-fixed-pair-category) and coproduct
   uniqueness give the identity and composition laws of Free.functor.
4. At every integer n, h maps to c_n.inv followed by F(h) and the target structure.
   This is bijective by lem-sf-quasi-inverse-hom-bijection and invertibility of the
   two structure comparisons.
5. Starting at a0, recurse forwards by this bijection and backwards by its inverse.
   Two natural-number inductions prove uniqueness on all integers, including -1 to 0.
6. The coproduct-induced map of this family commutes with the structure by its
   recurrence, hence is a fixed-pair morphism.
7. Conversely, restrict a fixed-pair morphism to all summands. Its commuting square
   gives that recurrence; step 5 and coproduct uniqueness identify it with step 6.
   Restriction at zero and extension are therefore inverse.
8. The formula for the map on the zero summand proves naturality in the source;
   associativity proves naturality in the target. Apply
   lem-weil-pbc-adjunction-of-natural-bijection to obtain the specified adjunction.
9. Under the additive hypotheses the commuting-square condition is closed under
   sums, zero and negatives, by bilinearity (def-weil-preadditive-category) and
   additivity (def-weil-pbc-additive-functor). This is the inherited Hom addition.
10. Counit naturality and faithfulness of F show that its quasi-inverse is additive.
    Induction gives additivity of every positive and negative iterate.
11. Restriction to every coprojection then proves that the free functor preserves
    addition and zero, using coproduct uniqueness and faithful forgetting.
-/
theorem fixedPairFreeIntegerAdjunction {C : Type u} [Category.{v} C]
    (F : C ⥤ C) [F.IsEquivalence] [HasColimitsOfShape (Discrete ℤ) C] :
    (∀ M : C, ((Free.functor F).obj M).carrier = ∐ (Free.obj F M)) ∧
    (∀ (M N : C) (f : M ⟶ N),
      ((Free.functor F).map f).hom.f = Limits.Sigma.map (Free.objMap F f)) ∧
    (∀ (M : C) (n : ℤ),
      F.map (Sigma.ι (Free.obj F M) n) ≫ ((Free.functor F).obj M).str.hom =
        (Free.objSucc F M n).hom ≫ Sigma.ι (Free.obj F M) (n + 1)) ∧
    (∀ (M : C) (σ : F.obj (∐ (Free.obj F M)) ≅ ∐ (Free.obj F M)),
      (∀ n : ℤ, F.map (Sigma.ι (Free.obj F M) n) ≫ σ.hom =
        (Free.objSucc F M n).hom ≫ Sigma.ι (Free.obj F M) (n + 1)) →
      σ = ((Free.functor F).obj M).str) ∧
    (∀ (M : C) (K : IsoAlgebra F) (a0 : M ⟶ K.carrier),
      ∃! a : (n : ℤ) → (Free.obj F M n ⟶ K.carrier),
        a 0 = a0 ∧ ∀ n : ℤ,
          (Free.objSucc F M n).hom ≫ a (n + 1) = F.map (a n) ≫ K.str.hom) ∧
    (∃ adj : Free.functor F ⊣ forget F,
      (∀ (M : C) (K : IsoAlgebra F) (a : (Free.functor F).obj M ⟶ K),
        adj.homEquiv M K a = Sigma.ι (Free.obj F M) 0 ≫ a.hom.f) ∧
      (∀ (M : C) (K : IsoAlgebra F) (a0 : M ⟶ K.carrier)
          (a : (n : ℤ) → (Free.obj F M n ⟶ K.carrier)),
        a 0 = a0 →
        (∀ n : ℤ, (Free.objSucc F M n).hom ≫ a (n + 1) = F.map (a n) ≫ K.str.hom) →
        ((adj.homEquiv M K).symm a0).hom.f = Sigma.desc a) ∧
      (∀ (M N : C) (f : M ⟶ N) (K : IsoAlgebra F)
          (a : (Free.functor F).obj N ⟶ K),
        adj.homEquiv M K ((Free.functor F).map f ≫ a) = f ≫ adj.homEquiv N K a) ∧
      (∀ (M : C) (K L : IsoAlgebra F) (a : (Free.functor F).obj M ⟶ K) (b : K ⟶ L),
        adj.homEquiv M L (a ≫ b) = adj.homEquiv M K a ≫ (forget F).map b)) ∧
    (∀ [Preadditive C] [HasFiniteBiproducts C] [F.Additive],
      (Free.functor F).Additive) := by
  have family_ext (M : C) (K : IsoAlgebra F)
      (a b : (n : ℤ) → (Free.obj F M n ⟶ K.carrier))
      (h0 : a 0 = b 0)
      (ha : ∀ n : ℤ,
        (Free.objSucc F M n).hom ≫ a (n + 1) = F.map (a n) ≫ K.str.hom)
      (hb : ∀ n : ℤ,
        (Free.objSucc F M n).hom ≫ b (n + 1) = F.map (b n) ≫ K.str.hom) : a = b := by
    have step : ∀ m n : ℤ, m + 1 = n → (a m = b m ↔ a n = b n) := by
      rintro m _ rfl
      constructor
      · intro hm
        apply (cancel_epi (Free.objSucc F M m).hom).1
        rw [ha m, hb m, hm]
      · intro hm
        apply F.map_injective
        apply (cancel_mono K.str.hom).1
        rw [← ha m, ← hb m, hm]
    funext n
    exact Int.induction_on n h0 (fun i hi ↦ (step _ _ rfl).1 hi)
      (fun i hi ↦ (step _ _ (by omega)).2 hi)
  refine ⟨fun _ ↦ rfl, fun _ _ _ ↦ rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro M n
    exact Free.map_ι_comp_str F M n
  · intro M σ hσ
    apply Iso.ext
    apply Free.map_hom_ext F M
    intro n
    exact (hσ n).trans (Free.map_ι_comp_str F M n).symm
  · intro M K a0
    refine ⟨Free.hom K a0, ⟨Free.hom_zero K a0, ?_⟩, ?_⟩
    · intro n
      exact (Free.map_hom_comp_str K a0 n).symm
    · intro a ha
      exact family_ext M K a (Free.hom K a0)
        (ha.1.trans (Free.hom_zero K a0).symm) ha.2
        (fun n ↦ (Free.map_hom_comp_str K a0 n).symm)
  · refine ⟨Free.adjunction F, ?_, ?_, ?_, ?_⟩
    · intro M K a
      simp only [Free.adjunction, Adjunction.mkOfHomEquiv_homEquiv]
      rfl
    · intro M K a0 a h0 ha
      simp only [Free.adjunction, Adjunction.mkOfHomEquiv_homEquiv]
      change Sigma.desc (Free.hom K a0) = Sigma.desc a
      exact congrArg Sigma.desc (family_ext M K (Free.hom K a0) a
        ((Free.hom_zero K a0).trans h0.symm)
        (fun n ↦ (Free.map_hom_comp_str K a0 n).symm) ha)
    · intro M N f K a
      exact (Free.adjunction F).homEquiv_naturality_left f a
    · intro M K L a b
      exact (Free.adjunction F).homEquiv_naturality_right a b
  · intro _ _ _
    refine ⟨fun {M N} f g ↦ Free.hom_ext ?_⟩
    change Sigma.ι (Free.obj F M) 0 ≫ (Free.map (f + g)).hom.f =
      Sigma.ι (Free.obj F M) 0 ≫ ((Free.map f).hom.f + (Free.map g).hom.f)
    simp [Free.map_hom_f, Preadditive.comp_add, Sigma.ι_map]

end CategoryTheory.Endofunctor.IsoAlgebra
