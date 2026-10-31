/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedComplexes
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The kernel of the ordinary coinduced difference

Source: Stacks 0941, with the compatible-family assembly argument of the coinduced resolution.
(blueprint: lem-coef-sequence-coinduced-kernel).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction

attribute [local irreducible] constantSheaf presheafToSheaf

private theorem conjugate_apply
    {A B A' B' : AddCommGrpCat.{u}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g)
    (x : A) (y : A') (hxy : HEq x y) : HEq (f x) (g y) := by
  subst A' B'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst g
  have hx : x = y := eq_of_heq hxy
  subst y
  rfl

set_option maxHeartbeats 400000 in
-- The concrete coefficient ring identifications require extra reduction.
private theorem transition_section
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (N : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m)
    (U : W.ProEtᵒᵖ)
    (x : N.val.obj (op (m, U.unop))) :
    ((coefficientSequenceTransition l E W h).app N).val.app U x =
      N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  have ht := (coefficientSequenceTransition_exists l E W h).exists.choose_spec N U
  have hh := conjugate_apply
    (coefficientSequenceEvaluationAb_eq l E W N m U)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W N h U)
    ((forget₂ (ModuleCat.{u + 1}
      ((integralCoefficientSheaf l E W m).obj.obj U)) AddCommGrpCat).map
        (((coefficientSequenceTransition l E W h).app N).val.app U))
    (N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) ht x x (HEq.refl x)
  exact eq_of_heq hh

section Assembly
universe c v w
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]

private instance pushforward_additive
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{w})
    (A : Sheaf J RingCat.{w}) (n : ℕ)
    (φ : A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R) :
    (SheafOfModules.pushforward.{w} φ).Additive where
  map_add := by
    intro M N f g
    ext U x
    rfl

private theorem assemble_sections
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{w})
    (A : ℕ → Sheaf J RingCat.{w})
    (φ : ∀ n, A n ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R) [∀ n, IsIso (φ n)]
    (M N : CochainComplex (SheafOfModules.{w} R) ℤ)
    (f : ∀ n, ((SheafOfModules.pushforward (φ n)).mapHomologicalComplex (.up ℤ)).obj M ⟶
      ((SheafOfModules.pushforward (φ n)).mapHomologicalComplex (.up ℤ)).obj N)
    (hs : ∀ (i : ℤ) (n : ℕ) (U : Cᵒᵖ)
      (x : (M.X i).val.obj (op (n + 1, U.unop))),
      ((f n).f i).val.app U
          ((M.X i).val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x) =
        (N.X i).val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
          (((f (n + 1)).f i).val.app U x)) :
    ∃ g : M ⟶ N, ∀ n,
      ((SheafOfModules.pushforward (φ n)).mapHomologicalComplex (.up ℤ)).map g = f n := by
  have hh (i : ℤ) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) :
      ∀ x : (M.X i).val.obj (op (n, U.unop)),
        ((f m).f i).val.app U
            ((M.X i).val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) =
          (N.X i).val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
            (((f n).f i).val.app U x) := by
    induction n, h using Nat.le_induction with
    | base =>
        intro x
        change ((f m).f i).val.app U ((M.X i).val.map (𝟙 _) x) =
          (N.X i).val.map (𝟙 _) (((f m).f i).val.app U x)
        erw [PresheafOfModules.map_id, PresheafOfModules.map_id]
        rfl
    | succ n h ih =>
        intro x
        have hc : (Prod.mkHom (homOfLE (h.trans (Nat.le_succ n))) (𝟙 U.unop)).op =
            (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op ≫
              (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op := by
          apply Quiver.Hom.unop_inj
          apply Prod.hom_ext
          · exact Subsingleton.elim _ _
          · simp
        erw [hc, PresheafOfModules.map_comp_apply, PresheafOfModules.map_comp_apply,
          ih, hs]
  let a (i : ℤ) : M.X i ⟶ N.X i :=
    ⟨{ app := fun X ↦ ModuleCat.ofHom
          { toFun := fun x ↦ ((f X.unop.1).f i).val.app (op X.unop.2) x
            map_add' := by intro x y; exact map_add _ _ _
            map_smul' := by
              intro c x
              let U := op X.unop.2
              let c' := ((asIso (φ X.unop.1)).inv.hom.app U) c
              have hc : ((φ X.unop.1).hom.app U) c' = c := by
                exact congrArg (fun z ↦ z.hom.app U c)
                  (asIso (φ X.unop.1)).inv_hom_id
              have h := (((f X.unop.1).f i).val.app U).hom.map_smul c' x
              change ((f X.unop.1).f i).val.app U
                  ((show R.obj.obj X from ((φ X.unop.1).hom.app U) c') • x) =
                (show R.obj.obj X from ((φ X.unop.1).hom.app U) c') •
                  (show (N.X i).val.obj X from
                    (((f X.unop.1).f i).val.app U x)) at h
              rw [hc] at h
              exact h }
       naturality := by
         intro X Y k
         ext x
         have hc : k =
             (Prod.mkHom k.unop.1 (𝟙 X.unop.2)).op ≫
               (Prod.mkHom (𝟙 Y.unop.1) k.unop.2).op := by
           apply Quiver.Hom.unop_inj
           apply Prod.hom_ext <;> simp
         change ((f Y.unop.1).f i).val.app (op Y.unop.2) ((M.X i).val.map k x) =
           (N.X i).val.map k (((f X.unop.1).f i).val.app (op X.unop.2) x)
         erw [hc, PresheafOfModules.map_comp_apply, PresheafOfModules.map_comp_apply]
         have hv := PresheafOfModules.naturality_apply ((f Y.unop.1).f i).val
           k.unop.2.op
           ((M.X i).val.map (Prod.mkHom k.unop.1 (𝟙 X.unop.2)).op x)
         change ((f Y.unop.1).f i).val.app (op Y.unop.2)
             ((M.X i).val.map (Prod.mkHom (𝟙 Y.unop.1) k.unop.2).op
               ((M.X i).val.map (Prod.mkHom k.unop.1 (𝟙 X.unop.2)).op x)) =
           (N.X i).val.map (Prod.mkHom (𝟙 Y.unop.1) k.unop.2).op
             (((f Y.unop.1).f i).val.app (op X.unop.2)
               ((M.X i).val.map (Prod.mkHom k.unop.1 (𝟙 X.unop.2)).op x)) at hv
         erw [hv, hh i (leOfHom k.unop.1)]
         exact congrArg
           (fun a : Y.unop.1 ⟶ X.unop.1 ↦
             (N.X i).val.map (Prod.mkHom (𝟙 Y.unop.1) k.unop.2).op
               ((N.X i).val.map (Prod.mkHom a (𝟙 X.unop.2)).op
                 (((f X.unop.1).f i).val.app (op X.unop.2) x)))
           (Subsingleton.elim _ _) }⟩
  let g : M ⟶ N :=
    { f := a
      comm' := by
        intro i j _
        ext X x
        exact congrArg (fun z ↦ z.val.app (op X.unop.2) x) ((f X.unop.1).comm i j) }
  refine ⟨g, ?_⟩
  intro n
  ext i U x
  rfl

end Assembly

private theorem restricted_square
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (φ : R ⟶ S)
    (M₀ N₀ : CochainComplex (SheafOfModules.{u} S) ℤ)
    (M₁ N₁ : CochainComplex (SheafOfModules.{u} R) ℤ)
    (f₀ : M₀ ⟶ N₀) (f₁ : M₁ ⟶ N₁)
    (a : M₁ ⟶ ((SheafOfModules.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj M₀)
    (b : N₁ ⟶ ((SheafOfModules.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj N₀)
    (h : f₁ ≫ b = a ≫
      ((SheafOfModules.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map f₀)
    (i : ℤ) (U : Cᵒᵖ) (x : (M₁.X i).val.obj U) :
    (f₀.f i).val.app U ((a.f i).val.app U x) =
      (b.f i).val.app U ((f₁.f i).val.app U x) := by
  exact (congrArg (fun z ↦ (z.f i).val.app U x) h).symm

section Compatibility
universe c v w
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]

private theorem assemble_compatible
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{w})
    (A : ℕ → Sheaf J RingCat.{w})
    (φ : ∀ n, A n ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R) [∀ n, IsIso (φ n)]
    (ψ : ∀ n, A (n + 1) ⟶ A n)
    (τ : ∀ n, SheafOfModules.pushforward.{w} (φ (n + 1)) ⟶
      SheafOfModules.pushforward.{w} (φ n) ⋙ SheafOfModules.restrictScalars (ψ n))
    (hτ : ∀ (n : ℕ) (X : SheafOfModules.{w} R) (U : Cᵒᵖ)
      (x : X.val.obj (op (n + 1, U.unop))),
      ((τ n).app X).val.app U x =
        X.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)
    (M N : CochainComplex (SheafOfModules.{w} R) ℤ)
    (f : ∀ n, ((SheafOfModules.pushforward (φ n)).mapHomologicalComplex (.up ℤ)).obj M ⟶
      ((SheafOfModules.pushforward (φ n)).mapHomologicalComplex (.up ℤ)).obj N)
    (hf : ∀ n, f (n + 1) ≫ ((τ n).mapHomologicalComplex (.up ℤ)).app N =
      ((τ n).mapHomologicalComplex (.up ℤ)).app M ≫
        ((SheafOfModules.restrictScalars (ψ n)).mapHomologicalComplex (.up ℤ)).map (f n)) :
    ∃ g : M ⟶ N, ∀ n,
      ((SheafOfModules.pushforward (φ n)).mapHomologicalComplex (.up ℤ)).map g = f n := by
  apply assemble_sections J R A φ M N f
  intro i n U x
  have he := restricted_square (ψ n)
    (((SheafOfModules.pushforward (φ n)).mapHomologicalComplex (.up ℤ)).obj M)
    (((SheafOfModules.pushforward (φ n)).mapHomologicalComplex (.up ℤ)).obj N)
    (((SheafOfModules.pushforward (φ (n + 1))).mapHomologicalComplex (.up ℤ)).obj M)
    (((SheafOfModules.pushforward (φ (n + 1))).mapHomologicalComplex (.up ℤ)).obj N)
    (f n) (f (n + 1)) (((τ n).mapHomologicalComplex (.up ℤ)).app M)
    (((τ n).mapHomologicalComplex (.up ℤ)).app N) (hf n) i U x
  have hM := hτ n (M.X i) U x
  have hN := hτ n (N.X i) U (((f (n + 1)).f i).val.app U x)
  exact (congrArg (fun y ↦ ((f n).f i).val.app U y) hM).symm.trans
    (he.trans hN)

end Compatibility

attribute [local irreducible] coefficientSequenceTransition normalizedDVRQuotient
  integralCoefficientSheaf integralCoefficientCommRingSheaf coefficientSequenceCommRingSheaf

set_option maxHeartbeats 400000 in
-- Assembly checks the scalar transports of evaluation on the sequence site.
private theorem assemble
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (M N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (f : ∀ n, (complexEvaluation l E W n).obj M ⟶
      (complexEvaluation l E W n).obj N)
    (hf : ∀ n, f (n + 1) ≫ (complexTransition l E W n).app N =
      (complexTransition l E W n).app M ≫ (complexRestriction l E W n).map (f n)) :
    ∃ g : M ⟶ N, ∀ n, (complexEvaluation l E W n).map g = f n := by
  exact assemble_compatible (Scheme.ProEt.topology W) _
    (fun n ↦ integralCoefficientSheaf l E W n)
    (fun n ↦ eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm)
    (fun n ↦ normalizedDVRQuotient l E W (Nat.le_succ n))
    (fun n ↦ coefficientSequenceTransition l E W (Nat.le_succ n))
    (fun n X U x ↦ transition_section l E W X (Nat.le_succ n) U x) M N f hf

section KernelCriterion
universe c cv d dv
variable {C : Type c} [Category.{cv} C] [Abelian C]
  {D : ℕ → Type d} [∀ n, Category.{dv} (D n)] [∀ n, Preadditive (D n)]
  (Ev : ∀ n, C ⥤ D n) (R : ∀ n, D n ⥤ C) (adj : ∀ n, Ev n ⊣ R n)
  (S : ∀ n, D n ⥤ D (n + 1)) (t : ∀ n, Ev (n + 1) ⟶ Ev n ⋙ S n)
  [∀ n, (Ev n).Additive] [∀ n, (R n).Additive] [∀ n, (S n).Additive]
  [HasCountableProducts C]

private theorem kernel_cokernel_zero (K : C)
    (assembly : ∀ (M : C) (f : ∀ n, (Ev n).obj M ⟶ (Ev n).obj K),
      (∀ n, f (n + 1) ≫ (t n).app K = (t n).app M ≫ (S n).map (f n)) →
      ∃ g : M ⟶ K, ∀ n, (Ev n).map g = f n) :
    kernel.ι (CoinducedSequence.difference Ev R adj S t K) ≫
      cokernel.π (CoinducedSequence.augmentation Ev R adj K) = 0 := by
  have lift {M : C} (b : M ⟶ CoinducedSequence.product Ev R K)
      (hb : b ≫ CoinducedSequence.difference Ev R adj S t K = 0) :
      ∃ g : M ⟶ K, g ≫ CoinducedSequence.augmentation Ev R adj K = b := by
    let f := CoinducedSequence.components Ev R adj b
    have hf (n : ℕ) : f (n + 1) ≫ (t n).app K =
        (t n).app M ≫ (S n).map (f n) := by
      have hd := CoinducedSequence.difference_component Ev R adj S t b n
      apply sub_eq_zero.mp
      change (show (Ev (n + 1)).obj M ⟶ (S n).obj ((Ev n).obj K) from
        CoinducedSequence.components Ev R adj b (n + 1) ≫ (t n).app K) -
          (t n).app M ≫ (S n).map (CoinducedSequence.components Ev R adj b n) = 0
      erw [← hd, ← Category.assoc, hb, zero_comp]
      simp
    obtain ⟨g, hg⟩ := assembly M f hf
    refine ⟨g, ?_⟩
    apply Pi.hom_ext
    intro n
    apply ((adj n).homEquiv _ _).symm.injective
    change CoinducedSequence.components Ev R adj
      (g ≫ CoinducedSequence.augmentation Ev R adj K) n = f n
    rw [CoinducedSequence.components_augmentation]
    exact hg n
  obtain ⟨g, hg⟩ := lift (kernel.ι (CoinducedSequence.difference Ev R adj S t K))
    (kernel.condition _)
  rw [← hg, Category.assoc, cokernel.condition, comp_zero]

private theorem sequence_exact (K : C)
    (assembly : ∀ (M : C) (f : ∀ n, (Ev n).obj M ⟶ (Ev n).obj K),
      (∀ n, f (n + 1) ≫ (t n).app K = (t n).app M ≫ (S n).map (f n)) →
      ∃ g : M ⟶ K, ∀ n, (Ev n).map g = f n) :
    (ShortComplex.mk (CoinducedSequence.augmentation Ev R adj K)
      (CoinducedSequence.difference Ev R adj S t K)
      (CoinducedSequence.augmentation_difference Ev R adj S t K)).Exact := by
  apply (ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero _).2
  exact kernel_cokernel_zero Ev R adj S t K assembly

end KernelCriterion

set_option maxHeartbeats 400000 in
-- Transposing the product projections unfolds the specified complex adjunction.
/-- Exactness at the middle term of the ordinary coinduced sequence.
Source: Stacks 0941 and 07A6; the kernel step of the proof of
lem-coef-sequence-coinduced-complex-short-exact.
(blueprint: lem-coef-sequence-coinduced-kernel).

Proof: let b : M → complexProduct(K) be killed by complexDifference. Transposing
its product projections by the complex adjunctions gives chain maps
f_n : e_n M → e_n K, and the difference_component identity says that the adjacent
defect f_(n+1)·τ_n − τ_n·r_n(f_n) is zero, so the family is compatible with the
transitions. On sections the transition of the sequence site is the horizontal
restriction (the section formula of coefficientSequenceTransition); induction on the
upper level gives compatibility with every horizontal restriction, the slice ring maps
are isomorphisms so the components are linear over the sequence ring, and factoring a
sequence-site arrow into horizontal and vertical parts assembles the f_n into a chain
map g : M → K with e_n g = f_n. By components_augmentation, g followed by the
augmentation has the same projections as b, so it equals b. Applied to the kernel
inclusion of the difference, the kernel inclusion followed by the cokernel projection
of the augmentation is zero, which is exactness (Mathlib
ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero). The case n = 0 needs no
separate treatment. -/
theorem complexSequence_exact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (complexSequence l E W K).Exact := by
  unfold complexSequence complexAugmentation complexDifference
  exact sequence_exact (complexEvaluation l E W) (complexRight l E W)
    (complexAdjunction l E W) (complexRestriction l E W) (complexTransition l E W) K
    (fun M f hf ↦ assemble l E W M K f hf)

end WeilConjectures.CoefficientCoinduction
