/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalCone.PrincipalConeTower
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.RingTheory.Nilpotent.Basic
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import all WeilConjectures.Algebra.Homology.RoosSplitComparison
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.CategoryTheory.Principal.PrincipalConeKoszulRoosComparison
/-! # Nilpotent power-cone completion

The normalized Roos augmentation of the power-cone tower of a nilpotent chain
endomorphism is a quasi-isomorphism. This uses no exactness of countable products.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe a b w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory.RingedPowerTorsion
private theorem constant_shift_power {B : Type a} [Category.{b} B]
    (P : B) [HasProduct (fun _ : ℕ ↦ P)] (μ : End P) (m n : ℕ) :
    (End.of (towerProductShift (K := fun _ : ℕ ↦ P) (fun _ ↦ μ)) ^ m) ≫
        Pi.π (fun _ : ℕ ↦ P) n =
      Pi.π (fun _ : ℕ ↦ P) (n + m) ≫ (μ ^ m) := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', End.mul_def, Category.assoc]
    rw [show (towerProductShift (K := fun _ : ℕ ↦ P) (fun _ ↦ μ)) ≫
        Pi.π (fun _ : ℕ ↦ P) n = Pi.π _ (n + 1) ≫ μ by
      simp only [towerProductShift, Pi.lift_π]]
    rw [← Category.assoc, ih]
    simp only [Category.assoc, pow_succ', End.mul_def, Nat.add_assoc,
      Nat.add_comm 1 m]

private theorem nilpotent_shift_isIso {B : Type a} [Category.{b} B] [Preadditive B]
    (P : B) [HasProduct (fun _ : ℕ ↦ P)] (μ : End P) (m : ℕ) (h : μ ^ m = 0) :
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ P) (fun _ ↦ μ)) := by
  let S : End (∏ᶜ fun _ : ℕ ↦ P) := towerProductShift (fun _ ↦ μ)
  have hS : S ^ m = 0 := by
    apply Pi.hom_ext
    intro n
    rw [constant_shift_power P μ m n, h, comp_zero, zero_comp]
  exact (isUnit_iff_isIso _).mp ((show IsNilpotent S from ⟨m, hS⟩).isUnit_one_sub)

private def constantRec {B : Type a} [Category.{b} B] [Preadditive B]
    (P : B) [HasProduct (fun _ : ℕ ↦ P)] [HasBinaryBiproduct P (∏ᶜ fun _ : ℕ ↦ P)] :
    ℕ → (P ⊞ (∏ᶜ fun _ : ℕ ↦ P) ⟶ P)
  | 0 => biprod.fst
  | n + 1 => constantRec P n - biprod.snd ≫ Pi.π _ n

private def constantProductIso {B : Type a} [Category.{b} B] [Preadditive B]
    (P : B) [HasProduct (fun _ : ℕ ↦ P)] [HasBinaryBiproduct P (∏ᶜ fun _ : ℕ ↦ P)] :
    (∏ᶜ fun _ : ℕ ↦ P) ≅ P ⊞ (∏ᶜ fun _ : ℕ ↦ P) where
  hom := biprod.lift (Pi.π _ 0)
    (towerTransitionEndomorphism (K := fun _ : ℕ ↦ P) (fun _ ↦ 𝟙 P))
  inv := Pi.lift (constantRec P)
  hom_inv_id := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π, Category.id_comp]
    induction n with
    | zero => simp [constantRec]
    | succ n ih =>
      rw [constantRec, Preadditive.comp_sub, ih]
      rw [← Category.assoc, biprod.lift_snd]
      simp only [towerTransitionEndomorphism, Preadditive.sub_comp, Category.id_comp,
        towerProductShift, Pi.lift_π, Category.comp_id]
      abel
  inv_hom_id := by
    apply biprod.hom_ext
    · simp [Category.assoc, constantRec]
    · apply Pi.hom_ext
      intro n
      simp only [Category.assoc, biprod.lift_snd_assoc, Category.id_comp]
      simp only [towerTransitionEndomorphism, Preadditive.sub_comp,
        Category.id_comp, Preadditive.comp_sub, towerProductShift, Pi.lift_π,
        Category.comp_id]
      rw [constantRec]
      abel

private theorem row_roosLift_quasiIso
    {B : Type a} [Category.{b} B] [Abelian B] [HasCountableProducts B]
    {N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} {P : CochainComplex B ℤ}
    (i : P ⟶ roosP N) (hi : i ≫ roosU N = 0)
    (hker : IsLimit (KernelFork.ofι i hi))
    (hepi : ∀ p : ℤ, Epi ((roosU N).f p)) : QuasiIso (roosLift i hi) := by
  let e : P ≅ kernel (roosU N) := hker.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ kernel.ι (roosU N) = i :=
    hker.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
  have hκ : QuasiIso (CochainComplex.comparison (roosU N)) :=
    CochainComplex.comparison_quasiIso (roosU N) hepi
  have h : roosLift i hi = e.hom ≫ CochainComplex.comparison (roosU N) := by
    ext k : 1
    obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change p + 1 = k at hp
    subst k
    apply (cancel_mono (roosχ N p).hom).mp
    rw [roosLift_χ]
    simp only [HomologicalComplex.comp_f, roosχ, Iso.trans_hom, Category.assoc]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.braiding_hom,
        biprod.lift_fst, cofiber_biprod_snd]
      rw [(CochainComplex.comparison_projections (roosU N) (p + 1) p
        (by omega)).1, comp_zero]
    · simp only [Category.assoc, biprod.lift_snd, biprod.braiding_hom,
        biprod.lift_snd, cofiber_biprod_fst]
      rw [(CochainComplex.comparison_projections (roosU N) (p + 1) p
        (by omega)).2]
      exact (congrArg (fun f ↦ f.f (p + 1)) he).symm
  rw [h]
  exact quasiIso_comp _ _

private def constantProduct_kernel {B : Type a} [Category.{b} B] [Preadditive B]
    (P : B) [HasProduct (fun _ : ℕ ↦ P)]
    (h : Pi.lift (fun _ : ℕ ↦ 𝟙 P) ≫
      towerTransitionEndomorphism (K := fun _ : ℕ ↦ P) (fun _ ↦ 𝟙 P) = 0) :
    IsLimit (KernelFork.ofι (Pi.lift (fun _ : ℕ ↦ 𝟙 P)) h) := by
  let i := Pi.lift (fun _ : ℕ ↦ 𝟙 P)
  let U := towerTransitionEndomorphism (K := fun _ : ℕ ↦ P) (fun _ ↦ 𝟙 P)
  apply Fork.IsLimit.mk'
  intro s
  have hs (n : ℕ) : s.ι ≫ Pi.π (fun _ : ℕ ↦ P) (n + 1) =
      s.ι ≫ Pi.π (fun _ : ℕ ↦ P) n := by
    have hz : s.ι ≫ U = 0 := by simpa only [comp_zero] using s.condition
    have hh := congrArg (fun f ↦ f ≫ Pi.π (fun _ : ℕ ↦ P) n) hz
    have hh' : s.ι ≫ Pi.π (fun _ : ℕ ↦ P) n -
        s.ι ≫ Pi.π (fun _ : ℕ ↦ P) (n + 1) = 0 := by
      simpa [U, towerTransitionEndomorphism, towerProductShift,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
        Category.id_comp] using hh
    exact (sub_eq_zero.mp hh').symm
  have hc (n : ℕ) : s.ι ≫ Pi.π (fun _ : ℕ ↦ P) n =
      s.ι ≫ Pi.π (fun _ : ℕ ↦ P) 0 := by
    induction n with
    | zero => rfl
    | succ n ih => exact (hs n).trans ih
  refine ⟨s.ι ≫ Pi.π (fun _ : ℕ ↦ P) 0, ?_, ?_⟩
  · apply Pi.hom_ext
    intro n
    change ((s.ι ≫ Pi.π (fun _ : ℕ ↦ P) 0) ≫
      Pi.lift (fun _ : ℕ ↦ 𝟙 P)) ≫ Pi.π (fun _ : ℕ ↦ P) n =
      s.ι ≫ Pi.π (fun _ : ℕ ↦ P) n
    simpa only [Category.assoc, Pi.lift_π, Category.comp_id] using (hc n).symm
  · intro m hm
    have hh := congrArg (fun f ↦ f ≫ Pi.π (fun _ : ℕ ↦ P) 0) hm
    change (m ≫ Pi.lift (fun _ : ℕ ↦ 𝟙 P)) ≫ Pi.π (fun _ : ℕ ↦ P) 0 =
      s.ι ≫ Pi.π (fun _ : ℕ ↦ P) 0 at hh
    rw [Category.assoc, Pi.lift_π] at hh
    exact (Category.comp_id (show s.pt ⟶ P from m)).symm.trans hh

private theorem constant_roos_augmentation
    {B : Type a} [Category.{b} B] [Abelian B] [HasCountableProducts B]
    (P : CochainComplex B ℤ) :
    let N := ((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapHomologicalComplex (.up ℤ)).obj P
    QuasiIso (roosAugment (X := N) (fun _ ↦ 𝟙 P)
      (fun _ ↦ by ext q : 1; simp only [Category.id_comp]; rfl)) := by
  intro N
  let γ : ∀ n : ℕ, P ⟶ N.asFunctor.obj (op n) := fun _ ↦ 𝟙 P
  have hγ (n : ℕ) : γ (n + 1) ≫ N.asFunctor.map (homOfLE (Nat.le_succ n)).op =
      γ n := by
    ext q : 1
    simp [γ, N]
  let i := Pi.lift γ
  let U := towerTransitionEndomorphism (K := fun _ : ℕ ↦ P) (fun _ ↦ 𝟙 P)
  have hU : roosU N = U := by
    rfl
  have hi : i ≫ roosU N = 0 := by
    change i ≫ U = 0
    change Pi.lift (fun _ : ℕ ↦ 𝟙 P) ≫ U = 0
    apply Pi.hom_ext
    intro n
    simp [U, towerTransitionEndomorphism, towerProductShift, Category.assoc]
  have hker : IsLimit (KernelFork.ofι i hi) := constantProduct_kernel P hi
  have hu : (constantProductIso P).hom ≫ biprod.snd = U := by
    exact biprod.lift_snd _ _
  have hsplit : IsSplitEpi U := IsSplitEpi.mk' ⟨
    biprod.inr ≫ (constantProductIso P).inv, by
      simp only [← hu, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd]⟩
  have hsplit' : IsSplitEpi (roosU N) := by rw [hU]; exact hsplit
  exact row_roosLift_quasiIso i hi hker (fun p ↦ inferInstance)

namespace RowEvalCone
variable {A : Type a} [Category.{b} A] [Abelian A]
open CochainComplex RoosConeCalculus
end RowEvalCone

private def rowTranspose {B : Type a} [Category.{b} B] [Abelian B]
    (X : ℕᵒᵖ ⥤ CochainComplex B ℤ) : CochainComplex (ℕᵒᵖ ⥤ B) ℤ where
  X i := { obj := fun n ↦ (X.obj n).X i
           map := fun f ↦ (X.map f).f i
           map_id := fun n ↦ by simp
           map_comp := fun f g ↦ by simp }
  d i j := { app := fun n ↦ (X.obj n).d i j }
  shape i j h := NatTrans.ext (by funext n; exact (X.obj n).shape i j h)
  d_comp_d' i j k _ _ := NatTrans.ext (by funext n; exact (X.obj n).d_comp_d i j k)

private def rowTransposeMap {B : Type a} [Category.{b} B] [Abelian B]
    {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) :
    rowTranspose X ⟶ rowTranspose Y where
  f i := { app := fun n ↦ (f.app n).f i
           naturality := fun n m g ↦ congrArg (fun h ↦ h.f i) (f.naturality g) }
  comm' i j _ := NatTrans.ext (by funext n; exact (f.app n).comm i j)

private theorem roosAugment_map {B : Type a} [Category.{b} B] [Abelian B]
    [HasCountableProducts B] {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y)
    {P : CochainComplex B ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (δ : ∀ n : ℕ, P ⟶ Y.asFunctor.obj (op n))
    (hδ : ∀ n, δ (n + 1) ≫ Y.asFunctor.map (homOfLE (Nat.le_succ n)).op = δ n)
    (h : ∀ n, γ n ≫ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
      (op n) = δ n) :
    roosAugment γ hγ ≫ roosF.map f = roosAugment δ hδ := by
  have hp : Pi.lift γ ≫ roosPmap f = Pi.lift δ := by
    apply Pi.hom_ext
    intro n
    simp only [roosPmap, Category.assoc, Pi.map_π, Pi.lift_π_assoc, Pi.lift_π]
    exact h n
  ext k : 1
  obtain ⟨p, hp'⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change p + 1 = k at hp'
  subst k
  apply (cancel_mono (roosχ Y p).hom).mp
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [roosF_map_χ, ← Category.assoc, roosAugment_χ, roosAugment_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
    exact congrArg (fun z ↦ z.f (p + 1)) hp


set_option maxHeartbeats 1200000 in
-- Coherence checks compare evaluated cones and their product presentations.
/-- The normalized unit into the Roos completion of the power-cone tower is a
quasi-isomorphism for a nilpotent endomorphism.
Source: Bhatt--Scholze, Lemma 3.4.9; Stacks Tags 08TC and 0941
(blueprint: lem-sp-nilpotent-principal-cone-unit).

Proof: Regard the power-cone tower as the cone of the natural map from the tower
with constant object P and transition μ to the constant tower P, whose level n map
is μ^(n+1). The former has zero Roos object in the derived category: its transition
shift S has S^m=0, so 1-S is invertible. The constant tower's augmentation is a
quasi-isomorphism. Indeed its difference map is split epic, with kernel the
diagonal P, by the product isomorphism (ev₀,1-S). The Roos cone comparison therefore
makes the augmented cone tower quasi-isomorphic to P. Evaluation commutes with
cones and their inclusions; the normalized power-cone comparison transports this
result to the prescribed unit. All maps are chain maps, so unbounded P is allowed. -/
theorem quasiIso_principalConeUnit_of_nilpotent
    {B : Type a} [Category.{b} B] [Abelian B] [HasCountableProducts B]
    [HasDerivedCategory.{w} B] (P : CochainComplex B ℤ)
    (μ : End P) (m : ℕ) (hm : μ ^ m = 0) :
    QuasiIso (CochainComplex.PrincipalCone.unit μ) := by
  classical
  let F : ℕᵒᵖ ⥤ CochainComplex B ℤ := Functor.ofOpSequence (X := fun _ : ℕ ↦ P) (fun _ : ℕ ↦ μ)
  let G : ℕᵒᵖ ⥤ CochainComplex B ℤ := (Functor.const ℕᵒᵖ).obj P
  let α : F ⟶ G := NatTrans.ofOpSequence (fun n ↦ μ ^ (n + 1)) (by
    intro n
    simp only [F, G, Functor.ofOpSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    exact (CochainComplex.PrincipalCone.square μ n).symm.trans (by simp))
  let N := rowTranspose F
  let Y := rowTranspose G
  let f : N ⟶ Y := rowTransposeMap α
  have hU : roosU N = towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ P) (fun _ ↦ μ) := by
    unfold roosU
    congr 1
    funext n
    ext q : 1
    exact congrArg (fun g ↦ g.f q) (Functor.ofOpSequence_map_homOfLE_succ
      (X := fun _ : ℕ ↦ P) (fun _ : ℕ ↦ μ) n)
  have hUi : IsIso (roosU N) := by
    rw [hU]
    exact nilpotent_shift_isIso P μ m hm
  have hzero : IsZero (DerivedCategory.Q.obj (roosF.obj N)) := by
    exact Triangle.isZero₁_of_isIso₂ _
      (DerivedCategory.mappingCocone_triangle_distinguished (roosU N))
      (show IsIso (DerivedCategory.Q.map (roosU N)) from inferInstance)
  have hinc : QuasiIso (roosF.map (CochainComplex.mappingCone.inr f)) := by
    have hh : IsIso (DerivedCategory.Q.map
        (CochainComplex.mappingCone.inr (roosF.map f))) :=
      (Triangle.isZero₁_iff_isIso₂ _
        (DerivedCategory.mappingCone_triangle_distinguished (roosF.map f))).mp hzero
    have he := CategoryTheory.RoosConeCalculus.cone_inclusion f
    have heq := congrArg DerivedCategory.Q.map he
    simp only [Functor.map_comp] at heq
    have hiso : IsIso (DerivedCategory.Q.map
        (roosF.map (CochainComplex.mappingCone.inr f)) ≫
        DerivedCategory.Q.map (CategoryTheory.RoosConeCalculus.coneIso f).hom) := by
      rw [heq]
      exact hh
    have hleft : IsIso (DerivedCategory.Q.map
        (roosF.map (CochainComplex.mappingCone.inr f))) :=
      IsIso.of_isIso_comp_right
        (DerivedCategory.Q.map (roosF.map (CochainComplex.mappingCone.inr f)))
        (DerivedCategory.Q.map (CategoryTheory.RoosConeCalculus.coneIso f).hom)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).mp hleft
  let T := (CochainComplex.mappingCone f).asFunctor
  let ε : (Functor.const ℕᵒᵖ).obj P ⟶ Y.asFunctor :=
    { app := fun _ ↦ 𝟙 P
      naturality := by
        intro n n' g
        ext q : 1
        simp [Y, rowTranspose, G] }
  let γ : (Functor.const ℕᵒᵖ).obj P ⟶ T :=
    ε ≫ HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (CochainComplex.mappingCone.inr f)
  have hY : QuasiIso (roosAugment (X := Y) (fun _ ↦ 𝟙 P)
      (fun n ↦ by ext q : 1; simp only [Category.id_comp]; rfl)) :=
    constant_roos_augmentation P
  have hγ : ∀ n, γ.app (op (n + 1)) ≫ T.map (homOfLE (Nat.le_succ n)).op =
      γ.app (op n) := fun n ↦ by
    exact (γ.naturality (homOfLE (Nat.le_succ n)).op).symm.trans
      (Category.id_comp (γ.app (op n)))
  have haug : QuasiIso (roosAugment (fun n ↦ γ.app (op n)) hγ) := by
    have he := roosAugment_map (CochainComplex.mappingCone.inr f)
      (fun _ ↦ 𝟙 P) (fun n ↦ by ext q : 1; simp only [Category.id_comp]; rfl)
      (fun n ↦ γ.app (op n)) hγ (fun n ↦ by simp [γ, ε])
    rw [← he]
    exact quasiIso_comp _ _
  let a (n : ℕ) : CochainComplex.PrincipalCone.level μ n ≅ T.obj (op n) :=
    (RowEvalCone.coneIso f (op n)).symm
  have hf (n : ℕ) : (RowEvalCone.eval (op n)).map f = μ ^ (n + 1) := rfl
  have hN (n : ℕ) : N.asFunctor.map (homOfLE (Nat.le_succ n)).op = μ := by
    ext q : 1
    exact congrArg (fun g ↦ g.f q) (Functor.ofOpSequence_map_homOfLE_succ
      (X := fun _ : ℕ ↦ P) (fun _ : ℕ ↦ μ) n)
  have hYmap (n : ℕ) : Y.asFunctor.map (homOfLE (Nat.le_succ n)).op = 𝟙 P := rfl
  have hs (n : ℕ) : CochainComplex.PrincipalCone.step μ n ≫ (a n).hom =
      (a (n + 1)).hom ≫ WeilConjectures.integralOperationsTowerStep T n := by
    apply (cancel_epi (RowEvalCone.coneIso f (op (n + 1))).hom).mp
    apply (cancel_mono (RowEvalCone.coneIso f (op n)).hom).mp
    have hnat := (RowEvalCone.natural f (homOfLE (Nat.le_succ n)).op).symm
    change (RowEvalCone.coneIso f (op (n + 1))).hom ≫
      CochainComplex.mappingCone.map (μ ^ (n + 1 + 1)) (μ ^ (n + 1))
        (N.asFunctor.map (homOfLE (Nat.le_succ n)).op) (𝟙 P) _ = _ at hnat
    simp only [hN] at hnat
    simpa only [a, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp,
      CochainComplex.PrincipalCone.step, WeilConjectures.integralOperationsTowerStep] using hnat
  have hu (n : ℕ) : CochainComplex.mappingCone.inr (μ ^ (n + 1)) ≫
      (a n).hom = γ.app (op n) := by
    apply (cancel_mono (RowEvalCone.coneIso f (op n)).hom).mp
    simp only [a, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      γ, ε, NatTrans.comp_app]
    erw [Category.id_comp]
    exact (CochainComplex.mappingCone.map_inr f
      ((evaluation ℕᵒᵖ B).obj (op n))).symm
  obtain ⟨c, hc⟩ := normalizedConeComparison μ T γ a hs hu
  have hi : IsIso (DerivedCategory.Q.map (normalizedCoconeLift _
      (Pi.lift (fun n ↦ γ.app (op n))) (towerAugmentationCondition T γ))) := by
    change IsIso (DerivedCategory.Q.map (roosAugment (fun n ↦ γ.app (op n)) hγ))
    infer_instance
  have hiso : IsIso (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ)) := by
    have hciso : IsIso (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫
        c.hom) := by rw [hc]; exact hi
    exact IsIso.of_isIso_comp_right
      (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ)) c.hom
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).mp hiso

end CategoryTheory.RingedPowerTorsion
