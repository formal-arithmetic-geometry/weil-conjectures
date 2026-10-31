/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NilpotentKoszulGradedTower
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Mathlib.Algebra.Ring.GeomSum

/-! # Koszul completion at nilpotent generators

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/lemma-weil-pbc-adic-completion-reduction.proof.md,
proof sentences four through seven (order 1328).
(blueprint: lem-weil-pbc-nilpotent-koszul-completion-unit).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
namespace ProconstantRoos
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable (T : ℕᵒᵖ ⥤ A) (C : A)
  (u : (Functor.const ℕᵒᵖ).obj C ⟶ T)
  (v : T ⟶ (Functor.const ℕᵒᵖ).obj C)
  (huv : ∀ n : ℕ, u.app (op n) ≫ v.app (op n) = 𝟙 C)
  (a : ℕ) (hf : ∀ n : ℕ, T.map (homOfLE (Nat.le_add_right n a)).op =
    v.app (op (n + a)) ≫ u.app (op n))

include v huv a hf in
private noncomputable def isLimit : IsLimit (Cone.mk C u) := by
  refine ⟨fun s ↦ s.π.app (op 0) ≫ v.app (op 0), ?_, ?_⟩
  · intro s j
    obtain ⟨n⟩ := j
    have hsn := s.w (homOfLE (Nat.le_add_right n a)).op
    have hsv := s.w (homOfLE (Nat.zero_le (n + a))).op
    have hv := v.naturality (homOfLE (Nat.zero_le (n + a))).op
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map] at hv
    rw [Category.comp_id] at hv
    change (s.π.app (op 0) ≫ v.app (op 0)) ≫ u.app (op n) = s.π.app (op n)
    rw [← hsv]
    simp only [Category.assoc]
    rw [reassoc_of% hv, ← hf n, hsn]
  · intro s m hm
    have h := hm (op 0)
    change m ≫ u.app (op 0) = s.π.app (op 0) at h
    rw [← h, Category.assoc, huv, Category.comp_id]

variable [HasProduct (fun n : ℕ ↦ T.obj (op n))] [HasProduct (fun _ : ℕ ↦ C)]

include u v huv a hf in
private theorem epi : Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
    (fun n ↦ T.map (homOfLE n.le_succ).op)) := by
  let P := ∏ᶜ (fun n : ℕ ↦ T.obj (op n))
  let Q := ∏ᶜ (fun _ : ℕ ↦ C)
  let hP := productIsProduct (fun n : ℕ ↦ T.obj (op n))
  let hQ := productIsProduct (fun _ : ℕ ↦ C)
  let p : P ⟶ Q := Limits.Pi.map (fun n ↦ v.app (op n))
  let i : Q ⟶ P := Limits.Pi.map (fun n ↦ u.app (op n))
  let s : P ⟶ P := Pretriangulated.towerShift (F := T) hP
  let t : Q ⟶ Q := Pretriangulated.towerShift
    (F := (Functor.const ℕᵒᵖ).obj C) hQ
  have hs (n : ℕ) : s ≫ Limits.Pi.π _ n =
      Limits.Pi.π _ (n + 1) ≫ T.map (homOfLE n.le_succ).op :=
    Pretriangulated.towerShift_proj hP n
  have ht (n : ℕ) : t ≫ Limits.Pi.π _ n = Limits.Pi.π _ (n + 1) := by
    have h := Pretriangulated.towerShift_proj (F := (Functor.const ℕᵒᵖ).obj C) hQ n
    change t ≫ Limits.Pi.π _ n = Limits.Pi.π _ (n + 1) ≫ 𝟙 C at h
    simpa only [Category.comp_id] using h
  have hip : i ≫ p = 𝟙 Q := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [i, p, Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc, huv,
      Category.comp_id, Category.id_comp]
  have hsi : t ≫ i = i ≫ s := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, i, Limits.Pi.map_π]
    rw [← Category.assoc, ht, hs]
    simp only [Limits.Pi.map_π_assoc]
    have hu := u.naturality (homOfLE n.le_succ).op
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map] at hu
    rw [Category.id_comp] at hu
    simpa only [Category.assoc] using
      congrArg (fun k ↦ Limits.Pi.π (fun _ : ℕ ↦ C) (n + 1) ≫ k) hu
  have hsp : s ≫ p = p ≫ t := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, p, Limits.Pi.map_π]
    rw [← Category.assoc, hs, ht]
    simp only [Limits.Pi.map_π, Category.assoc]
    have hv := v.naturality (homOfLE n.le_succ).op
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map] at hv
    rw [Category.comp_id] at hv
    simpa only [Category.assoc] using
      congrArg (fun k ↦ Limits.Pi.π (fun n : ℕ ↦ T.obj (op n)) (n + 1) ≫ k) hv
  have hpow : (End.of s ^ a) ≫ (𝟙 P - p ≫ i) = 0 := by
    apply Limits.Pi.hom_ext
    intro n
    have hp (k : ℕ) : (End.of s ^ a) ≫ Limits.Pi.π _ k =
        Limits.Pi.π _ (k + a) ≫ T.map (homOfLE (Nat.le_add_right k a)).op :=
      Pretriangulated.towerShift_pow_proj hP a k
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Category.assoc, zero_comp, p, i, Limits.Pi.map_π, Limits.Pi.map_π_assoc]
    rw [hp, hf]
    rw [reassoc_of% hp, hf]
    simp only [Category.assoc]
    rw [← Category.assoc (u.app (op n)), huv]
    simp only [Functor.const_obj_obj, Category.id_comp, sub_self]
  have hcomm : (𝟙 P - p ≫ i) ≫ (𝟙 P - s) =
      (𝟙 P - s) ≫ (𝟙 P - p ≫ i) := by
    have he : (p ≫ i) ≫ s = s ≫ (p ≫ i) := by
      rw [Category.assoc, ← hsi, ← Category.assoc, ← hsp, Category.assoc]
    simp only [Preadditive.comp_sub, Preadditive.sub_comp,
      Category.id_comp, Category.comp_id, he]
    abel
  obtain ⟨q, hq⟩ := Pretriangulated.exists_comp_sub_towerShift_eq_id hQ
  let g : P ⟶ P := (∑ k ∈ Finset.range a, End.of s ^ k)
  have hg : g ≫ (𝟙 P - s) = (1 - End.of s ^ a : End P) := by
    change (1 - End.of s) * (∑ k ∈ Finset.range a, End.of s ^ k) = 1 - End.of s ^ a
    exact mul_neg_geom_sum (End.of s) a
  have hq' : (q : Q ⟶ Q) ≫ (𝟙 Q - t) = 𝟙 Q := hq
  have hsec : (g ≫ (𝟙 P - p ≫ i) + p ≫ q ≫ i) ≫ (𝟙 P - s) = 𝟙 P := by
    rw [Preadditive.add_comp, Category.assoc, hcomm, ← Category.assoc, hg]
    rw [Preadditive.sub_comp, End.one_def, Category.id_comp, hpow, sub_zero]
    have hit : i ≫ (𝟙 P - s) = (𝟙 Q - t) ≫ i := by
      simp only [Preadditive.comp_sub, Preadditive.sub_comp,
        Category.comp_id, Category.id_comp, hsi]
    rw [Category.assoc, Category.assoc, hit, ← Category.assoc q, hq']
    change (𝟙 P - p ≫ i) + p ≫ 𝟙 Q ≫ i = 𝟙 P
    rw [Category.id_comp]
    abel
  have : Epi (𝟙 P - s) := epi_of_epi_fac hsec
  have hs' : s = towerProductShift (fun n ↦ T.map (homOfLE n.le_succ).op) :=
    (towerProductShift_eq_iff _ _).2 hs
  simpa only [towerTransitionEndomorphism, ← hs'] using this

include u v huv a hf in
private theorem epiOneSub {P : Fan fun n : ℕ ↦ T.obj (op n)} (hP : IsLimit P)
    (s : P.pt ⟶ P.pt)
    (hs : ∀ n : ℕ, s ≫ P.proj n = P.proj (n + 1) ≫
      T.map (homOfLE n.le_succ).op) : Epi (𝟙 P.pt - s) := by
  let e := hP.conePointUniqueUpToIso (productIsProduct (fun n : ℕ ↦ T.obj (op n)))
  let z := towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
    (fun n ↦ T.map (homOfLE n.le_succ).op)
  have he (n : ℕ) : e.hom ≫ Limits.Pi.π _ n = P.proj n :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk n)
  have hz : e.hom ≫ z = (𝟙 P.pt - s) ≫ e.hom := by
    apply Limits.Pi.hom_ext
    intro n
    dsimp only [z, towerTransitionEndomorphism, towerProductShift]
    simp only [Category.assoc, Preadditive.comp_sub,
      Limits.Pi.lift_π, Preadditive.sub_comp, Category.id_comp, he,
      reassoc_of% he, hs]
    change (e.hom ≫ 𝟙 _ ≫ _) - _ = _ - _
    rw [Category.id_comp, he]
  have := epi T C u v huv a hf
  have : Epi ((𝟙 P.pt - s) ≫ e.hom) := by rw [← hz]; infer_instance
  exact (epi_comp_iff_of_isIso _ e.hom).1 this

end ProconstantRoos
namespace ProconstantComplex
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
variable (D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (L : CochainComplex A ℤ)
  (w : (Functor.const ℕᵒᵖ).obj L ⟶ D)
  (β : ∀ p : ℤ, (D ⋙ HomologicalComplex.eval A (.up ℤ) p) ⟶
    (Functor.const ℕᵒᵖ).obj (L.X p))
  (hβ : ∀ n p, (w.app (op n)).f p ≫ (β p).app (op n) = 𝟙 (L.X p))
  (N : ℕ) (hN : ∀ n p,
    (D.map (homOfLE (Nat.le_add_right n N)).op).f p =
      (β p).app (op (n + N)) ≫ (w.app (op n)).f p)

private def wDegree (p : ℤ) : (Functor.const ℕᵒᵖ).obj (L.X p) ⟶
    D ⋙ HomologicalComplex.eval A (.up ℤ) p where
  app n := (w.app n).f p
  naturality i j f := by
    have h := congrArg (fun z ↦ z.f p) (w.naturality f)
    exact h

include β hβ N hN in
private noncomputable def complexIsLimit : IsLimit (Cone.mk L w) := by
  apply HomologicalComplex.isLimitOfEval
  intro p
  exact ProconstantRoos.isLimit _ (L.X p) (wDegree D L w p) (β p) (fun n ↦ hβ n p) N
    (fun n ↦ hN n p)

include β hβ N hN in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complexUnit_quasiIso
    (κ : L ⟶ (CochainComplex.mappingCone
      (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
        (fun n ↦ D.map (homOfLE n.le_succ).op)))⟦(-1 : ℤ)⟧)
    (hκ : ∀ p, κ.f p = (Limits.Pi.lift (fun n ↦ w.app (op n))).f p ≫
      HomologicalComplex.homotopyCofiber.inlX
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
        (fun n ↦ D.map (homOfLE n.le_succ).op))
        p (p + (-1)) (by change p + (-1) + 1 = p; omega)) : QuasiIso κ := by
  let P := ∏ᶜ (fun n : ℕ ↦ D.obj (op n))
  let hP := productIsProduct (fun n : ℕ ↦ D.obj (op n))
  let s : P ⟶ P := towerProductShift (K := fun n : ℕ ↦ D.obj (op n))
    (fun n ↦ D.map (homOfLE n.le_succ).op)
  let z : P ⟶ P := 𝟙 P - s
  have hs (n : ℕ) : s ≫ Limits.Pi.π _ n =
      Limits.Pi.π _ (n + 1) ≫ D.map (homOfLE n.le_succ).op := by
    exact Limits.Pi.lift_π _ _
  have hz (p : ℤ) : Epi (z.f p) := by
    let E := HomologicalComplex.eval A (.up ℤ) p
    let hPP := isLimitOfHasProductOfPreservesLimit E (fun n : ℕ ↦ D.obj (op n))
    have hs' (n : ℕ) : s.f p ≫ (Limits.Pi.π (fun n : ℕ ↦ D.obj (op n)) n).f p =
        (Limits.Pi.π (fun n : ℕ ↦ D.obj (op n)) (n + 1)).f p ≫ (D.map (homOfLE n.le_succ).op).f p :=
      congrArg (fun z ↦ z.f p) (hs n)
    exact ProconstantRoos.epiOneSub _ (L.X p) (wDegree D L w p) (β p) (fun n ↦ hβ n p) N
      (fun n ↦ hN n p) hPP (s.f p) hs'
  let hc := complexIsLimit D L w β hβ N hN
  let hk := Fan.IsLimit.isLimitKernelForkOneSub hP s hs hc
  let e := hk.conePointUniqueUpToIso (kernelIsKernel z)
  have he' := IsLimit.conePointUniqueUpToIso_hom_comp hk (kernelIsKernel z)
    WalkingParallelPair.zero
  have he : e.hom ≫ kernel.ι z = Limits.Pi.lift (fun n ↦ w.app (op n)) := by
    change e.hom ≫ kernel.ι z = Fan.IsLimit.lift hP _ at he'
    refine he'.trans ?_
    apply Limits.Pi.hom_ext
    intro n
    rw [Limits.Pi.lift_π]
    exact Fan.IsLimit.fac hP _ n
  have hcomp : κ = e.hom ≫ CochainComplex.comparison z := by
    ext p
    rw [hκ]
    change _ = e.hom.f p ≫ (kernel.ι z).f p ≫ _
    rw [← Category.assoc, ← HomologicalComplex.comp_f, he]
    rfl
  rw [hcomp]
  have := CochainComplex.comparison_quasiIso z hz
  infer_instance
end ProconstantComplex

universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Koszul completion at a finite list of uniformly nilpotent scalars is the identity.
The input complex may be unbounded and need not be K-flat.

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/lemma-weil-pbc-adic-completion-reduction.proof.md,
proof sentences four through seven (order 1328).
(blueprint: lem-weil-pbc-nilpotent-koszul-completion-unit).

Proof: use the graded split-proconstant calculation: the tensor unit has graded
retractions compatible with transitions, and every a-step transition factors through
them. In each degree the constant cone is a limit cone. On the product, split off the
constant part. On its complement the shift has a-th power zero, so the finite geometric
sum inverts one minus shift. On the constant part finite partial sums provide a section.
Thus one minus shift is degreewise epic, and its kernel is exactly C via the tensor
units. The kernel-to-shifted-cone comparison is a quasi-isomorphism. Its components are
precisely the specified koszulCompletionUnitComplex, so localization is an isomorphism.
This argument works in all degrees simultaneously and needs neither boundedness of C
nor removal of a finite prefix. -/
theorem nilpotentKoszulCompletionUnit_isIso (X : Scheme.{t}) (B : Type t) [CommRing B]
    (r : ℕ) (b : Fin r → B) (a : ℕ) (ha : 0 < a) (hb : ∀ j, b j ^ a = 0)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :
    IsIso ((adicLocalization X B).map (koszulCompletionUnitComplex X B r b C)) := by
  let := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  let T := Functor.ofOpSequence (koszulTensorTransition X B r b C)
  let w : (Functor.const ℕᵒᵖ).obj C ⟶ T :=
    NatTrans.ofOpSequence (koszulTensorUnit X B r b C) (fun n ↦ by
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
      rw [Category.id_comp]
      dsimp only [T]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (koszulTensorUnit_transition X B r b C n).symm)
  obtain ⟨β, hβ, hN⟩ := nilpotentKoszulGradedTower X B r b a ha hb C
  have hT : (fun n ↦ T.map (homOfLE n.le_succ).op) =
      koszulTensorTransition X B r b C := by
    funext n
    exact Functor.ofOpSequence_map_homOfLE_succ _ n
  have hz : towerTransitionEndomorphism (K := koszulTensor X B r b C)
      (fun n ↦ T.map (homOfLE n.le_succ).op) = koszulOneSubShift X B r b C := by
    rw [hT]
    rfl
  have q := ProconstantComplex.complexUnit_quasiIso T C w β hβ a hN
  rw [hz] at q
  have hi : QuasiIso (koszulCompletionUnitComplex X B r b C) :=
    q (koszulCompletionUnitComplex X B r b C) (fun p ↦ rfl)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hi

end AlgebraicGeometry.Scheme
