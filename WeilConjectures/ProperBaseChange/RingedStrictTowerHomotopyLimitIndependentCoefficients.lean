/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Total derived inverse limits with independent site and coefficient universes

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941; More on Algebra,
Tag 0H9L (blueprint: lem-weil-pbc-ringed-strict-tower-homotopy-limit).

This companion retains the original interface through its public import. Its generalized
statement applies to the small pro-etale site and the actual completed coefficient sheaf.
-/

@[expose] public section

set_option autoImplicit false

universe w uC vC r u v u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped BigOperators

namespace CategoryTheory

private lemma tower_grothendieck
    (A : Type uC) [Category.{vC} A] [Abelian A] [IsGrothendieckAbelian.{r} A] :
    IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

private theorem injective_tower_transition_split
    {A : Type*} [Category A] [Abelian A]
    (T : ℕᵒᵖ ⥤ A) [Injective T]
    (n : ℕ) : IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op) := by
  classical
  let k := (homOfLE (Nat.le_succ n)).op
  let M := T.obj (op n)
  let L := (evaluationLeftAdjoint A (op n)).obj M
  let L' := (evaluationLeftAdjoint A (op (n + 1))).obj M
  let i : L ⟶ L' :=
    { app := fun m ↦ Sigma.desc fun g ↦ Sigma.ι (fun _ ↦ M) (k ≫ g)
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, L', evaluationLeftAdjoint, Category.assoc] }
  have (m : ℕᵒᵖ) : Mono (i.app m) := by
    let r : L'.obj m ⟶ L.obj m := Sigma.desc fun _ ↦
      if h : Nonempty (op n ⟶ m) then Sigma.ι (fun _ ↦ M) h.some else 0
    have hr : i.app m ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro g
      simp only [i, r, colimit.ι_desc_assoc, Cofan.mk_ι_app,
        dif_pos (show Nonempty (op n ⟶ m) from ⟨g⟩), colimit.ι_desc]
      exact (congrArg (Sigma.ι (fun _ : op n ⟶ m ↦ M))
        (Subsingleton.elim _ g)).trans (Category.comp_id _).symm
    exact (IsSplitMono.mk' ⟨r, hr⟩).mono
  have : Mono i := NatTrans.mono_of_mono_app i
  let a : L ⟶ T :=
    { app := fun m ↦ Sigma.desc fun g ↦ T.map g
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, evaluationLeftAdjoint, Functor.map_comp] }
  let b := Injective.factorThru a i
  have hb : i ≫ b = a := Injective.comp_factorThru a i
  refine IsSplitEpi.mk' ⟨Sigma.ι (fun _ ↦ M) (𝟙 (op (n + 1))) ≫
    b.app (op (n + 1)), ?_⟩
  rw [Category.assoc, ← b.naturality k, ← Category.assoc]
  have hn := congrArg (fun f : L ⟶ T ↦
    Sigma.ι (fun _ ↦ M) (𝟙 (op n)) ≫ f.app (op n)) hb
  simpa [L', evaluationLeftAdjoint, i, a] using hn


private theorem tower_compatibility
    {B : Type*} [Category* B] (F : ℕᵒᵖ ⥤ B) {Z : B}
    (a : ∀ n : ℕ, Z ⟶ F.obj (Opposite.op n))
    (ha : ∀ n, a (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = a n)
    {n m : ℕ} (h : n ≤ m) : a m ≫ F.map (homOfLE h).op = a n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    have he : (homOfLE (Nat.le_trans h (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, F.map_comp, ← Category.assoc, ha, ih]

private theorem tower_kernel
    {B : Type*} [Category* B] [Preadditive B]
    (F : ℕᵒᵖ ⥤ B) (c : Cone F) (hc : IsLimit c)
    (P : Fan (fun n : ℕ ↦ F.obj (Opposite.op n))) (hP : IsLimit P)
    (i : c.pt ⟶ P.pt) (t : P.pt ⟶ P.pt)
    (hi : ∀ n : ℕ, i ≫ P.proj n = c.π.app (Opposite.op n))
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj n -
      P.proj (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) :
    ∃ h : i ≫ t = 0, Nonempty (IsLimit (KernelFork.ofι i h)) := by
  have hz : i ≫ t = 0 := by
    apply hP.hom_ext
    intro ⟨n⟩
    change (i ≫ t) ≫ P.proj n = 0 ≫ P.proj n
    rw [Category.assoc, ht, Preadditive.comp_sub, hi, ← Category.assoc, hi]
    simp only [zero_comp, sub_eq_zero]
    exact (c.w (homOfLE (Nat.le_succ n)).op).symm
  refine ⟨hz, ⟨Fork.IsLimit.mk' _ ?_⟩⟩
  intro s
  let Z := s.pt
  let k := s.ι
  have hk : k ≫ t = 0 := by
    have h := s.condition
    simp only [comp_zero] at h
    exact h
  have ha (n : ℕ) : (k ≫ P.proj (n + 1)) ≫
      F.map (homOfLE (Nat.le_succ n)).op = k ≫ P.proj n := by
    have hn := congrArg (fun f ↦ f ≫ P.proj n) hk
    rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, zero_comp] at hn
    exact (sub_eq_zero.mp hn).symm
  let d : Cone F :=
    { pt := Z
      π := { app := fun n ↦ k ≫ P.proj n.unop
             naturality := by
               intro n m f
               change 𝟙 Z ≫ (k ≫ P.proj m.unop) =
                 (k ≫ P.proj n.unop) ≫ F.map f
               rw [Category.id_comp]
               symm
               exact tower_compatibility F (fun n ↦ k ≫ P.proj n) ha
                 (leOfHom f.unop) } }
  refine ⟨hc.lift d, ?_, ?_⟩
  · apply hP.hom_ext
    intro ⟨n⟩
    change (hc.lift d ≫ i) ≫ P.proj n = k ≫ P.proj n
    rw [Category.assoc, hi]
    exact hc.fac d (Opposite.op n)
  · intro l hl
    apply hc.hom_ext
    intro n
    change l ≫ i = k at hl
    calc
      l ≫ c.π.app n = k ≫ P.proj n.unop := by
        rw [← hi n.unop, ← Category.assoc, hl]
      _ = hc.lift d ≫ c.π.app n := (hc.fac d n).symm


private theorem fan_shift_splitEpi
    {A : Type u} [Category.{v} A] [Preadditive A]
    (K : ℕ → A) (P : Fan K) (hP : IsLimit P) (q : ∀ n, K (n + 1) ⟶ K n)
    [∀ n, IsSplitEpi (q n)] (t : P.pt ⟶ P.pt)
    (ht : ∀ n, t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫ q n) : IsSplitEpi t := by
  let a : ∀ n : ℕ, P.pt ⟶ K n := fun n ↦ Nat.rec 0
    (fun n a ↦ (a - P.proj n) ≫ section_ (q n)) n
  have ha (n : ℕ) : a (n + 1) ≫ q n = a n - P.proj n := by
    change ((a n - P.proj n) ≫ section_ (q n)) ≫ q n = _
    rw [Category.assoc, IsSplitEpi.id, Category.comp_id]
  let r := hP.lift (Fan.mk P.pt a)
  have hr (n) : r ≫ P.proj n = a n := hP.fac _ ⟨n⟩
  refine IsSplitEpi.mk' ⟨r, ?_⟩
  apply Fan.IsLimit.hom_ext hP
  intro n
  rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, hr, hr, ha]
  simp

private theorem complexRoos_shortExact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [∀ p, Injective (I.X p)] :
    let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)
    let p : L.obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
      Pi.lift (fun n : ℕ ↦ (NatTrans.mapHomologicalComplex
        (lim.π (op n)) (ComplexShape.up ℤ)).app I)
    let t := towerTransitionEndomorphism
      (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
    ∃ h : p ≫ t = 0, (ShortComplex.mk p t h).ShortExact := by
  intro L p t
  let c : Cone I.asFunctor :=
    { pt := L.obj I
      π := { app := fun n ↦ (NatTrans.mapHomologicalComplex
                (lim.π n) (ComplexShape.up ℤ)).app I
             naturality := by
               intro n m f
               ext r
               change 𝟙 _ ≫ limit.π (I.X r) m =
                 limit.π (I.X r) n ≫ (I.X r).map f
               rw [Category.id_comp]
               exact (limit.w _ _).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro r
    exact limit.isLimit (I.X r)
  let K := fun n : ℕ ↦ I.asFunctor.obj (op n)
  let P : Fan K := limit.cone (Discrete.functor K)
  have ht (n) : t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫
      I.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
    change t ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ _
    simp [t, K, towerTransitionEndomorphism, towerProductShift]
  obtain ⟨h, ⟨hk⟩⟩ := tower_kernel I.asFunctor c hc P
    (limit.isLimit _) p t (fun n ↦ Pi.lift_π _ n) ht
  refine ⟨h, HomologicalComplex.shortExact_of_degreewise_shortExact _ ?_⟩
  intro r
  let ev := HomologicalComplex.eval A (ComplexShape.up ℤ) r
  have hkr := KernelFork.mapIsLimit _ hk ev
  have hPr : IsLimit (Fan.mk (P.pt.X r) (fun n ↦ (P.proj n).f r)) :=
    (Fan.isLimitMapConeEquiv ev K P) (isLimitOfPreserves ev (limit.isLimit _))
  have (n : ℕ) : IsSplitEpi ((I.X r).map (homOfLE (Nat.le_succ n)).op) :=
    injective_tower_transition_split (I.X r) n
  have htr : IsSplitEpi (t.f r) := fan_shift_splitEpi
    (fun n : ℕ ↦ (I.X r).obj (op n)) _ hPr
    (fun n : ℕ ↦ (I.X r).map (homOfLE (Nat.le_succ n)).op) (t.f r)
    (fun n ↦ congrArg (fun f ↦ f.f r) (ht n))
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hkr)
    (mono_of_isLimit_fork hkr) htr.epi


namespace CoreWork
universe g
set_option backward.isDefEq.respectTransparency false
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]

@[reducible] private noncomputable def L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)

@[reducible] private noncomputable def P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj I := ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n))
  map f := Limits.Pi.map (fun n : ℕ ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))
  map_id I := by
    apply Pi.hom_ext
    intro n
    simp only [Limits.Pi.map_π, Category.id_comp]
    exact Category.comp_id _
  map_comp f g := by simp [Limits.Pi.map_comp_map]

private lemma inc_diff (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    inc.app I ≫ diff.app I = 0 := by
  change (Pi.lift (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)) ≫
    towerTransitionEndomorphism _ = 0
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Category.assoc,
    Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
    Pi.lift_π, Pi.lift_π_assoc, zero_comp, sub_eq_zero]
  ext r
  exact (limit.w (I.X r) (homOfLE (Nat.le_succ n)).op).symm

@[reducible] private noncomputable def S (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ShortComplex (CochainComplex A ℤ) := ShortComplex.mk (inc.app I) (diff.app I) (inc_diff I)

private lemma hS (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [∀ r, Injective (I.X r)] :
    (S I).ShortExact := by
  obtain ⟨h, hs⟩ := complexRoos_shortExact I
  exact hs

@[reducible] private noncomputable def Smap {I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : I ⟶ J) : S I ⟶ S J :=
  { τ₁ := L.map f
    τ₂ := P.map f
    τ₃ := P.map f
    comm₁₂ := inc.naturality f
    comm₂₃ := diff.naturality f }


variable [HasDerivedCategory.{w} A] [HasCountableProducts (DerivedCategory.{w} A)]

omit [HasLimitsOfShape ℕᵒᵖ A] in
omit [HasLimitsOfShape ℕᵒᵖ A] in
variable [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

private noncomputable abbrev F := CochainComplex.kInjectiveResolutionFunctor.{g} (ℕᵒᵖ ⥤ A)
private noncomputable abbrev q := CochainComplex.toKInjectiveResolution.{g} (ℕᵒᵖ ⥤ A)

@[reducible] private noncomputable def delta : F ⋙ P ⋙ DerivedCategory.Q ⟶
    F ⋙ L ⋙ DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory.{w} A) (1 : ℤ) where
  app X := DerivedCategory.triangleOfSESδ (hS (F.obj X))
  naturality X Y f := by
    exact (DerivedCategory.triangleOfSESδ_naturality (hS (F.obj X))
      (hS (F.obj Y)) (Smap (F.map f))).symm

omit [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A] [HasDerivedCategory.{w} A]
  [HasCountableProducts (DerivedCategory.{w} A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] in
omit [HasLimitsOfShape ℕᵒᵖ A] in
end CoreWork

end CategoryTheory
