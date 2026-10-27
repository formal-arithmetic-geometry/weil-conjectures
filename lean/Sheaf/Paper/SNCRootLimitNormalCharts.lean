/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.RingTheory.RegularRingNormal
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Etale.Weakly
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.WeaklyEtaleNormalRing
import Sheaf.RingTheory.FlatRootTowerNonzerodivisor
import Sheaf.AlgebraicGeometry.SNCFiniteRootRegularRing
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.CategoryTheory.Category.ULift

/-! # Normal charts on the full SNC parameter-root limit

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, printed p.133;
Bhatt--Scholze, Theorem 2.3.4; Stacks Tags 097Z, 033C, 037D, 033G.
(blueprint: lem-sfb-snc-root-limit-normal-charts).

The existing `tameRootAlgebra` presents the displayed colimit by adjoining every root
and imposing precisely the divisibility transition equations. No root choice is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private abbrev RootStage {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) := Algebra.pthRootAlgebra n r R t

private theorem rootStage_rel {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) :
    (Ideal.Quotient.mk _ (MvPolynomial.X i) : RootStage t n) ^ n =
      algebraMap R (RootStage t n) (t i) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _ (MvPolynomial.X i ^ n - MvPolynomial.C (t i)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

private def rootStageLift {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) {T : Type w} [CommRing T]
    (f : R →+* T) (x : Fin r → T) (hx : ∀ i, x i ^ n = f (t i)) :
    RootStage t n →+* T :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f x) (by
    change Ideal.span _ ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.eval₂Hom f x _ = 0
    simp [hx])

private theorem rootStageLift_coeff {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) {T : Type w} [CommRing T]
    (f : R →+* T) (x : Fin r → T) (hx : ∀ i, x i ^ n = f (t i)) (c : R) :
    rootStageLift t n f x hx (algebraMap R (RootStage t n) c) = f c := by
  change MvPolynomial.eval₂Hom f x (MvPolynomial.C c) = f c
  simp

private theorem rootStageLift_root {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) {T : Type w} [CommRing T]
    (f : R →+* T) (x : Fin r → T) (hx : ∀ i, x i ^ n = f (t i)) (i : Fin r) :
    rootStageLift t n f x hx (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i := by
  change MvPolynomial.eval₂Hom f x (MvPolynomial.X i) = x i
  simp

private theorem rootStage_ext {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) {T : Type w} [CommRing T]
    (f g : RootStage t n →+* T)
    (hc : ∀ c, f (algebraMap R (RootStage t n) c) =
      g (algebraMap R (RootStage t n) c))
    (hx : ∀ i, f (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      g (Ideal.Quotient.mk _ (MvPolynomial.X i))) : f = g := by
  apply RingHom.ext
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  have h : f.comp (Ideal.Quotient.mk _) = g.comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact hc c
    · exact hx
  exact RingHom.congr_fun h z

private def fullRoot {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) (i : Fin r) (n : TameRootOrder p) : tameRootAlgebra p t :=
  Ideal.Quotient.mk _ (MvPolynomial.X (i, n))

private theorem fullRoot_rel {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) (i : Fin r) (n : TameRootOrder p) :
    fullRoot p t i n ^ n.val = algebraMap R (tameRootAlgebra p t) (t i) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _
    (MvPolynomial.X (i, n) ^ n.val - MvPolynomial.C (t i)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inl ⟨i, n, rfl⟩))

private theorem fullRoot_transition {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) (i : Fin r) (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    fullRoot p t i m ^ (m.val / n.val) = fullRoot p t i n := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _
    (MvPolynomial.X (i, m) ^ (m.val / n.val) - MvPolynomial.X (i, n)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inr ⟨i, n, m, h, rfl⟩))

private def fullRootLift {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) {T : Type w} [CommRing T]
    (f : R →+* T) (x : Fin r → TameRootOrder p → T)
    (hx : ∀ i n, x i n ^ n.val = f (t i))
    (hc : ∀ i n m, n.val ∣ m.val → x i m ^ (m.val / n.val) = x i n) :
    tameRootAlgebra p t →+* T :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f (fun a ↦ x a.1 a.2)) (by
    change Ideal.span _ ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    rintro _ (⟨i, n, rfl⟩ | ⟨i, n, m, h, rfl⟩)
    · change MvPolynomial.eval₂Hom f _ _ = 0
      simp [hx]
    · change MvPolynomial.eval₂Hom f _ _ = 0
      simp [hc i n m h])

private theorem fullRootLift_coeff {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) {T : Type w} [CommRing T]
    (f : R →+* T) (x : Fin r → TameRootOrder p → T)
    (hx : ∀ i n, x i n ^ n.val = f (t i))
    (hc : ∀ i n m, n.val ∣ m.val → x i m ^ (m.val / n.val) = x i n) (c : R) :
    fullRootLift p t f x hx hc (algebraMap R (tameRootAlgebra p t) c) = f c := by
  change MvPolynomial.eval₂Hom f _ (MvPolynomial.C c) = f c
  simp

private theorem fullRootLift_root {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) {T : Type w} [CommRing T]
    (f : R →+* T) (x : Fin r → TameRootOrder p → T)
    (hx : ∀ i n, x i n ^ n.val = f (t i))
    (hc : ∀ i n m, n.val ∣ m.val → x i m ^ (m.val / n.val) = x i n)
    (i : Fin r) (n : TameRootOrder p) :
    fullRootLift p t f x hx hc (fullRoot p t i n) = x i n := by
  change MvPolynomial.eval₂Hom f _ (MvPolynomial.X (i, n)) = x i n
  simp

private theorem fullRoot_ext {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) {T : Type w} [CommRing T]
    (f g : tameRootAlgebra p t →+* T)
    (hc : ∀ c, f (algebraMap R (tameRootAlgebra p t) c) =
      g (algebraMap R (tameRootAlgebra p t) c))
    (hx : ∀ i n, f (fullRoot p t i n) = g (fullRoot p t i n)) : f = g := by
  apply RingHom.ext
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  have h : f.comp (Ideal.Quotient.mk _) = g.comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact hc c
    · rintro ⟨i, n⟩
      exact hx i n
  exact RingHom.congr_fun h z

private def tameOrders (p : ℕ) : Set ℕ+ := {n | (n : ℕ).Coprime p}

private def towerOrder (p : ℕ) (n : Algebra.RootTowerIndex (tameOrders p)) :
    TameRootOrder p := ⟨n.1, n.1.2, n.2⟩

private def orderIndex (p : ℕ) (n : TameRootOrder p) :
    Algebra.RootTowerIndex (tameOrders p) := ⟨⟨n.val, n.property.1⟩, n.property.2⟩

private theorem transition_coeff {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ)) (c : R) :
    Algebra.simultaneousRootTransition t h
      (algebraMap R (RootStage t n) c) = algebraMap R (RootStage t m) c :=
  (Algebra.simultaneousRootTransition t h).commutes c

private theorem transition_root {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ)) (i : Fin r) :
    Algebra.simultaneousRootTransition t h (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      (Ideal.Quotient.mk _ (MvPolynomial.X i) : RootStage t m) ^
        ((m : ℕ) / (n : ℕ)) := by
  simp [Algebra.simultaneousRootTransition, Algebra.simultaneousRootEval,
    Algebra.simultaneousRoot, Algebra.simultaneousRootQuotient]

private def stageInclusion {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) (n : TameRootOrder p) :
    RootStage t n.val →+* tameRootAlgebra p t :=
  rootStageLift t n.val (algebraMap R _) (fun i ↦ fullRoot p t i n)
    (fun i ↦ fullRoot_rel p t i n)

private def rootCocone {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) : Cocone (Algebra.simultaneousRootDiagram t (tameOrders p)) where
  pt := .of (tameRootAlgebra p t)
  ι :=
    { app := fun n ↦ CommRingCat.ofHom (stageInclusion p t (towerOrder p n))
      naturality := by
        intro n m h
        apply CommRingCat.hom_ext
        apply rootStage_ext t (n.1 : ℕ)
        · intro c
          change stageInclusion p t (towerOrder p m)
            (Algebra.simultaneousRootTransition t (leOfHom h)
              (algebraMap R _ c)) = stageInclusion p t (towerOrder p n)
                (algebraMap R _ c)
          rw [transition_coeff]
          exact (rootStageLift_coeff _ _ _ _ _ c).trans
            (rootStageLift_coeff _ _ _ _ _ c).symm
        · intro i
          change stageInclusion p t (towerOrder p m)
            (Algebra.simultaneousRootTransition t (leOfHom h)
              (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
                stageInclusion p t (towerOrder p n) (Ideal.Quotient.mk _ (MvPolynomial.X i))
          rw [transition_root, map_pow]
          exact (congrArg (fun z : tameRootAlgebra p t ↦
            z ^ ((m.1 : ℕ) / (n.1 : ℕ)))
              (rootStageLift_root t (towerOrder p m).val (algebraMap R _)
                (fun i ↦ fullRoot p t i (towerOrder p m))
                (fun i ↦ fullRoot_rel p t i (towerOrder p m)) i)).trans
            ((fullRoot_transition p t i (towerOrder p n) (towerOrder p m) (leOfHom h)).trans
              (rootStageLift_root t (towerOrder p n).val (algebraMap R _)
                (fun i ↦ fullRoot p t i (towerOrder p n))
                (fun i ↦ fullRoot_rel p t i (towerOrder p n)) i).symm) }

set_option backward.isDefEq.respectTransparency false in
private def rootCocone_isColimit {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R) : IsColimit (rootCocone p t) := by
  let D := Algebra.simultaneousRootDiagram t (tameOrders p)
  let one : Algebra.RootTowerIndex (tameOrders p) := ⟨1, Nat.coprime_one_left p⟩
  let coeff (c : Cocone D) : R →+* c.pt :=
    (c.ι.app one).hom.comp (algebraMap R (RootStage t 1))
  let roots (c : Cocone D) (i : Fin r) (n : TameRootOrder p) : c.pt :=
    (c.ι.app (orderIndex p n)).hom (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have hc (c : Cocone D) (n : Algebra.RootTowerIndex (tameOrders p)) (a : R) :
      (c.ι.app n).hom (algebraMap R (RootStage t n.1) a) = coeff c a := by
    let h : one ⟶ n := homOfLE (one_dvd (n.1 : ℕ))
    have hw : (c.ι.app n).hom.comp
        (Algebra.simultaneousRootTransition t (one_dvd (n.1 : ℕ))).toRingHom =
        (c.ι.app one).hom := congrArg CommRingCat.Hom.hom (c.w h)
    have hh := RingHom.congr_fun hw (algebraMap R (RootStage t 1) a)
    dsimp only [RingHom.comp_apply] at hh
    exact (congrArg (c.ι.app n).hom (transition_coeff t
      (n := 1) (m := n.1) (one_dvd _) a)).symm.trans hh
  have hr (c : Cocone D) (i : Fin r) (n : TameRootOrder p) :
      roots c i n ^ n.val = coeff c (t i) := by
    exact (map_pow (c.ι.app (orderIndex p n)).hom
      (Ideal.Quotient.mk _ (MvPolynomial.X i)) n.val).symm.trans
        ((congrArg (c.ι.app (orderIndex p n)).hom (rootStage_rel t n.val i)).trans
          (hc c (orderIndex p n) (t i)))
  have ht (c : Cocone D) (i : Fin r) (n m : TameRootOrder p) (h : n.val ∣ m.val) :
      roots c i m ^ (m.val / n.val) = roots c i n := by
    have hh := ConcreteCategory.congr_hom
      (c.w (homOfLE (show orderIndex p n ≤ orderIndex p m from h)))
        (Ideal.Quotient.mk _ (MvPolynomial.X i))
    change (c.ι.app (orderIndex p m)).hom
      (Algebra.simultaneousRootTransition t (n := (orderIndex p n).1)
        (m := (orderIndex p m).1) h (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
        roots c i n at hh
    rwa [transition_root, map_pow] at hh
  let desc (c : Cocone D) : tameRootAlgebra p t →+* c.pt :=
    fullRootLift p t (coeff c) (roots c) (hr c) (ht c)
  have fac (c : Cocone D) (n : Algebra.RootTowerIndex (tameOrders p)) :
      (rootCocone p t).ι.app n ≫ CommRingCat.ofHom (desc c) = c.ι.app n := by
    apply CommRingCat.hom_ext
    apply rootStage_ext t (n.1 : ℕ)
    · intro a
      change desc c (stageInclusion p t (towerOrder p n) (algebraMap R _ a)) = _
      simp only [stageInclusion, rootStageLift_coeff, desc, fullRootLift_coeff]
      exact (hc c n a).symm
    · intro i
      change desc c (stageInclusion p t (towerOrder p n)
        (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _
      simp only [stageInclusion, rootStageLift_root, desc, fullRootLift_root]
      rfl
  refine ⟨fun c ↦ CommRingCat.ofHom (desc c), fac, ?_⟩
  intro c m hm
  apply CommRingCat.hom_ext
  apply fullRoot_ext p t
  · intro a
    have hh := ConcreteCategory.congr_hom (hm one) (algebraMap R (RootStage t 1) a)
    change m.hom (stageInclusion p t (towerOrder p one) (algebraMap R _ a)) = _ at hh
    simp only [stageInclusion, rootStageLift_coeff] at hh
    change m.hom (algebraMap R (tameRootAlgebra p t) a) =
      desc c (algebraMap R (tameRootAlgebra p t) a)
    rw [show desc c (algebraMap R (tameRootAlgebra p t) a) = coeff c a from
      fullRootLift_coeff _ _ _ _ _ _ a]
    exact hh
  · intro i n
    have hh := ConcreteCategory.congr_hom (hm (orderIndex p n))
      (Ideal.Quotient.mk _ (MvPolynomial.X i))
    change m.hom (stageInclusion p t n (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _ at hh
    simp only [stageInclusion, rootStageLift_root] at hh
    change m.hom (fullRoot p t i n) = desc c (fullRoot p t i n)
    rw [show desc c (fullRoot p t i n) = roots c i n from
      fullRootLift_root _ _ _ _ _ _ i n]
    exact hh

private theorem radical_factor {A : Type u} [CommRing A] (c d : A)
    (hd : Function.Injective (fun x : A ↦ d * x))
    (h : (Ideal.span ({c * d} : Set A)).IsRadical) :
    (Ideal.span ({c} : Set A)).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro x hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hx
  have hy : (x * d) ^ 2 ∈ Ideal.span ({c * d} : Set A) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨a * d, ?_⟩
    calc
      (x * d) ^ 2 = x ^ 2 * d ^ 2 := mul_pow _ _ _
      _ = (c * a) * d ^ 2 := by rw [ha]
      _ = (c * d) * (a * d) := by ring
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
    ((Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mp h _ hy)
  apply Ideal.mem_span_singleton.mpr
  refine ⟨b, hd ?_⟩
  calc
    d * x = x * d := mul_comm _ _
    _ = (c * d) * b := hb
    _ = d * (c * b) := by ring

private theorem boundary_regular {A : Type u} [CommRing A] {r : ℕ}
    (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (.of A)).inv (∏ i, t i)})) :
    Function.Injective (fun z : A ↦ (∏ i, t i) * z) ∧
      (Ideal.span ({∏ i, t i} : Set A)).IsRadical := by
  let e := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  have htop : H.ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e.symm (∏ i, t i)} := by
    rw [hproduct]
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
    change Ideal.map (RingHom.id _) _ = _
    rw [Ideal.map_id]
    rfl
  have hreg := hH.1.mem_nonZeroDivisors htop
  have hinj : Function.Injective (fun z : A ↦ (∏ i, t i) * z) := by
    intro z w h
    apply e.symm.injective
    apply (isRegular_iff_mem_nonZeroDivisors.mpr hreg).left
    simpa only [← map_mul] using congrArg e.symm h
  have hrad : (Ideal.span ({e.symm (∏ i, t i)} : Set Γ(Spec (.of A), ⊤))).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    rw [← htop]
    exact congrArg (fun J : (Spec (.of A)).IdealSheafData ↦
      J.ideal ⟨⊤, isAffineOpen_top _⟩) hH.2.1
  have he : (Ideal.span ({e.symm (∏ i, t i)} : Set Γ(Spec (.of A), ⊤))).comap
      e.symm.toRingHom = Ideal.span ({∏ i, t i} : Set A) := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e y, e.symm.injective (by simpa using hy)⟩
    · rintro ⟨y, hy⟩
      exact ⟨e.symm y, by change e.symm x = _; rw [← map_mul, hy]⟩
  exact ⟨hinj, he ▸ hrad.comap e.symm.toRingHom⟩

private theorem boundary_equations {A : Type u} [CommRing A] {r : ℕ}
    (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (.of A)).inv (∏ i, t i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A))))) :
    (∀ i : Fin r, _root_.IsReduced (A ⧸ Ideal.span ({t i} : Set A))) ∧
      Function.Injective (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) := by
  classical
  obtain ⟨hinj, hrad⟩ := boundary_regular t H hH hproduct
  have hfactor (i : Fin r) : ∃ d : A, (∏ j, t j) = t i * d := by
    exact ⟨∏ j ∈ Finset.univ.erase i, t j,
      (Finset.mul_prod_erase Finset.univ t (Finset.mem_univ i)).symm⟩
  have hri (i : Fin r) : (Ideal.span ({t i} : Set A)).IsRadical := by
    obtain ⟨d, hd⟩ := hfactor i
    have hdreg : Function.Injective (fun x : A ↦ d * x) := by
      intro x y h
      apply hinj
      simpa only [hd, mul_assoc] using congrArg (fun z ↦ t i * z) h
    exact radical_factor (t i) d hdreg (hd ▸ hrad)
  refine ⟨fun i ↦ (Ideal.isRadical_iff_quotient_reduced _).mp (hri i), ?_⟩
  intro i j hij
  by_contra hne
  have heq : Ideal.span ({t i} : Set A) = Ideal.span ({t j} : Set A) := by
    have hh := PrimeSpectrum.zeroLocus_eq_iff
      (I := Ideal.span ({t i} : Set A)) (J := Ideal.span ({t j} : Set A)) |>.mp
      (by simpa only [PrimeSpectrum.zeroLocus_span] using hij)
    simpa only [(hri i).radical, (hri j).radical] using hh
  have hdiv : t i ∣ t j := Ideal.mem_span_singleton.mp
    (heq ▸ Ideal.subset_span (Set.mem_singleton (t j)))
  obtain ⟨c, hc⟩ := hdiv
  let d := ∏ k ∈ (Finset.univ.erase i).erase j, t k
  have hprod : (∏ k, t k) = t i * t j * d := by
    rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) t
        (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩)]
    exact (mul_assoc _ _ _).symm
  let z := t i * c * d
  have hz : z ^ 2 ∈ Ideal.span ({∏ k, t k} : Set A) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨c * d, ?_⟩
    dsimp [z]
    rw [hprod, hc]
    ring
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
    ((Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mp hrad _ hz)
  have hzinj : Function.Injective (fun x : A ↦ z * x) := by
    intro x y h
    apply hinj
    have hh : (∏ k, t k) = t i * z := by dsimp [z]; rw [hprod, hc]; ring
    simpa only [hh, mul_assoc] using congrArg (fun z ↦ t i * z) h
  have hunit : IsUnit (t i) := by
    apply isUnit_of_dvd_one
    refine ⟨a, hzinj ?_⟩
    calc
      z * 1 = z := mul_one _
      _ = (∏ k, t k) * a := ha
      _ = z * (t i * a) := by dsimp [z]; rw [hprod, hc]; ring
  have hmem := hbranches ▸ Set.mem_range_self i
  obtain ⟨C, hC, hCi⟩ := hmem
  have hnonempty := hC.1.nonempty
  obtain ⟨x, hx⟩ := hnonempty
  have hx' : (x : Spec (.of A)) ∈ PrimeSpectrum.zeroLocus ({t i} : Set A) := by
    rw [← hCi]
    exact Set.mem_image_of_mem Subtype.val hx
  exact (show x.val.asIdeal ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance)
    (Ideal.eq_top_of_isUnit_mem _ (hx' (Set.mem_singleton (t i))) hunit)

private theorem stage_weaklyEtale {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] (a : A →+* R) (ha : a.WeaklyEtale)
    {r : ℕ} (t : Fin r → A) (n : ℕ) :
    (rootStageLift t n ((algebraMap R (RootStage (fun i ↦ a (t i)) n)).comp a)
      (fun i ↦ Ideal.Quotient.mk _ (MvPolynomial.X i))
      (fun i ↦ rootStage_rel (fun i ↦ a (t i)) n i)).WeaklyEtale := by
  let : Algebra A R := a.toAlgebra
  let : Algebra.WeaklyEtale A R := ha
  let B := RootStage t n
  let C := RootStage (fun i ↦ a (t i)) n
  let : Algebra A C := ((algebraMap R C).comp a).toAlgebra
  let f : B →+* C := rootStageLift t n ((algebraMap R C).comp a)
    (fun i ↦ Ideal.Quotient.mk _ (MvPolynomial.X i))
    (fun i ↦ rootStage_rel (fun i ↦ a (t i)) n i)
  let f' : B →ₐ[A] C := ⟨f, fun c ↦ rootStageLift_coeff _ _ _ _ _ c⟩
  let g : R →ₐ[A] C := ⟨algebraMap R C, fun _ ↦ rfl⟩
  let forward : TensorProduct A B R →ₐ[A] C :=
    Algebra.TensorProduct.productMap f' g
  let backwardMap : C →+* TensorProduct A B R :=
    rootStageLift (fun i ↦ a (t i)) n Algebra.TensorProduct.includeRight.toRingHom
      (fun i ↦ Algebra.TensorProduct.includeLeftRingHom
        (Ideal.Quotient.mk _ (MvPolynomial.X i) : B)) (by
      intro i
      rw [← map_pow, rootStage_rel]
      exact RingHom.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap _)
  have fl (b : B) : forward (Algebra.TensorProduct.includeLeftRingHom b) = f b :=
    AlgHom.congr_fun (Algebra.TensorProduct.productMap_left f' g) b
  have fr (c : R) : forward (Algebra.TensorProduct.includeRight c) = algebraMap R C c :=
    AlgHom.congr_fun (Algebra.TensorProduct.productMap_right f' g) c
  have hleft : backwardMap.comp forward.toRingHom = RingHom.id _ := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply rootStage_ext t n
      · intro c
        change backwardMap (forward (Algebra.TensorProduct.includeLeftRingHom
          (algebraMap A B c))) = Algebra.TensorProduct.includeLeftRingHom (algebraMap A B c)
        rw [fl]
        rw [show f (algebraMap A B c) = algebraMap R C (a c) from
          rootStageLift_coeff _ _ _ _ _ c]
        rw [show backwardMap (algebraMap R C (a c)) =
          Algebra.TensorProduct.includeRight (a c) from rootStageLift_coeff _ _ _ _ _ (a c)]
        exact (RingHom.congr_fun
          Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap c).symm
      · intro i
        change backwardMap (forward (Algebra.TensorProduct.includeLeftRingHom
          (Ideal.Quotient.mk _ (MvPolynomial.X i) : B))) = _
        rw [fl]
        rw [show f (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
          (Ideal.Quotient.mk _ (MvPolynomial.X i) : C) from
            rootStageLift_root _ _ _ _ _ i]
        exact rootStageLift_root _ _ _ _ _ i
    · ext c
      change backwardMap (forward (Algebra.TensorProduct.includeRight c)) =
        Algebra.TensorProduct.includeRight c
      rw [fr]
      exact rootStageLift_coeff _ _ _ _ _ c
  have hright : forward.toRingHom.comp backwardMap = RingHom.id C := by
    apply rootStage_ext (fun i ↦ a (t i)) n
    · intro c
      change forward (backwardMap (algebraMap R C c)) = algebraMap R C c
      rw [show backwardMap (algebraMap R C c) = Algebra.TensorProduct.includeRight c from
        rootStageLift_coeff _ _ _ _ _ c]
      exact fr c
    · intro i
      change forward (backwardMap (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _
      rw [show backwardMap (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
        Algebra.TensorProduct.includeLeftRingHom
          (Ideal.Quotient.mk _ (MvPolynomial.X i) : B) from
            rootStageLift_root _ _ _ _ _ i]
      rw [fl]
      exact rootStageLift_root _ _ _ _ _ i
  have hbij : Function.Bijective forward :=
    ⟨Function.LeftInverse.injective (fun x ↦ RingHom.congr_fun hleft x),
      Function.RightInverse.surjective (fun x ↦ RingHom.congr_fun hright x)⟩
  have he : forward.toRingHom.WeaklyEtale := by
    let : Algebra (TensorProduct A B R) C := forward.toRingHom.toAlgebra
    let : Algebra.Etale (TensorProduct A B R) C :=
      (RingHom.Etale.of_bijective hbij).toAlgebra
    exact inferInstanceAs (Algebra.WeaklyEtale (TensorProduct A B R) C)
  have hb : (Algebra.TensorProduct.includeLeftRingHom :
      B →+* TensorProduct A B R).WeaklyEtale :=
    (RingHom.weaklyEtale_algebraMap_iff).mpr inferInstance
  have hh := hb.comp he
  have hcomp : forward.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = f :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.productMap_left f' g)
  rwa [hcomp] at hh

private theorem normal_equiv {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    (hR : ∀ (q : Ideal R) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime e.toRingHom q
  obtain ⟨hd, hi⟩ := hR p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e' := Localization.localRingEquiv p q e rfl
  exact ⟨e'.symm.injective.isDomain e'.symm, IsIntegrallyClosed.of_equiv e'⟩

private theorem tameOrders_filtered (p : ℕ) :
    IsFiltered (Algebra.RootTowerIndex (tameOrders p)) := by
  let : Nonempty (Algebra.RootTowerIndex (tameOrders p)) :=
    ⟨⟨1, Nat.coprime_one_left p⟩⟩
  let : IsDirectedOrder (Algebra.RootTowerIndex (tameOrders p)) := ⟨by
    intro n m
    refine ⟨⟨n.1 * m.1, n.2.mul_left m.2⟩, ?_, ?_⟩
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _⟩
  infer_instance

private theorem fullRoot_normal {R : Type v} [CommRing R] {r : ℕ}
    (p : ℕ) (t : Fin r → R)
    (hn : ∀ n : TameRootOrder p, ∀ (q : Ideal (RootStage t n.val)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (q : Ideal (tameRootAlgebra p t)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let : IsFiltered (Algebra.RootTowerIndex (tameOrders p)) := tameOrders_filtered p
  let E : AsSmall.{v} (Algebra.RootTowerIndex (tameOrders p)) ≌
      Algebra.RootTowerIndex (tameOrders p) := AsSmall.equiv.symm
  let F : AsSmall.{v} (Algebra.RootTowerIndex (tameOrders p)) ⥤ CommRingCat.{v} :=
    E.functor ⋙ Algebra.simultaneousRootDiagram t (tameOrders p)
  let c : Cocone F := (rootCocone p t).whisker E.functor
  have hc : IsColimit c := (rootCocone_isColimit p t).whiskerEquivalence E
  let e := (colimit.isoColimitCocone ⟨c, hc⟩).commRingCatIsoToRingEquiv
  exact normal_equiv e (CommRingCat.isNormal_of_filtered_colimit F
    (fun n ↦ hn (towerOrder p (E.functor.obj n))))

private theorem fullRoot_regular {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] (a : A →+* R) (ha : a.Flat)
    {r : ℕ} (t : Fin r → A) (p : ℕ) (c : A)
    (hc : Function.Injective (fun x : A ↦ c * x))
    {Q : Type w} [CommRing Q] [Algebra (tameRootAlgebra p (fun i ↦ a (t i))) Q]
    (hq : (algebraMap (tameRootAlgebra p (fun i ↦ a (t i))) Q).Flat) :
    Function.Injective (fun x : Q ↦
      algebraMap (tameRootAlgebra p (fun i ↦ a (t i))) Q
        (algebraMap R (tameRootAlgebra p (fun i ↦ a (t i))) (a c)) * x) := by
  let tR := fun i ↦ a (t i)
  let D := Algebra.simultaneousRootDiagram tR (tameOrders p)
  let e := (colimit.isoColimitCocone
    ⟨rootCocone p tR, rootCocone_isColimit p tR⟩).commRingCatIsoToRingEquiv
  let q := (algebraMap (tameRootAlgebra p tR) Q).comp e.toRingHom
  have hq' : q.Flat := (RingHom.Flat.of_bijective e.bijective).comp hq
  have h1 : (1 : ℕ+) ∈ tameOrders p := Nat.coprime_one_left p
  have hf : ∀ n ∈ tameOrders p, ∀ m ∈ tameOrders p,
      ∃ k ∈ tameOrders p, (n : ℕ) ∣ (k : ℕ) ∧ (m : ℕ) ∣ (k : ℕ) := by
    intro n hn m hm
    exact ⟨n * m, hn.mul_left hm, dvd_mul_right _ _, dvd_mul_left _ _⟩
  have hh := (Algebra.flat_root_tower_nonzerodivisor
    A R a ha r t c hc (tameOrders p) h1 hf Q q hq').2.2.2.1
  have he : e (Algebra.simultaneousRootColimitMap tR (tameOrders p) h1 (a c)) =
      algebraMap R (tameRootAlgebra p tR) (a c) := by
    have he' := ConcreteCategory.congr_hom
      (colimit.isoColimitCocone_ι_hom
        ⟨rootCocone p tR, rootCocone_isColimit p tR⟩
        (⟨1, h1⟩ : Algebra.RootTowerIndex (tameOrders p)))
      (algebraMap R (RootStage tR 1) (a c))
    change e (Algebra.simultaneousRootColimitMap tR (tameOrders p) h1 (a c)) =
      stageInclusion p tR (towerOrder p ⟨1, h1⟩) (algebraMap R _ (a c)) at he'
    exact he'.trans (rootStageLift_coeff _ _ _ _ _ (a c))
  change Function.Injective (fun x : Q ↦
    algebraMap (tameRootAlgebra p tR) Q
      (e (Algebra.simultaneousRootColimitMap tR (tameOrders p) h1 (a c))) * x) at hh
  rwa [he] at hh

/-- Every weakly etale chart of the full simultaneous prime-forward-p parameter-root limit
is normal, and the image of the boundary product acts injectively on its ring.
Source: ILO IX, Proposition 2.1 proof, p.133; Bhatt--Scholze Theorem 2.3.4;
Stacks Tags 097Z, 033C, 037D, 033G.
(blueprint: lem-sfb-snc-root-limit-normal-charts).

Proof:
1. For each positive n prime forward p, the finite simultaneous root algebra A_n over A
   is regular Noetherian by `lem-sfb-snc-finite-root-regular-ring`: Bezout makes n
   invertible in A. The SNC empty intersection supplies regularity of the chart.
   `lem-weil-pbc-regular-ring-normal` gives normality of A_n.
2. The polynomial quotient universal property identifies A_n tensor_A R with R_n:
   the two inverse maps fix all coefficients and all roots. Thus A_n -> R_n is
   weakly etale by `lem-exc-weakly-etale-ring-base-change-composition`, using
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`.
3. `lem-weil-pbc-existing-weakly-etale-indetale-refinement` gives a faithfully flat
   refinement R_n -> T_n with A_n -> T_n ind-etale. Its finite-presentation etale
   stages are normal by `lem-weil-pbc-etale-over-normal-ring-normal`; apply
   `lem-weil-pbc-filtered-colimit-normal-ring` and then
   `lem-sfb-faithfully-flat-normal-ring-descent` forward obtain normality of R_n.
4. The positive orders prime forward p are directed by divisibility (use the product
   as upper bound). Their prescribed power maps respect the equations and compose.
   The quotient presentation `tameRootAlgebra` is their colimit. Apply
   `lem-weil-pbc-filtered-colimit-normal-ring` forward obtain normality of S.
5. Apply the same ind-etale refinement, etale normality, filtered-colimit normality,
   and faithfully flat descent forward S -> Q. This gives the asserted prime-local form.
6. Each maximal localization of A is a domain by `lem-sc-regular-local-domain`.
   A branch equation cannot vanish there: its generic prime would lie on that
   branch with local dimension zero, contradicting the SNC codimension-one clause.
   Thus t_d y = 0 implies y vanishes at every maximal localization, and hence y = 0
   by `lem-weil-pbc-ideal-membership-at-maximal-localizations`. Composing gives
   injectivity of multiplication by the product on A.
7. Flatness of A -> R preserves this injection. Each R_n is free over R on monomials
   with each exponent less than n, by `lem-weil-pbc-monic-quotient-free`; uniqueness
   of coefficients therefore gives injectivity of multiplication by the product.
8. Represent a kernel element at a finite stage and its zero equality at a common
   later stage by `lem-pc-filtered-colimit-commrings-elementwise`. Step 7 kills it
   there, proving injectivity on S. Flatness of S -> Q preserves the injection.
9. A zero ring has no prime ideals and multiplication on its singleton set is
   injective. For r = 0 all stages and their colimit are canonically R, the product
   is 1, and multiplication is the identity. The argument includes n = 1.
-/
theorem sncRootLimit_normal_charts
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [LocallyOfFiniteType y] [QuasiCompact y]
    [IsSeparated y] (hY : IsRegularScheme Y)
    (A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (∏ i, t i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (R : Type v) [CommRing R] (a : A →+* R) (ha : a.WeaklyEtale)
    (Q : Type w) [CommRing Q] [Algebra (tameRootAlgebra p (fun i ↦ a (t i))) Q]
    [Algebra.WeaklyEtale (tameRootAlgebra p (fun i ↦ a (t i))) Q] :
    (∀ (q : Ideal Q) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) ∧
    Function.Injective (fun z : Q ↦
      algebraMap (tameRootAlgebra p (fun i ↦ a (t i))) Q
        (algebraMap R (tameRootAlgebra p (fun i ↦ a (t i))) (a (∏ i, t i))) * z) := by
  classical
  let : IsLocallyNoetherian Y := hY.1
  let : IsRegular Y := hY.2
  have hA : IsRegularScheme (Spec (.of A)) :=
    ⟨LocallyOfFiniteType.isLocallyNoetherian b,
      ⟨isRegularLocalRing_stalk_of_etale b (fun z ↦ inferInstance)⟩⟩
  obtain ⟨hreduced, hdistinct⟩ := boundary_equations t H hH hproduct hbranches
  have hnunit (n : TameRootOrder p) : IsUnit (n.val : A) := by
    let f : k →+* A := (Scheme.ΓSpecIso (.of A)).hom.hom.comp
      ((b ≫ y).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    have hk : (n.val : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff]
      exact fun hd ↦ (Fact.out : p.Prime).not_dvd_one
        ((Nat.dvd_gcd (dvd_refl p) hd).trans (by rw [Nat.gcd_comm, n.property.2.gcd_eq_one]))
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hk).map f
  have hn : ∀ n : TameRootOrder p, ∀ (q : Ideal
      (RootStage (fun i ↦ a (t i)) n.val)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
    intro n
    let : IsRegularRing (RootStage t n.val) := isRegularRing_snc_finiteRoot
      A hA r t H hH hreduced hdistinct hbranches n.val n.property.1 (hnunit n)
    exact (stage_weaklyEtale a ha t n.val).isNormalRing
      (IsRegularRing.isNormalRing (RootStage t n.val))
  refine ⟨?_, ?_⟩
  · exact ((RingHom.weaklyEtale_algebraMap_iff).mpr
      (inferInstance : Algebra.WeaklyEtale (tameRootAlgebra p (fun i ↦ a (t i))) Q)).isNormalRing
      (fullRoot_normal p (fun i ↦ a (t i)) hn)
  · have ha' : a.Flat := by
      let : Algebra A R := a.toAlgebra
      let : Algebra.WeaklyEtale A R := ha
      exact inferInstanceAs (Module.Flat A R)
    have hq : (algebraMap (tameRootAlgebra p (fun i ↦ a (t i))) Q).Flat :=
      RingHom.flat_algebraMap_iff.mpr inferInstance
    exact fullRoot_regular a ha' t p (∏ i, t i)
      (boundary_regular t H hH hproduct).1 hq

end AlgebraicGeometry.ProEtale
