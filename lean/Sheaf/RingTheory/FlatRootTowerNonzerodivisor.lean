/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.SimultaneousRootTower
public import Mathlib.RingTheory.RingHom.Flat

import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Nonzerodivisors in a flat simultaneous-root tower

Source: Stacks Project, Algebra, Tags 00HB, 00CX, 04GG (monic quotient argument),
00D6 and 00D7; Categories, Tag 04AX (eventual equality before Tag 002W).
The full assertion is the agent assembly recorded in the DAG.
(blueprint: lem-sfb-flat-root-tower-nonzerodivisor).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Algebra

private theorem flat_regular {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    (a : A →+* R) (ha : a.Flat) (c : A)
    (hc : Function.Injective (fun x : A ↦ c * x)) :
    Function.Injective (fun x : R ↦ a c * x) := by
  let := a.toAlgebra
  have : Module.Flat A R := ha
  exact IsSMulRegular.of_flat (S := R) hc

private noncomputable def rootVar {R : Type v} [CommRing R] {r : ℕ} (n : ℕ) (t : Fin r → R)
    (i : Fin r) : pthRootAlgebra n r R t :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

private theorem rootVar_pow {R : Type v} [CommRing R] {r : ℕ} (n : ℕ)
    (t : Fin r → R) (i : Fin r) :
    rootVar n t i ^ n = algebraMap R (pthRootAlgebra n r R t) (t i) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _ (MvPolynomial.X i ^ n - MvPolynomial.C (t i)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

private noncomputable def rootLift {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] {r : ℕ} (n : ℕ) (t : Fin r → R) (x : Fin r → S)
    (hx : ∀ i, x i ^ n = algebraMap R S (t i)) : pthRootAlgebra n r R t →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) (by
    intro f hf
    apply (show Ideal.span (Set.range (fun i : Fin r ↦
      MvPolynomial.X i ^ n - MvPolynomial.C (t i))) ≤
      RingHom.ker (MvPolynomial.aeval x).toRingHom from
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp [hx])) hf)

private theorem rootLift_var {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] {r : ℕ} (n : ℕ) (t : Fin r → R) (x : Fin r → S)
    (hx : ∀ i, x i ^ n = algebraMap R S (t i)) (i : Fin r) :
    rootLift n t x hx (rootVar n t i) = x i := by
  simp [rootLift, rootVar]

private theorem root_ext {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] {r n : ℕ} {t : Fin r → R}
    (f g : pthRootAlgebra n r R t →ₐ[R] S)
    (h : ∀ i, f (rootVar n t i) = g (rootVar n t i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem root_regular {R : Type v} [CommRing R] (n : ℕ) (hn : n ≠ 0)
    (r : ℕ) (t : Fin r → R) (c : R)
    (hc : Function.Injective (fun x : R ↦ c * x)) :
    Function.Injective (fun x : pthRootAlgebra n r R t ↦
      algebraMap R (pthRootAlgebra n r R t) c * x) := by
  classical
  induction r with
  | zero =>
    let f := rootLift (S := R) n t (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
    have hleft (x : pthRootAlgebra n 0 R t) : algebraMap R _ (f x) = x := by
      have he : (Algebra.ofId R _).comp f = AlgHom.id R _ :=
        root_ext _ _ (fun i ↦ Fin.elim0 i)
      exact AlgHom.congr_fun he x
    intro x y hxy
    have hf : f x = f y := hc (by simpa using congrArg f hxy)
    rw [← hleft x, ← hleft y, hf]
  | succ r ih =>
    let B := pthRootAlgebra n r R (fun i ↦ t i.succ)
    let p : Polynomial B := Polynomial.X ^ n - Polynomial.C (algebraMap R B (t 0))
    let T := AdjoinRoot p
    have : Module.Free B T := (Polynomial.monic_X_pow_sub_C _ hn).free_adjoinRoot
    have hB := ih (fun i ↦ t i.succ)
    have hT := flat_regular (algebraMap B T)
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat B T))
      (algebraMap R B c) hB
    let x : Fin (r + 1) → T := Fin.cases (AdjoinRoot.root p)
      (fun i ↦ algebraMap B T (rootVar n (fun j ↦ t j.succ) i))
    have hx (i : Fin (r + 1)) : x i ^ n = algebraMap R T (t i) := by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · have hp := AdjoinRoot.eval₂_root p
        change AdjoinRoot.root p ^ n = algebraMap R T (t 0)
        rw [IsScalarTower.algebraMap_apply R B T]
        change AdjoinRoot.root p ^ n = AdjoinRoot.of p _
        exact sub_eq_zero.mp (by simpa only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C, AdjoinRoot.algebraMap_eq] using hp)
      · change (algebraMap B T) (rootVar n (fun j ↦ t j.succ) j) ^ n = _
        rw [← map_pow, rootVar_pow, ← IsScalarTower.algebraMap_apply R B T]
    let f := rootLift n t x hx
    let j : B →ₐ[R] pthRootAlgebra n (r + 1) R t :=
      rootLift n (fun i ↦ t i.succ) (fun i ↦ rootVar n t i.succ)
        (fun i ↦ rootVar_pow n t i.succ)
    let g : T →ₐ[R] pthRootAlgebra n (r + 1) R t :=
      AdjoinRoot.liftAlgHom p j (rootVar n t 0) (by simp [p, rootVar_pow])
    have hgf : g.comp f = AlgHom.id R _ := by
      apply root_ext
      intro i
      change g (f (rootVar n t i)) = rootVar n t i
      rw [rootLift_var]
      refine Fin.cases ?_ (fun k ↦ ?_) i
      · exact AdjoinRoot.liftAlgHom_root p j (rootVar n t 0) _
      · change g (AdjoinRoot.of p (rootVar n (fun j ↦ t j.succ) k)) = _
        rw [AdjoinRoot.liftAlgHom_of]
        exact rootLift_var n _ _ _ k
    have hf : Function.Injective f := by
      intro z z' h
      have := congrArg g h
      simpa only [← AlgHom.comp_apply, hgf, AlgHom.id_apply] using this
    intro z z' h
    apply hf
    apply hT
    rw [← IsScalarTower.algebraMap_apply R B T]
    simpa only [map_mul, AlgHom.commutes] using congrArg f h

set_option backward.isDefEq.respectTransparency false in
private theorem colimit_coeff {R : Type v} [CommRing R] {r : ℕ}
    (t : Fin r → R) (I : Set ℕ+) (h1 : (1 : ℕ+) ∈ I)
    (n : RootTowerIndex I) (c : R) :
    (colimit.ι (simultaneousRootDiagram t I) n).hom
      (algebraMap R (pthRootAlgebra (n.1 : ℕ) r R t) c) =
      simultaneousRootColimitMap t I h1 c := by
  let f := @homOfLE (RootTowerIndex I) (rootTowerIndexPreorder I)
    (⟨1, h1⟩ : RootTowerIndex I) n (one_dvd _)
  have h := congrArg
    (fun k ↦ CommRingCat.Hom.hom k (algebraMap R (pthRootAlgebra 1 r R t) c))
    (colimit.w (simultaneousRootDiagram t I) f)
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at h
  change (colimit.ι (simultaneousRootDiagram t I) n).hom
    (simultaneousRootTransition t (leOfHom f) (algebraMap R _ c)) = _ at h
  rw [AlgHom.commutes] at h
  dsimp only [simultaneousRootColimitMap, RingHom.comp_apply]
  convert h using 1
  rfl

private theorem zero_root_bijective {R : Type v} [CommRing R]
    (n : ℕ) (t : Fin 0 → R) :
    Function.Bijective (algebraMap R (pthRootAlgebra n 0 R t)) := by
  let f := rootLift (S := R) n t (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
  have hleft (x : pthRootAlgebra n 0 R t) : algebraMap R _ (f x) = x := by
    have he : (Algebra.ofId R _).comp f = AlgHom.id R _ :=
      root_ext _ _ (fun i ↦ Fin.elim0 i)
    exact AlgHom.congr_fun he x
  constructor
  · intro x y h
    simpa using congrArg f h
  · intro x
    exact ⟨f x, hleft x⟩

set_option backward.isDefEq.respectTransparency false in
/-- A regular element stays regular on the flat base, all finite simultaneous-root stages,
their filtered ring colimit, and every flat algebra over that colimit. With no parameters
the finite stages and colimit identify with the base through their coefficient maps.

Source: Stacks, Algebra, Tags 00HB, 00CX, 04GG (monic quotient argument), 00D6 and 00D7;
Categories, Tag 04AX, eventual equality before Tag 002W. This is an agent assembly.
(blueprint: lem-sfb-flat-root-tower-nonzerodivisor).

Proof:
1. The index is the divisibility preorder on I. It contains 1, and the common-multiple
   hypothesis gives an upper bound for every pair; parallel arrows are unique. Hence
   it is filtered. The canonical diagram is that of `def-sfb-simultaneous-root-tower`:
   its quotient evaluations send x_(d,n) to x_(d,m)^(m/n), preserve the root equations,
   and compose since (k/m)*(m/n)=k/n. These are R-algebra maps.
2. Tensor the injective A-linear multiplication map by c with the flat A-module R,
   using `lem-trf-flat-tensor-preserves-injection` and
   `def-weil-pbc-module-tensor-product`. Under R ⊗[A] A ≃ R, r ⊗ b ↦ r*a(b),
   with inverse r ↦ r ⊗ 1, this is multiplication by a(c). It is injective.
3. For a fixed n, adjoin the r roots successively. A zero intermediate ring causes
   no problem. Otherwise each polynomial X^n-a(t_d) is monic of degree n > 0.
   `lem-weil-pbc-monic-quotient-free` gives unique coefficients on 1,X,...,X^(n-1).
   Multiplication by c kills an element only if it kills every coefficient; the
   induction hypothesis makes all coefficients zero. The successive quotients and
   `pthRootAlgebra` are isomorphic by the mutually inverse evaluations fixing all
   coefficients and root generators. Thus every finite stage has the asserted injection.
4. By `lem-pc-filtered-colimit-commrings-elementwise`, every colimit element z has
   a representative b at some stage n. If c*z=0, eventual equality gives a later
   stage where c*b=0. The two arrows coincide since the index is a preorder.
   Step 3 makes the image of b zero, so z=0 by the cocone identity. A zero kernel
   gives injectivity of the additive multiplication map by taking differences.
   No transition map was assumed injective.
5. Repeat step 2 over S with its flat algebra Q, using Q ⊗[S] S ≃ Q.
   This proves the fourth injectivity claim. These arguments allow zero R, S or Q:
   every self-map of the zero module is injective. No characteristic, invertibility,
   normality or Noetherian assumption has occurred.
6. If r=0 the polynomial ring has no variables and the relation ideal is zero.
   Its coefficient map identifies every stage with R, and all transitions become
   identities. A cocone on this constant diagram factors uniquely through its
   leg at 1, since 1 divides every root order. Therefore its colimit is R by the
   coefficient map as well. These are exactly the displayed ring equivalences.
-/
theorem flat_root_tower_nonzerodivisor
    (A : Type u) (R : Type v) [CommRing A] [CommRing R]
    (a : A →+* R) (ha : a.Flat) (r : ℕ) (t : Fin r → A) (c : A)
    (hc : Function.Injective (fun x : A ↦ c * x))
    (I : Set ℕ+) (h1 : (1 : ℕ+) ∈ I)
    (hfiltered : ∀ n ∈ I, ∀ m ∈ I, ∃ k ∈ I, (n : ℕ) ∣ (k : ℕ) ∧ (m : ℕ) ∣ (k : ℕ))
    (Q : Type w) [CommRing Q]
    (q : ↥(colimit (simultaneousRootDiagram (fun d ↦ a (t d)) I)) →+* Q) (hq : q.Flat) :
    Function.Injective (fun x : R ↦ a c * x) ∧
    (∀ n : RootTowerIndex I,
      Function.Injective (fun x : pthRootAlgebra (n.1 : ℕ) r R (fun d ↦ a (t d)) ↦
        algebraMap R (pthRootAlgebra (n.1 : ℕ) r R (fun d ↦ a (t d))) (a c) * x)) ∧
    Function.Injective
      (fun x : ↥(colimit (simultaneousRootDiagram (fun d ↦ a (t d)) I)) ↦
        simultaneousRootColimitMap (fun d ↦ a (t d)) I h1 (a c) * x) ∧
    Function.Injective (fun x : Q ↦
      q (simultaneousRootColimitMap (fun d ↦ a (t d)) I h1 (a c)) * x) ∧
    (r = 0 →
      (∀ n : RootTowerIndex I,
        ∃ e : R ≃+* pthRootAlgebra (n.1 : ℕ) r R (fun d ↦ a (t d)),
          e.toRingHom = algebraMap R (pthRootAlgebra (n.1 : ℕ) r R (fun d ↦ a (t d)))) ∧
      ∃ e : R ≃+* ↥(colimit (simultaneousRootDiagram (fun d ↦ a (t d)) I)),
        e.toRingHom = simultaneousRootColimitMap (fun d ↦ a (t d)) I h1) := by
  classical
  have : IsFiltered (RootTowerIndex I) := {
    nonempty := ⟨⟨1, h1⟩⟩
    cocone_objs := fun n m ↦ by
      obtain ⟨k, hk, hnk, hmk⟩ := hfiltered n.1 n.2 m.1 m.2
      exact ⟨⟨k, hk⟩, @homOfLE (RootTowerIndex I) (rootTowerIndexPreorder I) n ⟨k, hk⟩ hnk,
        @homOfLE (RootTowerIndex I) (rootTowerIndexPreorder I) m ⟨k, hk⟩ hmk, trivial⟩
    cocone_maps := fun {_ _} f g ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩ }
  let tR : Fin r → R := fun d ↦ a (t d)
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let F := simultaneousRootDiagram tR I
  let S := ↥(colimit F)
  let cS := simultaneousRootColimitMap tR I h1 (a c)
  have hR := flat_regular a ha c hc
  have hstage (n : RootTowerIndex I) :=
    root_regular (n.1 : ℕ) (ne_of_gt n.1.pos) r tR (a c) hR
  have hSzero (z : S) (hz : cS * z = 0) : z = 0 := by
    obtain ⟨n, b, rfl⟩ := Concrete.colimit_exists_rep F z
    change pthRootAlgebra (n.1 : ℕ) r R tR at b
    have hb : (colimit.ι F n)
        (algebraMap R (pthRootAlgebra (n.1 : ℕ) r R tR) (a c) * b) =
        (colimit.ι F n) 0 := by
      change (colimit.ι F n).hom
        (algebraMap R (pthRootAlgebra (n.1 : ℕ) r R tR) (a c) * b) = _
      rw [map_mul, colimit_coeff tR I h1, map_zero]
      exact hz
    obtain ⟨m, f, g, hfg⟩ := Concrete.colimit_exists_of_rep_eq F _ _ hb
    have hm : F.map f b = 0 := by
      have hzero : F.map f (algebraMap R (pthRootAlgebra (n.1 : ℕ) r R tR) (a c) * b) = 0 := by
        simpa using hfg
      change simultaneousRootTransition tR (leOfHom f)
        (algebraMap R _ (a c) * b) = 0 at hzero
      rw [map_mul, AlgHom.commutes] at hzero
      change simultaneousRootTransition tR (leOfHom f) b = 0
      exact hstage m (by simpa using hzero)
    have hw := ConcreteCategory.congr_hom (colimit.w F f) b
    change (colimit.ι F m).hom (F.map f b) = (colimit.ι F n) b at hw
    rw [hm, map_zero] at hw
    exact hw.symm
  have hS : Function.Injective (fun z : S ↦ cS * z) := by
    intro x y h
    exact sub_eq_zero.mp (hSzero (x - y) (by simpa only [mul_sub, sub_eq_zero] using h))
  refine ⟨hR, hstage, hS, flat_regular q hq cS hS, ?_⟩
  intro hr
  subst r
  have hfinite (n : RootTowerIndex I) := zero_root_bijective (n.1 : ℕ) tR
  refine ⟨fun n ↦ ⟨RingEquiv.ofBijective _ (hfinite n), rfl⟩, ?_⟩
  have hinj : Function.Injective (simultaneousRootColimitMap tR I h1) := by
    intro x y hxy
    change (colimit.ι F (⟨1, h1⟩ : RootTowerIndex I))
      (algebraMap R (pthRootAlgebra 1 0 R tR) x) =
      (colimit.ι F (⟨1, h1⟩ : RootTowerIndex I))
      (algebraMap R (pthRootAlgebra 1 0 R tR) y) at hxy
    obtain ⟨m, f, g, hfg⟩ := Concrete.colimit_exists_of_rep_eq F _ _ hxy
    apply (hfinite m).1
    change simultaneousRootTransition tR (leOfHom f) (algebraMap R _ x) =
      simultaneousRootTransition tR (leOfHom g) (algebraMap R _ y) at hfg
    simpa only [AlgHom.commutes] using hfg
  have hsurj : Function.Surjective (simultaneousRootColimitMap tR I h1) := by
    intro z
    obtain ⟨n, b, rfl⟩ := Concrete.colimit_exists_rep F z
    obtain ⟨x, rfl⟩ := (hfinite n).2 b
    exact ⟨x, (colimit_coeff tR I h1 n x).symm⟩
  exact ⟨RingEquiv.ofBijective _ ⟨hinj, hsurj⟩, rfl⟩

end Algebra
