/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.LocalFrobeniusConjugacy
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.FixedLocalOperatorAtLift
public import WeilConjectures.PointCount

/-!
# Degree formula for the local Frobenius

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-at-a-fixed-point/sk-p-frob/sk-c-proper-global/
lem-trf-frobenius-degree-formula.md and its proof, Steps 1--2
(blueprint: lem-trf-frobenius-degree-formula).

The operators are the recorded finite condensed-coefficient local Frobenii, evaluated
on their own point-fibre complexes. The scalar ring is the terminal evaluation of the
discrete condensed ring A, canonically A. Perfectness is concluded, not assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedFrobeniusOperators

open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

private theorem positive_powers {C : Type*} [Category C] {X : C}
    (f : (m : ℕ) → 1 ≤ m → End X)
    (hf : ∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b),
      f (a + b) (by omega) = f a ha ≫ f b hb)
    (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) (hdm : d ∣ m) :
    f m hm = (f d hd) ^ (m / d) := by
  have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdm
  have hr : 1 ≤ m / d := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hm hdm
    · exact hd
  have hpow : ∀ r : ℕ, ∀ hr : 1 ≤ r,
      f (d * r) (Nat.mul_pos hd hr) = (f d hd) ^ r := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => simp
    | succ r hr ih =>
      calc
        f (d * (r + 1)) _ = f (d * r) _ ≫ f d hd := by
          simpa only [Nat.mul_succ] using hf (d * r) d (Nat.mul_pos hd hr) hd
        _ = (f d hd) ^ (r + 1) := by rw [ih, pow_succ']; rfl
  simpa only [hmul] using hpow (m / d) hr

private theorem divisible_positive_powers {C : Type*} [Category C] {X : C}
    (d : ℕ) (hd : 1 ≤ d)
    (f : (m : ℕ) → 1 ≤ m → d ∣ m → End X)
    (hf : ∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hda : d ∣ a) (hdb : d ∣ b),
      f (a + b) (by omega) (dvd_add hda hdb) = f a ha hda ≫ f b hb hdb)
    (m : ℕ) (hm : 1 ≤ m) (hdm : d ∣ m) :
    f m hm hdm = (f d hd (dvd_refl d)) ^ (m / d) := by
  let g : (r : ℕ) → 1 ≤ r → End X :=
    fun r hr ↦ f (d * r) (Nat.mul_pos hd hr) (dvd_mul_right d r)
  have hg : ∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b),
      g (a + b) (by omega) = g a ha ≫ g b hb := by
    intro a b ha hb
    simpa only [g, Nat.mul_add] using
      hf (d * a) (d * b) (Nat.mul_pos hd ha) (Nat.mul_pos hd hb)
        (dvd_mul_right d a) (dvd_mul_right d b)
  have h := positive_powers g hg 1 (by omega) (m / d)
    (Nat.div_pos (Nat.le_of_dvd hm hdm) hd) (one_dvd _)
  simpa only [g, Nat.mul_one, Nat.div_one, Nat.mul_div_cancel' hdm] using h

private theorem trace_coordinates {R : Type u} [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {P Q : DerivedCategory (ModuleCat.{u} R)} (e : P = Q)
    (hP : DerivedCategory.IsPerfectRingComplex P)
    (hQ : DerivedCategory.IsPerfectRingComplex Q) (f : End P) :
    DerivedCategory.perfectCategoricalTrace _ hP f =
      DerivedCategory.perfectCategoricalTrace _ hQ
        ((eqToIso e).inv ≫ f ≫ (eqToIso e).hom) := by
  subst Q
  simp

private theorem frobeniusFixedOperator_powers
    (x : Y₀.left) (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (hd : 1 ≤ Y₀.hom.degreeOver x)
    (hfix : ∀ (m : ℕ) (_hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m →
      z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ m = z)
    (m : ℕ) (hm : 1 ≤ m) (hdm : Y₀.hom.degreeOver x ∣ m) :
    frobeniusFixedOperator F Y₀ ell E n hn K z m hm (hfix m hm hdm) =
      (frobeniusFixedOperator F Y₀ ell E n hn K z (Y₀.hom.degreeOver x) hd
        (hfix _ hd (dvd_refl _))) ^ (m / Y₀.hom.degreeOver x) := by
  refine divisible_positive_powers (Y₀.hom.degreeOver x) hd
    (fun r hr hdr ↦ frobeniusFixedOperator F Y₀ ell E n hn K z r hr (hfix r hr hdr))
    ?_ m hm hdm
  intro a b ha hb hda hdb
  exact frobeniusFixedOperator_add F Y₀ ell hEll E n hn K z a b ha hb
    (hfix a ha hda) (hfix b hb hdb) (hfix (a + b) (by omega) (dvd_add hda hdb))

/-- The trace at any F_(q^m)-point above x is the trace of the one-circuit local
Frobenius to the power m / deg(x), at the specified F_(q^deg(x))-point above x.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-at-a-fixed-point/sk-p-frob/sk-c-proper-global/
lem-trf-frobenius-degree-formula.md and its proof, Steps 1--2
(blueprint: lem-trf-frobenius-degree-formula).

Proof, following the node's five steps:
1. Set d = [kappa(x):k0] and r = m/d. The specified degree-d point gives a lift z
   fixed by Phi^d, and by Phi^m since d divides m.
2. At z, fixed-point transport composition and pullback-stalk coherence, the naturality
   of kappa, and the iterated Weil cocycle give F_(z,(r+1)d) = F_(z,d) F_(z,rd).
3. Starting with r=1, induction gives F_(z,rd) = F_(z,d)^r.
4. Every degree-m point above x is a lift in the normalized orbit of z. Local Frobenius
   conjugacy transports F_(z,m) to its operator on that point's actual stalk complex.
5. These stalk complexes are perfect. Conjugacy invariance of their categorical traces
   gives the displayed equality, with r=m/d. This also proves independence of the
   chosen degree-d lift. The zero complex and d=1 require no separate assumptions.
-/
theorem frobenius_degree_formula
    (F : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of F.k₀)))
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (x : Y₀.left) (_hx : IsClosed ({x} : Set Y₀.left)) :
    letI : HasDerivedCategory.{u + 1}
        (ModuleCat.{u + 1} (condensedScalarRing (finiteCoefficient ell E n))) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    ∃ hd : 1 ≤ Y₀.hom.degreeOver x,
      ∀ (xₘ : F.extensionPoints Y₀ (Y₀.hom.degreeOver x) hd),
        IsLocalFrobeniusLift F Y₀ x
          (extensionPointGeometry F Y₀ (Y₀.hom.degreeOver x) hd xₘ) →
      ∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m →
      ∀ (y : F.extensionPoints Y₀ m hm),
        IsLocalFrobeniusLift F Y₀ x (extensionPointGeometry F Y₀ m hm y) →
      ∃ (hPy : DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
          ((localFrobeniusFibre F Y₀ ell E n (extensionPointGeometry F Y₀ m hm y)).obj
            K.carrier.obj))
        (hPx : DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
          ((localFrobeniusFibre F Y₀ ell E n
            (extensionPointGeometry F Y₀ (Y₀.hom.degreeOver x) hd xₘ)).obj K.carrier.obj)),
        DerivedCategory.perfectCategoricalTrace _ hPy
            (condensedLocalFrobenius F Y₀ ell hEll E n hn m hm ⟨y⟩ K) =
          DerivedCategory.perfectCategoricalTrace _ hPx
            ((condensedLocalFrobenius F Y₀ ell hEll E n hn
              (Y₀.hom.degreeOver x) hd ⟨xₘ⟩ K) ^ (m / Y₀.hom.degreeOver x)) := by
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (condensedScalarRing (finiteCoefficient ell E n))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have hxfin : x ∈ Y₀.left.finitePoints := by
    rw [Y₀.hom.finitePoints_eq_closedPoints]
    exact _hx
  have hd : 1 ≤ Y₀.hom.degreeOver x :=
    Nat.one_le_iff_ne_zero.mpr (Y₀.hom.degreeOver_ne_zero hxfin)
  refine ⟨hd, ?_⟩
  intro xₘ hxₘ m hm hdm y hy
  let z := extensionPointGeometry F Y₀ (Y₀.hom.degreeOver x) hd xₘ
  obtain ⟨hd', hP, hP₀, hlift, hinj, henum, hperiod, hiter, hcomp, hpoints,
    hT₀, hTadd, hfixed, hconj, hlast⟩ :=
    (local_frobenius_conjugacy F Y₀ ell E n hn hEll K x _hx).2 z hxₘ
  have hzero : localFrobeniusOrbit F Y₀ z 0 = z := by
    change z ≫ 𝟙 _ = z
    exact Category.comp_id z
  have hfix : ∀ (r : ℕ) (hr : 1 ≤ r), Y₀.hom.degreeOver x ∣ r →
      z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ r = z := by
    intro r hr hdr
    simpa only [hzero] using hfixed r hr hdr 0
  obtain ⟨i, hi⟩ := henum (extensionPointGeometry F Y₀ m hm y) hy
  have hPy : DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
      ((localFrobeniusFibre F Y₀ ell E n
        (extensionPointGeometry F Y₀ m hm y)).obj K.carrier.obj) := by
    rw [← hi]
    exact hP i
  refine ⟨hPy, hP₀, ?_⟩
  obtain ⟨y₀, hy₀, _⟩ := hpoints m hm hdm 0
  have hy₀' : extensionPointGeometry F Y₀ m hm y₀ = z := hy₀.trans hzero
  have ht := (hconj m hm hdm i y₀ y hy₀' hi.symm).2
  have hcoord := trace_coordinates
    (congrArg (fun w ↦ (localFrobeniusFibre F Y₀ ell E n w).obj K.carrier.obj) hi.symm)
    hPy (hP i) (condensedLocalFrobenius F Y₀ ell hEll E n hn m hm ⟨y⟩ K)
  change DerivedCategory.perfectCategoricalTrace _ hPy _ =
    DerivedCategory.perfectCategoricalTrace _ (hP i)
      (localFrobeniusAtLift F Y₀ ell E n hn hEll K m hm y _ hi.symm) at hcoord
  rw [hcoord, ht]
  have hpower := frobeniusFixedOperator_powers F Y₀ ell hEll E n hn K x z hd hfix m hm hdm
  rw [frobeniusFixedOperator_atLift F Y₀ ell hEll E n hn K m hm y₀ z hy₀',
    frobeniusFixedOperator_atLift F Y₀ ell hEll E n hn K _ hd xₘ z rfl] at hpower
  rw [hpower]
  simp only [localFrobeniusAtLift, z, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp]
  erw [Category.comp_id]

end WeilConjectures.CondensedFrobeniusOperators
