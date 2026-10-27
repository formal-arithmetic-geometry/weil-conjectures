/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.GroupTheory.IntegralSharpeningGroupExactness
import Mathlib.GroupTheory.MonoidLocalization.Finite
import Sheaf.GroupTheory.FineMonoidUnitSplitting
import Sheaf.RingTheory.AffineMonoidAlgebraNormalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Saturation and sharp reduction of a smooth affine toric algebra

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VIII, proof of
Lemma 3.2.12(ii), printed pp. 104--105
(blueprint: lem-trf-smooth-toric-saturated-sharp-reduction).

Monoids use multiplicative notation. Thus `Associates P` is the additive quotient
`P/Pˣ`, and a product of monoids expresses the finite direct sum in the source.
The Laurent algebra and its specified vertex ideal below are explicit constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The subgroup of the group completion coming from the units of `P`.
Source: ILO VIII, proof of Lemma 3.2.12(ii), p. 104
(blueprint: lem-trf-smooth-toric-saturated-sharp-reduction). -/
def toricUnitSubgroup (P : Type u) [CommMonoid P] :
    Subgroup (Algebra.GrothendieckGroup P) :=
  Subgroup.closure (Set.range (fun x : Pˣ ↦ Algebra.GrothendieckGroup.of (x : P)))

/-- The multivariate Laurent algebra `k[R][y₁⁻¹,y₁,...,yₜ⁻¹,yₜ]`, realized as the
actual group algebra of the integer exponent lattice over `k[R]`; rank zero is allowed.
Source: ILO VIII, proof of Lemma 3.2.12(ii), p. 104
(blueprint: lem-trf-smooth-toric-saturated-sharp-reduction). -/
abbrev toricLaurentAlgebra (k R : Type u) [Field k] [CommMonoid R] (t : ℕ) :=
  MonoidAlgebra (MonoidAlgebra k R) (Multiplicative (Fin t → ℤ))

/-- The specified rational vertex ideal: nonidentity sharp monomials and `yⱼ - 1`.
Both generating families may be empty. The definition itself needs no sharpness proof.
Source: ILO VIII, proof of Lemma 3.2.12(ii), pp. 104--105, with the unit factor retained
(blueprint: lem-trf-smooth-toric-saturated-sharp-reduction). -/
noncomputable def toricLaurentVertexIdeal
    (k R : Type u) [Field k] [CommMonoid R] (t : ℕ) :
    Ideal (toricLaurentAlgebra k R t) :=
  Ideal.span
    ((Set.range (fun q : {q : R // q ≠ 1} ↦
      algebraMap (MonoidAlgebra k R) (toricLaurentAlgebra k R t)
        (MonoidAlgebra.of k R q.1))) ∪
      Set.range (fun j : Fin t ↦
        MonoidAlgebra.of (MonoidAlgebra k R) (Multiplicative (Fin t → ℤ))
          (Multiplicative.ofAdd (Pi.single j 1)) - 1))

private theorem completion_torsionFree (P : Type u) [CommMonoid P]
    (hG : ∀ (g : Algebra.GrothendieckGroup P) (n : ℕ), 0 < n → g ^ n = 1 → g = 1) :
    IsMulTorsionFree (Algebra.GrothendieckGroup P) := by
  refine ⟨fun {n} hn a b hab ↦ ?_⟩
  apply div_eq_one.mp
  apply hG (a / b) n (Nat.pos_of_ne_zero hn)
  simp [div_pow, hab]

private theorem affine_regular_localizations (A : Type u) [CommRing A]
    (hA : IsRegular (Spec (.of A))) (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let := hA
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (.of A) ⟨p, inferInstance⟩).commRingCatIsoToRingEquiv

private theorem normal_monoid_saturation (k P : Type u) [Field k] [CommMonoid P]
    (hP : FineFan.IsFine P) [IsMulTorsionFree (Algebra.GrothendieckGroup P)]
    (hReg : IsRegular (Spec (.of (MonoidAlgebra k P)))) :
    FineFan.saturation (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := P))) =
      MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := P)) := by
  classical
  let G := Algebra.GrothendieckGroup P
  let A := MonoidAlgebra k P
  let B := MonoidAlgebra k G
  let K := FractionRing B
  obtain ⟨_, _, hK, hA, _, hB, hFrac, _, hint, _, _⟩ :=
    MonoidAlgebra.affine_monoid_algebra_normalization k P hP
  let : IsDomain A := hA
  let : IsDomain B := hB
  let : Algebra A K := (MonoidAlgebra.normalizationFractionMap k P).toAlgebra
  let : IsFractionRing A K := hFrac
  let : IsIntegrallyClosed A := IsIntegrallyClosed.of_localization_maximal
    (fun p _ _ ↦ by
      let := hReg
      have := IsRegular.isIntegrallyClosed_stalk (X := Spec (.of A)) ⟨p, inferInstance⟩
      exact IsIntegrallyClosed.of_equiv
        (Spec.stalkIso (.of A) ⟨p, inferInstance⟩).commRingCatIsoToRingEquiv)
  apply le_antisymm
  · apply Submonoid.closure_le.mpr
    rintro g ⟨n, hn, hg⟩
    let q : FineFan.saturation
        (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := P))) :=
      ⟨g, Submonoid.subset_closure ⟨n, hn, hg⟩⟩
    let y := MonoidAlgebra.normalizationSaturatedFractionMap k P
      (MonoidAlgebra.single q 1)
    have hy : _root_.IsIntegral A y := (hint y).mpr ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff K).mp inferInstance hy
    have heq : MonoidAlgebra.mapDomainRingHom k (Algebra.GrothendieckGroup.of (M := P)) a =
        MonoidAlgebra.single g 1 := by
      apply hK
      change algebraMap B K
          (MonoidAlgebra.mapDomain (Algebra.GrothendieckGroup.of (M := P)) a) =
        algebraMap B K (MonoidAlgebra.mapDomain
          (FineFan.saturation
            (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := P)))).subtype
          (MonoidAlgebra.single q 1)) at ha
      rw [MonoidAlgebra.mapDomain_single] at ha
      exact ha
    by_contra hnot
    have hzero :
        (MonoidAlgebra.mapDomain (Algebra.GrothendieckGroup.of (M := P)) a).coeff g = 0 := by
      exact Finsupp.mapDomain_of_notMem_range a.coeff g hnot
    have hone := congrArg (fun f : B ↦ f.coeff g) heq
    change (MonoidAlgebra.mapDomain (Algebra.GrothendieckGroup.of (M := P)) a).coeff g =
      (MonoidAlgebra.single g (1 : k)).coeff g at hone
    rw [hzero] at hone
    simp at hone
  · intro g hg
    exact Submonoid.subset_closure ⟨1, by decide, by simpa using hg⟩

private theorem fs_sharpening_data (P : Type u) [CommMonoid P]
    (hP : IsFineSaturatedMonoid P) :
    IsFineSaturatedMonoid (Associates P) ∧
      IsMulTorsionFree (Algebra.GrothendieckGroup (Associates P)) ∧
      (∃ e : Algebra.GrothendieckGroup (Associates P) ≃*
          (Algebra.GrothendieckGroup P ⧸ toricUnitSubgroup P),
        ∀ p : P, e (Algebra.GrothendieckGroup.of (Associates.mk p)) =
          QuotientGroup.mk' (toricUnitSubgroup P) (Algebra.GrothendieckGroup.of p)) ∧
      (∃ r : ℕ, Nonempty ((Algebra.GrothendieckGroup P ⧸ toricUnitSubgroup P) ≃*
        Multiplicative (Fin r → ℤ))) := by
  classical
  let G := Algebra.GrothendieckGroup P
  let R := Associates P
  let H := Algebra.GrothendieckGroup R
  let π : G →* H := Algebra.GrothendieckGroup.lift
    (Algebra.GrothendieckGroup.of.comp (Associates.mkMonoidHom : P →* R))
  have hπ (p : P) : π (Algebra.GrothendieckGroup.of p) =
      Algebra.GrothendieckGroup.of (Associates.mk p) := by
    exact DFunLike.congr_fun (Algebra.GrothendieckGroup.lift.symm_apply_apply
      (Algebra.GrothendieckGroup.of.comp (Associates.mkMonoidHom : P →* R))) p
  obtain ⟨U, hU, _, hinj, hsurj, hker, _⟩ :=
    FineFan.integral_sharpening_group_exactness P hP.2.1
  have hUeq : toricUnitSubgroup P = U := by
    apply le_antisymm
    · apply (Subgroup.closure_le U).mpr
      rintro _ ⟨u, rfl⟩
      rw [hU]
      exact ⟨u, u.isUnit, rfl⟩
    · intro g hg
      rw [← SetLike.mem_coe, hU] at hg
      obtain ⟨p, ⟨u, rfl⟩, rfl⟩ := hg
      exact Subgroup.subset_closure ⟨u, rfl⟩
  have hunit (x : G) (hx : π x = 1) : ∃ u : Pˣ,
      Algebra.GrothendieckGroup.of (u : P) = x := by
    have hxU : x ∈ U := by rw [← hker]; exact hx
    rw [← SetLike.mem_coe, hU] at hxU
    obtain ⟨p, ⟨u, rfl⟩, hp⟩ := hxU
    exact ⟨u, hp⟩
  let : Monoid.FG P := ⟨hP.1⟩
  let : Monoid.FG R :=
    Monoid.fg_of_surjective (Associates.mkMonoidHom : P →* R) Associates.mk_surjective
  have hfs : IsFineSaturatedMonoid R := by
    refine ⟨Monoid.FG.fg_top, hinj, ?_⟩
    intro g n hn hg
    obtain ⟨q, hq⟩ := hg
    obtain ⟨p, rfl⟩ := Associates.mk_surjective q
    obtain ⟨x, hx⟩ := hsurj g
    obtain ⟨u, hu⟩ := hunit (x ^ n / Algebra.GrothendieckGroup.of p) (by
      rw [map_div, map_pow, hx, hπ, hq]
      simp)
    have hxn : Algebra.GrothendieckGroup.of (p * (u : P)) = x ^ n := by
      rw [map_mul, hu]
      simp
    obtain ⟨r, hr⟩ := hP.2.2 x n hn ⟨_, hxn⟩
    exact ⟨Associates.mk r, by rw [← hπ, hr, hx]⟩
  have htf : IsMulTorsionFree H := by
    apply completion_torsionFree R
    intro g n hn hgn
    obtain ⟨q, hq⟩ := hfs.2.2 g n hn ⟨1, by simpa using hgn.symm⟩
    obtain ⟨r, hr⟩ := hfs.2.2 g⁻¹ n hn ⟨1, by simp [inv_pow, hgn]⟩
    have hqr : q * r = 1 := hinj (by rw [map_mul, hq, hr, mul_inv_cancel, map_one])
    have hqu : IsUnit q := ⟨⟨q, r, hqr, by simpa [mul_comm] using hqr⟩, rfl⟩
    rw [(Associates.isUnit_iff_eq_one q).mp hqu, map_one] at hq
    exact hq.symm
  let : IsMulTorsionFree H := htf
  let e : H ≃* (G ⧸ toricUnitSubgroup P) :=
    ((QuotientGroup.quotientMulEquivOfEq (hUeq.trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hsurj)).symm
  have he (p : P) : e (Algebra.GrothendieckGroup.of (Associates.mk p)) =
      QuotientGroup.mk' (toricUnitSubgroup P) (Algebra.GrothendieckGroup.of p) := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change Algebra.GrothendieckGroup.of (Associates.mk p) =
      π (Algebra.GrothendieckGroup.of p)
    exact (hπ p).symm
  let b := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive H)
  let eH : H ≃* Multiplicative (Fin b.1 → ℤ) :=
    { toFun := fun g ↦ Multiplicative.ofAdd (b.2.equivFun (Additive.ofMul g))
      invFun := fun v ↦ Additive.toMul (b.2.equivFun.symm (Multiplicative.toAdd v))
      left_inv := fun g ↦ b.2.equivFun.symm_apply_apply g
      right_inv := fun v ↦ b.2.equivFun.apply_symm_apply v
      map_mul' := fun x y ↦ b.2.equivFun.map_add x y }
  exact ⟨hfs, htf, ⟨e, he⟩, b.1, ⟨e.symm.trans eH⟩⟩

private theorem laurent_vertex_residue (k R : Type u) [Field k] [CommMonoid R]
    (hsharp : FineFan.IsSharp R) (t : ℕ) :
    (toricLaurentVertexIdeal k R t).IsMaximal ∧
      Nonempty ((toricLaurentAlgebra k R t ⧸ toricLaurentVertexIdeal k R t) ≃ₐ[k] k) := by
  classical
  let A := MonoidAlgebra k R
  let L := Multiplicative (Fin t → ℤ)
  let B := toricLaurentAlgebra k R t
  let I := toricLaurentVertexIdeal k R t
  let Q := B ⧸ I
  let mkQ : B →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  let f : R →* k :=
    { toFun := fun q ↦ if q = 1 then 1 else 0
      map_one' := by simp
      map_mul' := by
        intro a b
        by_cases ha : a = 1
        · simp [ha]
        by_cases hb : b = 1
        · simp [hb]
        have hab : a * b ≠ 1 := by
          intro hab
          exact ha (hsharp a ⟨⟨a, b, hab, by simpa [mul_comm] using hab⟩, rfl⟩)
        simp [ha, hb, hab] }
  let εR : A →ₐ[k] k := MonoidAlgebra.lift k k R f
  let ε : B →ₐ[k] k := εR.comp
    ((MonoidAlgebra.lift A A L (1 : L →* A)).restrictScalars k)
  have hεcoeff (a : A) : ε (algebraMap A B a) = εR a := by
    change εR ((MonoidAlgebra.lift A A L 1) (algebraMap A B a)) = εR a
    rw [AlgHom.commutes, Algebra.algebraMap_self_apply]
  have hεgroup (g : L) : ε (MonoidAlgebra.of A L g) = 1 := by
    change εR ((MonoidAlgebra.lift A A L 1) (MonoidAlgebra.of A L g)) = 1
    rw [MonoidAlgebra.lift_of]
    exact map_one εR
  have hI : I ≤ RingHom.ker ε := by
    apply Ideal.span_le.mpr
    rintro x (⟨q, rfl⟩ | ⟨j, rfl⟩)
    · change ε (algebraMap A B (MonoidAlgebra.of k R q.1)) = 0
      rw [hεcoeff]
      change (MonoidAlgebra.lift k k R f) (MonoidAlgebra.of k R q.1) = 0
      rw [MonoidAlgebra.lift_of]
      exact if_neg q.2
    · change ε (MonoidAlgebra.of A L (Multiplicative.ofAdd (Pi.single j 1)) - 1) = 0
      rw [map_sub, hεgroup, map_one, sub_self]
  let εQ : Q →ₐ[k] k := Ideal.Quotient.liftₐ I ε (fun x hx ↦ hI hx)
  have hqzero (q : R) (hq : q ≠ 1) :
      mkQ (algebraMap A B (MonoidAlgebra.of k R q)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Or.inl ⟨⟨q, hq⟩, rfl⟩)
  have hcoeff (a : A) : mkQ (algebraMap A B a) = algebraMap k Q (εR a) := by
    induction a using MonoidAlgebra.induction_on with
    | of q =>
      by_cases hq : q = 1
      · subst q
        change mkQ (algebraMap A B (1 : A)) = algebraMap k Q (εR 1)
        rw [map_one, map_one, map_one, map_one]
      · rw [hqzero q hq]
        change 0 = algebraMap k Q
          ((MonoidAlgebra.lift k k R f) (MonoidAlgebra.of k R q))
        rw [MonoidAlgebra.lift_of]
        simp [f, hq]
    | add a b ha hb => simp [ha, hb]
    | smul c a ha =>
      change (mkQ.comp (IsScalarTower.toAlgHom k A B)) (c • a) = _
      rw [map_smul]
      change c • mkQ (algebraMap A B a) = _
      rw [ha, map_smul εR]
      simp [Algebra.smul_def]
  let S : Subgroup L :=
    { carrier := {g | mkQ (MonoidAlgebra.of A L g) = 1}
      one_mem' := by
        change mkQ ((MonoidAlgebra.of A L) 1) = 1
        rw [map_one, map_one]
      mul_mem' := by
        intro g h hg hh
        change mkQ ((MonoidAlgebra.of A L) (g * h)) = 1
        rw [map_mul, map_mul, hg, hh, one_mul]
      inv_mem' := by
        intro g hg
        have h : mkQ ((MonoidAlgebra.of A L) g) *
            mkQ ((MonoidAlgebra.of A L) g⁻¹) = 1 := by
          rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
        rw [hg, one_mul] at h
        exact h }
  have hgen (j : Fin t) : Multiplicative.ofAdd (Pi.single j 1) ∈ S := by
    change mkQ (MonoidAlgebra.of A L (Multiplicative.ofAdd (Pi.single j 1))) = 1
    apply sub_eq_zero.mp
    rw [← map_one mkQ, ← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Or.inr ⟨j, rfl⟩)
  have hgroup (g : L) : mkQ (MonoidAlgebra.of A L g) = 1 := by
    change g ∈ S
    have hg : g = ∏ j : Fin t,
        Multiplicative.ofAdd (Pi.single j 1) ^ g.toAdd j := by
      apply Multiplicative.toAdd.injective
      change g.toAdd = ∑ j : Fin t, g.toAdd j • Pi.single j 1
      simp only [← Pi.single_smul, smul_eq_mul, mul_one]
      exact (Finset.univ_sum_single g.toAdd).symm
    rw [hg]
    exact S.prod_mem (fun j _ ↦ S.zpow_mem (hgen j) _)
  have hsurj : Function.Surjective (algebraMap k Q) := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I x
    change ∃ c, algebraMap k Q c = mkQ b
    induction b using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add a b ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by simp [hc, hd]⟩
    | single g a =>
      refine ⟨εR a, ?_⟩
      rw [MonoidAlgebra.single_eq_algebraMap_mul_of, map_mul, hcoeff, hgroup, mul_one]
  have hinj : Function.Injective (algebraMap k Q) := by
    intro a b hab
    have h := congrArg εQ hab
    simpa only [AlgHom.commutes, Algebra.algebraMap_self_apply] using h
  let e : Q ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k Q) ⟨hinj, hsurj⟩).symm
  exact ⟨Ideal.Quotient.maximal_of_isField I (e.toMulEquiv.isField (Field.toIsField k)), ⟨e⟩⟩

/-- A smooth affine toric algebra has saturated exponent monoid, regular spectrum,
and a sharp/unit splitting; all Laurent localizations are regular, including the
specified rational vertex. The equation for the group-completion equivalence fixes
its canonical quotient map, and the equation for the monoid equivalence fixes the
splitting to be `(q,u) ↦ s(q) * u`.

Source: ILO VIII, proof of Lemma 3.2.12(ii), printed pp. 104--105
(blueprint: lem-trf-smooth-toric-saturated-sharp-reduction).

Proof (the eleven steps of the node).
1. Smoothness gives regular stalks by `lem-weil-pbc-smooth-scheme-over-field-regular`;
   regularity gives normality by `rem-pc-regular-normal`. The affine stalk localization
   of `lem-weil-pbc-affine-open-stalk-localization` identifies these with prime localizations.
2. Finite generation and torsion-freeness identify the group completion with a finite
   integer lattice (`lem-trf-fg-torsionfree-group-free`). The leading monomial in its
   lexicographic order shows that its group algebra and the subalgebra `k[P]` are domains.
3. Apply `lem-weil-pbc-normal-domain-of-local-normal` to get integral closedness of `k[P]`.
4. If `g^m` belongs to `P` for positive `m`, its monomial lies in the fraction field of
   `k[P]` and satisfies the monic equation `T^m - e^(g^m)`. Integral closedness, as in
   `def-weil-pbc-normal-ring`, puts it in `k[P]`. Comparing coefficients forces `g ∈ P`.
5. Units form a face. Localizing at units changes nothing; `lem-trf-fs-face-sharpening`
   gives a sharp fs quotient and identifies its completion with the finite free group `G/U`.
6. By `lem-trf-fine-monoid-unit-generators`, the units are finitely generated and
   torsion-free. Apply `lem-trf-fg-torsionfree-group-free` to identify them with `ℤ^t`.
7. Lift a basis of `G/U` to `G` to obtain a group section. For a class represented by
   `p ∈ P`, its lifted value differs from `p` by a unit, so the section lands in `P`.
8. The map `(q,u) ↦ s(q) * u` is bijective: its inverse sends `p` to its quotient class
   and `p / s([p])`, a unit. Cancellation proves uniqueness and multiplicativity.
9. Extend this exponent splitting coefficientwise, using the unit basis to identify
   the second factor with the Laurent integer exponents. The inverse exponent map
   gives the inverse algebra map, as in `def-trf-monoscheme-toric-realization`.
10. Transport the regular prime localizations from step 1 along this algebra equivalence;
    regularity is invariant under ring equivalence (`def-weil-regular-scheme`).
11. Send nonidentity sharp monomials to zero and all Laurent variables to one.
    Sharpness makes this multiplicative. Its kernel is exactly the displayed generators,
    since the successive quotients are the Laurent algebra over `k` and then `k`.
    This proves maximality and the asserted residue field, including either empty family.
-/
theorem smooth_toric_saturated_sharp_reduction
    (k P : Type u) [Field k] [CommMonoid P]
    (hP : FineFan.IsFine P)
    (hG : ∀ (g : Algebra.GrothendieckGroup P) (n : ℕ), 0 < n → g ^ n = 1 → g = 1)
    (hSmooth : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k P))))) :
    FineFan.saturation (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := P))) =
        (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := P))) ∧
      IsRegularScheme (Spec (.of (MonoidAlgebra k P))) ∧
      IsFineSaturatedMonoid (Associates P) ∧ FineFan.IsSharp (Associates P) ∧
      (∃ e : Algebra.GrothendieckGroup (Associates P) ≃*
          (Algebra.GrothendieckGroup P ⧸ toricUnitSubgroup P),
        ∀ p : P, e (Algebra.GrothendieckGroup.of (Associates.mk p)) =
          QuotientGroup.mk' (toricUnitSubgroup P) (Algebra.GrothendieckGroup.of p)) ∧
      (∃ r : ℕ, Nonempty ((Algebra.GrothendieckGroup P ⧸ toricUnitSubgroup P) ≃*
        Multiplicative (Fin r → ℤ))) ∧
      ∃ (t : ℕ) (eU : Pˣ ≃* Multiplicative (Fin t → ℤ))
        (s : Associates P →* P) (eP : (Associates P × Pˣ) ≃* P)
        (eA : MonoidAlgebra k P ≃ₐ[k] toricLaurentAlgebra k (Associates P) t),
        (∀ q : Associates P, Associates.mk (s q) = q) ∧
        (∀ (q : Associates P) (u : Pˣ), eP (q, u) = s q * (u : P)) ∧
        (∀ (q : Associates P) (u : Pˣ),
          eA (MonoidAlgebra.of k P (s q * (u : P))) =
            MonoidAlgebra.single (eU u) (MonoidAlgebra.of k (Associates P) q)) ∧
        (∀ (p : Ideal (toricLaurentAlgebra k (Associates P) t)) [p.IsPrime],
          IsRegularLocalRing (Localization.AtPrime p)) ∧
        (toricLaurentVertexIdeal k (Associates P) t).IsMaximal ∧
        Nonempty ((toricLaurentAlgebra k (Associates P) t ⧸
          toricLaurentVertexIdeal k (Associates P) t) ≃ₐ[k] k) := by
  classical
  let := completion_torsionFree P hG
  let := hSmooth
  have hReg := IsRegular.of_smooth
    (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k P))))
  have hNoeth : IsLocallyNoetherian (Spec (.of (MonoidAlgebra k P))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k P))))
  have hsat := normal_monoid_saturation k P hP hReg
  let : Monoid.FG P := hP.1
  have hfsP : IsFineSaturatedMonoid P := by
    refine ⟨Monoid.FG.fg_top, hP.2, ?_⟩
    intro g n hn hg
    have hm : g ∈ FineFan.saturation
        (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := P))) :=
      Submonoid.subset_closure ⟨n, hn, hg⟩
    rw [hsat] at hm
    exact hm
  obtain ⟨hfs, htf, he, hr⟩ := fs_sharpening_data P hfsP
  let : IsMulTorsionFree (Algebra.GrothendieckGroup (Associates P)) := htf
  obtain ⟨t, _, s, hs, ⟨eP, heP⟩, ⟨eU⟩⟩ := FineFan.fine_monoid_unit_splitting P hP
  let eExp : P ≃* (Multiplicative (Fin t → ℤ) × Associates P) :=
    eP.symm.trans ((MulEquiv.prodCongr (MulEquiv.refl _) eU).trans MulEquiv.prodComm)
  let eA : MonoidAlgebra k P ≃ₐ[k] toricLaurentAlgebra k (Associates P) t :=
    (MonoidAlgebra.domCongr k k eExp).trans (MonoidAlgebra.curryAlgEquiv k)
  refine ⟨hsat, ⟨hNoeth, hReg⟩, hfs,
    (fun q hq ↦ (Associates.isUnit_iff_eq_one q).mp hq), he, hr,
    t, eU, s, eP, eA, hs, heP, ?_, ?_, laurent_vertex_residue k (Associates P)
      (fun q hq ↦ (Associates.isUnit_iff_eq_one q).mp hq) t⟩
  · intro q u
    rw [← heP q u]
    change eA (MonoidAlgebra.single (eP (q, u)) 1) =
      MonoidAlgebra.single (eU u) (MonoidAlgebra.single q 1)
    change (MonoidAlgebra.curryAlgEquiv k)
      ((MonoidAlgebra.domCongr k k eExp) (MonoidAlgebra.single (eP (q, u)) 1)) = _
    rw [MonoidAlgebra.domCongr_single]
    have hex : eExp (eP (q, u)) = (eU u, q) := by
      simp only [eExp, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rfl
    rw [hex, MonoidAlgebra.curryAlgEquiv_single]
  · intro p hp
    have := affine_regular_localizations (MonoidAlgebra k P) hReg
      (p.comap eA.toRingEquiv.toRingHom)
    exact IsRegularLocalRing.of_ringEquiv
      (Localization.localRingEquiv (p.comap eA.toRingEquiv.toRingHom) p
        eA.toRingEquiv rfl)

end AlgebraicGeometry
