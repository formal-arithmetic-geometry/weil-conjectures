/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes
public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.Blowup.Affine.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Rename
import Sheaf.RingTheory.ProjectiveOrderAlgebraAdditiveGenerators
import Sheaf.AlgebraicGeometry.NearPointOrderPresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Additive symmetry at a Hilbert--Samuel near point

Source: Cossart--Jannsen--Saito, March 12, 2009, Theorem 2.10(2) and the
characteristic-independent subgroup argument in the proof of Theorem 2.14, p.36;
Hironaka, Certain numerical characters of singularities, Theorem IV, and
Additive groups associated with points of a projective space, Theorem 2
(blueprint: lem-trf-near-point-additive-symmetry).

The prime of the exceptional-fibre point is constructed by its initial forms.
This uses the canonical quotient of the Rees algebra, without choosing a fibre
isomorphism. The tensor order is the existing `k tensor_A gr_I R` convention.
-/

@[expose] public section
set_option autoImplicit false

universe u v
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- The canonical residue-field extension at a blowup point over the closed point.
Transport first along the local-ring isomorphism at the closed point of Spec R,
then along the stated equality of points, and finally along the blowup morphism.
Source: CJS Theorem 2.10, residue extension k to k(y)
(blueprint: lem-trf-near-point-additive-symmetry). -/
@[instance_reducible]
noncomputable def nearPointResidueAlgebra {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (y : AffineBlowup I)
    (hy : AffineBlowup.toSpec I y = IsLocalRing.closedPoint R) :
    Algebra (IsLocalRing.ResidueField R) ((AffineBlowup I).residueField y) :=
  ((((Spec (.of R)).residueFieldCongr hy.symm).hom ≫
    (AffineBlowup.toSpec I).residueFieldMap y).hom.comp
      (IsLocalRing.ResidueField.mapEquiv
        (stalkClosedPointIso (.of R)).symm.commRingCatIsoToRingEquiv).toRingHom).toAlgebra

/-- The relative transcendence degree for the canonical extension k to k(y).
It is finite in the essentially finite type situation of the theorem below.
Source: CJS Theorem 2.10 (blueprint: lem-trf-near-point-additive-symmetry). -/
noncomputable def nearPointTrdeg {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (y : AffineBlowup I)
    (hy : AffineBlowup.toSpec I y = IsLocalRing.closedPoint R) : ℕ :=
  letI := nearPointResidueAlgebra I y hy
  Cardinal.toNat (Algebra.trdeg (IsLocalRing.ResidueField R)
    ((AffineBlowup I).residueField y))

/-- The homogeneous prime of y on the normal-cone fibre, presented by initial forms
of homogeneous Rees elements belonging to y. In degree n the canonical quotient
Rees/m Rees is I^n/m I^n; since I is contained in m, this is also the degree-n
piece of k tensor_(R/I) gr_I R. Thus the ideal span below is the image of y's
homogeneous prime under precisely that quotient, not an arbitrary point choice.
Source: CJS Theorem 2.2(2)(ii) and the fibre identification in Theorem 2.14
(blueprint: lem-trf-near-point-additive-symmetry). -/
noncomputable def nearPointFibreIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (y : AffineBlowup I) :
    Ideal (Ideal.normalConeFibre I hI) :=
  Ideal.span {z | ∃ (n : ℕ) (a : (I ^ n : Ideal R)),
    reesMonomial I a.val a.property ∈ y.asHomogeneousIdeal.toIdeal ∧
      z = Ideal.normalConeFibreClass I hI n a}


attribute [local instance] MvPolynomial.gradedAlgebra

private theorem additive_generators_symmetry
    {k : Type u} [Field k] (N : ℕ)
    (K q : Ideal (MvPolynomial (Fin N) k)) (hq : q ≠ ⊤)
    (T : Set (MvPolynomial (Fin N) k))
    (hThom : ∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t.IsHomogeneous d)
    (hTq : T ⊆ q)
    (hTadd : ∀ t ∈ T, MvPolynomial.aeval (fun i : Fin N ↦
        MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N) + MvPolynomial.X (Sum.inr i)) t =
      MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N) t +
        MvPolynomial.rename (Sum.inr : Fin N → Fin N ⊕ Fin N) t)
    (hK : K = Ideal.span {g | g ∈ K ∧ g ∈ Algebra.adjoin k T}) :
    ∃ L : Ideal (MvPolynomial (Fin N) k), L ≠ ⊤ ∧
      (∀ f ∈ L, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ L) ∧ L ≤ q ∧
      (∀ f ∈ L, MvPolynomial.eval (fun _ : Fin N ↦ (0 : k)) f = 0 ∧
        MvPolynomial.aeval (fun i : Fin N ↦
          -MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N)) f ∈
            L.map (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)).toRingHom ∧
        MvPolynomial.aeval (fun i : Fin N ↦
          MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N) + MvPolynomial.X (Sum.inr i)) f ∈
            L.map (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)).toRingHom ⊔
              L.map (MvPolynomial.rename (Sum.inr : Fin N → Fin N ⊕ Fin N)).toRingHom) ∧
      (∀ g ∈ K, MvPolynomial.aeval (fun i : Fin N ↦
          MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N) + MvPolynomial.X (Sum.inr i)) g ∈
            K.map (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)).toRingHom ⊔
              L.map (MvPolynomial.rename (Sum.inr : Fin N → Fin N ⊕ Fin N)).toRingHom) := by
  classical
  let L := Ideal.span T
  let z := MvPolynomial.rename (R := k) (Sum.inl : Fin N → Fin N ⊕ Fin N)
  let w := MvPolynomial.rename (R := k) (Sum.inr : Fin N → Fin N ⊕ Fin N)
  let a : MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin N ⊕ Fin N) k :=
    MvPolynomial.aeval (fun i : Fin N ↦
    MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N) + MvPolynomial.X (Sum.inr i))
  let neg : MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin N ⊕ Fin N) k :=
    MvPolynomial.aeval
    (fun i : Fin N ↦ -MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N))
  let D := L.map w.toRingHom
  have hLq : L ≤ q := Ideal.span_le.mpr hTq
  have hLhom : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) k) := by
    apply Ideal.homogeneous_span
    intro t ht
    obtain ⟨d, _, hd⟩ := hThom t ht
    exact ⟨d, hd⟩
  have hconst : ∀ t ∈ T, MvPolynomial.constantCoeff t = 0 := by
    intro t ht
    obtain ⟨d, hd, htd⟩ := hThom t ht
    exact htd.coeff_eq_zero (by simpa using Nat.ne_of_lt hd)
  have hzero : L ≤ RingHom.ker (MvPolynomial.eval (fun _ : Fin N ↦ (0 : k))) := by
    apply Ideal.span_le.mpr
    intro t ht
    change MvPolynomial.eval (fun _ : Fin N ↦ (0 : k)) t = 0
    simpa only [MvPolynomial.eval_zero'] using hconst t ht
  let s : MvPolynomial (Fin N ⊕ Fin N) k →ₐ[k]
      MvPolynomial (Fin N ⊕ Fin N) k := MvPolynomial.aeval
    (Sum.elim (fun i : Fin N ↦ MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N))
      (fun i : Fin N ↦ -MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N)))
  have hsa : s.comp a = MvPolynomial.aeval (fun _ : Fin N ↦
      (0 : MvPolynomial (Fin N ⊕ Fin N) k)) := by
    ext i
    simp [s, a]
  have hsz : s.comp z = z := by
    ext i
    simp [s, z]
  have hsw : s.comp w = neg := by
    ext i
    simp [s, w, neg]
  have hnegT : ∀ t ∈ T, neg t = -z t := by
    intro t ht
    have h : s (a t) = s (z t + w t) := congrArg s (hTadd t ht)
    have hz : MvPolynomial.C (MvPolynomial.constantCoeff t) = z t + neg t := by
      calc
        MvPolynomial.C (MvPolynomial.constantCoeff t) = (s.comp a) t := by
          rw [hsa, MvPolynomial.aeval_zero']
          rfl
        _ = s (z t + w t) := h
        _ = (s.comp z) t + (s.comp w) t := map_add s _ _
        _ = z t + neg t := by rw [hsz, hsw]
    rw [hconst t ht, MvPolynomial.C_0] at hz
    exact eq_neg_of_add_eq_zero_right hz.symm
  have hneg : L ≤ Ideal.comap neg.toRingHom (L.map z.toRingHom) := by
    apply Ideal.span_le.mpr
    intro t ht
    change neg t ∈ L.map z.toRingHom
    rw [hnegT t ht]
    exact (L.map z.toRingHom).neg_mem
      (Ideal.mem_map_of_mem z.toRingHom (Ideal.subset_span ht))
  have hadd : L ≤ Ideal.comap a.toRingHom (L.map z.toRingHom ⊔ D) := by
    apply Ideal.span_le.mpr
    intro t ht
    change a t ∈ L.map z.toRingHom ⊔ D
    rw [show a t = z t + w t from hTadd t ht]
    exact Ideal.add_mem _
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem z.toRingHom (Ideal.subset_span ht)))
      (Ideal.mem_sup_right (Ideal.mem_map_of_mem w.toRingHom (Ideal.subset_span ht)))
  let π := Ideal.Quotient.mkₐ k D
  have hcong : ∀ g ∈ Algebra.adjoin k T, π (a g) = π (z g) := by
    apply AlgHom.adjoin_le_equalizer (π.comp a) (π.comp z)
    intro t ht
    change π (a t) = π (z t)
    rw [show a t = z t + w t from hTadd t ht, map_add]
    have hw : π (w t) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem w.toRingHom (Ideal.subset_span ht))
    rw [hw, add_zero]
  have haction : K ≤ Ideal.comap a.toRingHom (K.map z.toRingHom ⊔ D) := by
    conv_lhs => rw [hK]
    apply Ideal.span_le.mpr
    rintro g ⟨hgK, hgU⟩
    change a g ∈ K.map z.toRingHom ⊔ D
    have hd : a g - z g ∈ D := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (hcong g hgU)
    have hz : z g ∈ K.map z.toRingHom ⊔ D :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem z.toRingHom hgK)
    have hd' : a g - z g ∈ K.map z.toRingHom ⊔ D := Ideal.mem_sup_right hd
    simpa only [sub_add_cancel] using Ideal.add_mem _ hd' hz
  refine ⟨L, ne_top_of_le_ne_top hq hLq, ?_, hLq, ?_, ?_⟩
  · exact fun f hf n ↦ MvPolynomial.homogeneousComponent_mem_of_mem hLhom hf n
  · intro f hf
    exact ⟨hzero hf, hneg hf, hadd hf⟩
  · exact fun g hg ↦ haction hg

/-- A near point lies on the projectivization of a homogeneous additive subgroup
whose translations preserve the normal-cone equations. No characteristic restriction
or degree-one generation of the subgroup ideal is imposed.
Source: CJS Theorem 2.10(2), Theorem 2.14, p.36, before its linearity argument;
Hironaka Theorem IV and Additive groups, Theorem 2
(blueprint: lem-trf-near-point-additive-symmetry).

Proof, following the node's six steps:
1. Split the degree-one kernel of the presentation by a basis V and lift a basis X
   of the fibre's degree-one part. Then P=Q[V], K=(V)+JP and q_y=(V)+q_0 P.
   Evaluation at V=0 proves both ideal identities. The invertible linear change
   commutes with addition, inversion and zero, so it can be undone at the end.
2. Apply lem-trf-near-blowup-order-generators to the minimal presentation Q onto S.
   Its hypotheses are exactly the local algebra, regular prime centre, normal flatness,
   non-component condition and raw near equality here. Its homogeneous generators H
   of J have local order at least their degree. Apply
   lem-trf-projective-order-algebra-additive-generators to the relevant homogeneous
   prime q_y: the algebra U of degree-d forms having local order at least d is k[T],
   where T consists of its positive-degree homogeneous additive polynomials.
3. The local map Q_(q_0) to P_(q_y) takes powers of the maximal ideal into their
   corresponding powers. Hence those H, as well as each redundant variable V, lie
   in U. Together they generate K. No equality of orders after field extension is used.
4. Set L=(T). Decomposing coefficients into homogeneous components shows L is homogeneous.
   Positive local order implies t lies in q_y: clear a denominator outside the prime
   and use primality. Thus L is contained in q_y and is proper. Positive degree gives
   t(0)=0, and the same holds for every finite sum of multiples of these generators.
5. Additivity gives t(Z+W)=t(Z)+t(W) and t(-Z)=-t(Z). Substitution in a finite sum
   of multiples of t proves the inversion and addition ideal memberships for every f in L.
6. Modulo L(W), each t(Z+W)=t(Z), hence the same identity holds for every u in U=k[T].
   Express g in K as a finite sum of multiples of the generators H and V from step 3.
   Substitution reduces it modulo L(W) to a sum of multiples of their values at Z,
   which belongs to K(Z). Undo the linear change from step 1. These are polynomial
   identities in disjoint tuples, including over finite and imperfect fields. -/
theorem near_point_additive_symmetry
    {F : Type v} [Field F] {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsReduced R] [Algebra F R]
    [Algebra.EssFiniteType F R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) [I.IsPrime]
    [IsRegularLocalRing (R ⧸ I)]
    (hcomponents : ∀ p ∈ minimalPrimes R, ¬ I ≤ p)
    [Module.Flat (R ⧸ I) (Ideal.associatedGraded I)]
    (y : AffineBlowup I)
    (hy : AffineBlowup.toSpec I y = IsLocalRing.closedPoint R)
    (hnear : (summation^[nearPointTrdeg I y hy]) (localFunction (AffineBlowup I) y) =
      fun n : ℕ ↦ (Module.length R
        (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))).toNat)
    (N : ℕ)
    (φ : MvPolynomial (Fin N) (IsLocalRing.ResidueField R) →ₐ[IsLocalRing.ResidueField R]
      Ideal.normalConeFibre I hI)
    (hφ : Function.Surjective φ)
    (hgraded : ∀ i : Fin N, φ (MvPolynomial.X i) ∈
      Submodule.span (IsLocalRing.ResidueField R)
        (Set.range (Ideal.normalConeFibreClass I hI 1))) :
    ∃ L : Ideal (MvPolynomial (Fin N) (IsLocalRing.ResidueField R)),
      L ≠ ⊤ ∧
      (∀ f ∈ L, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ L) ∧
      L ≤ Ideal.comap φ.toRingHom (nearPointFibreIdeal I hI y) ∧
      (∀ f ∈ L,
        MvPolynomial.eval (fun _ : Fin N ↦ (0 : IsLocalRing.ResidueField R)) f = 0 ∧
        MvPolynomial.aeval (fun i : Fin N ↦
          -MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N)) f ∈
            L.map (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)).toRingHom ∧
        MvPolynomial.aeval (fun i : Fin N ↦
          MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N) + MvPolynomial.X (Sum.inr i)) f ∈
            L.map (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)).toRingHom ⊔
              L.map (MvPolynomial.rename (Sum.inr : Fin N → Fin N ⊕ Fin N)).toRingHom) ∧
      (∀ g ∈ RingHom.ker φ.toRingHom,
        MvPolynomial.aeval (fun i : Fin N ↦
          MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N) + MvPolynomial.X (Sum.inr i)) g ∈
            (RingHom.ker φ.toRingHom).map
              (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)).toRingHom ⊔
              L.map (MvPolynomial.rename (Sum.inr : Fin N → Fin N ⊕ Fin N)).toRingHom) := by
  classical
  let q := Ideal.comap φ.toRingHom (nearPointFibreIdeal I hI y)
  obtain ⟨hN, hq, hqhom, hrel, hK⟩ :=
    near_point_order_presentation (F := F) I hI hcomponents y hy hnear N φ hφ hgraded
  let : q.IsPrime := hq
  have hqh : q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) (IsLocalRing.ResidueField R)) := by
    intro d f hf
    change (MvPolynomial.decomposition.decompose' f d :
      MvPolynomial (Fin N) (IsLocalRing.ResidueField R)) ∈ q
    rw [MvPolynomial.decomposition.decompose'_apply]
    exact hqhom f hf d
  obtain ⟨U, hU, _, hUgen⟩ :=
    Hironaka.projective_order_algebra_additive_generators N hN q hqh hrel
  let T := {t : MvPolynomial (Fin N) (IsLocalRing.ResidueField R) |
    t ∈ U ∧ (∃ d : ℕ, 0 < d ∧ t.IsHomogeneous d) ∧
      MvPolynomial.aeval (fun i : Fin N ↦
        MvPolynomial.X (Sum.inl i : Fin N ⊕ Fin N) + MvPolynomial.X (Sum.inr i)) t =
      MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N) t +
        MvPolynomial.rename (Sum.inr : Fin N → Fin N ⊕ Fin N) t}
  have hTq : T ⊆ q := by
    intro t ht
    obtain ⟨d, hd, htd⟩ := ht.2.1
    have ho := (hU t).mp ht.1 d
    rw [MvPolynomial.homogeneousComponent_eq_self htd] at ho
    have hm := Ideal.pow_le_self (Nat.ne_of_gt hd) ho
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)] at hm
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q t).mp hm
  have hKU : RingHom.ker φ.toRingHom = Ideal.span
      {g | g ∈ RingHom.ker φ.toRingHom ∧ g ∈ Algebra.adjoin (IsLocalRing.ResidueField R) T} := by
    apply le_antisymm
    · calc
        RingHom.ker φ.toRingHom = _ := hK
        _ ≤ _ := by
          apply Ideal.span_le.mpr
          rintro H ⟨hH, d, hd, hhom, horder⟩
          apply Ideal.subset_span
          refine ⟨hH, ?_⟩
          rw [← hUgen]
          apply (hU H).mpr
          intro n
          rw [MvPolynomial.homogeneousComponent_of_mem hhom]
          split_ifs with hn
          · subst n
            exact horder
          · simp
    · exact Ideal.span_le.mpr fun g hg ↦ hg.1
  exact additive_generators_symmetry N (RingHom.ker φ.toRingHom) q
    (Ideal.IsPrime.ne_top hq) T (fun t ht ↦ ht.2.1) hTq (fun t ht ↦ ht.2.2) hKU

end AlgebraicGeometry.HilbertSamuel
