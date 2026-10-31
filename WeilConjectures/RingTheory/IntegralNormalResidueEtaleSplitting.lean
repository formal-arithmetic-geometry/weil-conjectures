/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Étale splitting after an integral normal-residue extension

Source: Stacks Project, More on Morphisms, Tag 0BSR, specialized to algebraic normal
residue extensions with finite automorphism groups (blueprint:
lem-dl-a1-integral-normal-residue-etale-splitting).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

/-- An integral algebra with finitely many normal residue extensions of finite automorphism
 group splits after an étale base change into factors with one purely inseparable prime over
 the selected base prime, and every original prime over that base prime lifts. Source:
 Stacks Project, More on Morphisms, Tag 0BSR (blueprint:
 lem-dl-a1-integral-normal-residue-etale-splitting).

Proof:
1. Choose an algebraic closure Ω of κ(p) (`def-weil-algebraic-closure`) and a geometric
   point φ : C → Ω with kernel p. A point of R over φ factors uniquely through the
   residue field of its kernel. The integral geometric-point existence lemma
   (`lem-dl-a1-integral-geometric-point-existence`) supplies such points. By
   `Normal.algHomEquivAut` (`lem-sfb-normal-embeddings-automorphism-transitive`), the
   embeddings at each prime form a finite set. The finite fibre therefore gives a finite
   set I of geometric points, including the possibility I is empty.
2. Choose an element separating each pair of distinct points. The subalgebra D generated
   by these finitely many integral elements is finite over C by
   `Algebra.finite_adjoin_of_finite_of_isIntegral`
   (`lem-weil-pbc-finite-of-integral-generators`). Restriction I → J, the geometric points
   of D, is injective by separation. It is surjective by integral lying over
   (`lem-weil-pbc-integral-injective-lying-over`) and integral geometric-point existence
   for D → R. Thus it is a bijection, also for the empty family.
3. Apply `Algebra.exists_etale_completeOrthogonalIdempotents_forall_tensor_eq`
   (`lem-dl-a1-geometric-point-etale-idempotents`) to the finite algebra D. This yields an
   étale C-algebra A, α : A → Ω extending φ, and complete orthogonal idempotents indexed
   by J. Set p' = ker α. Push the idempotents to S = A ⊗[C] R and reindex by I. Tensor
   uniqueness (`lem-weil-pbc-algebra-tensor-pushout-universal-property`) shows that the
   evaluation F_u(a ⊗ r) = α(a)u(r) takes e_t to the Kronecker delta.
4. `Algebra.IsIntegral.tensorProduct` (`lem-weil-pbc-integral-base-change`) makes S integral
   over A. For each t use the quotient R_t = S/(1 - e_t), a model of the corner e_t S, as a
   factor. It is integral as a quotient of S. Orthogonality and the sum-one equation make
   the quotient maps S → ∏ t, R_t bijective (`CompleteOrthogonalIdempotents.bijective_pi`).
   If I is empty, S is the zero ring.
5. The evaluation F_t kills 1 - e_t and descends to a unital map R_t → Ω extending α. Every such map
   gives a geometric point u of R by tensor uniqueness. Its value on e_t forces u = t;
   hence the restricted map is unique. Integral geometric-point existence then implies
   that ker F_t is the unique prime of the factor over p'.
6. Apply `RingHom.PointsOver.isPurelyInseparable_of_forall_eq'`
   (`lem-dl-a1-unique-geometric-point-pure-residue`) to obtain pure inseparability for
   each factor. Given an original prime q over p, choose a geometric point t with kernel
   q. The prime ker F_t in S contracts to p' and q by its restrictions to A and R. Finally
   enumerate I by Fin m to obtain the displayed product.
-/
theorem exists_integral_normal_residue_etale_splitting
    (C : Type u) (R : Type v) [CommRing C] [CommRing R] [Algebra C R]
    [Algebra.IsIntegral C R] (p : Ideal C) [p.IsPrime]
    (hf : Set.Finite {q : Ideal R | q.IsPrime ∧
      q.comap (algebraMap C R) = p})
    (hres : ∀ (q : Ideal R) (_ : q.IsPrime)
      (hqp : q.comap (algebraMap C R) = p),
      @Normal p.ResidueField q.ResidueField _ _
          (Ideal.ResidueField.map p q (algebraMap C R) hqp.symm).toAlgebra ∧
        Finite (@AlgEquiv p.ResidueField q.ResidueField q.ResidueField _ _ _
          (Ideal.ResidueField.map p q (algebraMap C R) hqp.symm).toAlgebra
          (Ideal.ResidueField.map p q (algebraMap C R) hqp.symm).toAlgebra)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra C A),
      AlgebraicGeometry.Etale
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap C A))) ∧
      ∃ (p' : Ideal A) (_ : p'.IsPrime), p'.comap (algebraMap C A) = p ∧
      ∃ (m : ℕ) (Ri : Fin m → Type (max u v)) (_ : ∀ i, CommRing (Ri i))
        (_ : ∀ i, Algebra A (Ri i)),
        Nonempty (A ⊗[C] R ≃ₐ[A] (∀ i, Ri i)) ∧
        (∀ i, Algebra.IsIntegral A (Ri i) ∧
          ∃ (qi : Ideal (Ri i)) (_ : qi.IsPrime)
            (hqi : qi.comap (algebraMap A (Ri i)) = p'),
            (∀ qi' : Ideal (Ri i), qi'.IsPrime →
              qi'.comap (algebraMap A (Ri i)) = p' → qi' = qi) ∧
            (Ideal.ResidueField.map p' qi (algebraMap A (Ri i))
              hqi.symm).IsPurelyInseparable) ∧
        (∀ q : Ideal R, q.IsPrime → q.comap (algebraMap C R) = p →
          ∃ q' : Ideal (A ⊗[C] R), q'.IsPrime ∧
            q'.comap (algebraMap A (A ⊗[C] R)) = p' ∧
            q'.comap (Algebra.TensorProduct.includeRight (R := C) (A := A)
              (B := R)).toRingHom = q) := by
  classical
  let Ω := AlgebraicClosure p.ResidueField
  let φ : C →+* Ω := (algebraMap p.ResidueField Ω).comp (algebraMap C p.ResidueField)
  have hφ : RingHom.ker φ = p := by
    change RingHom.ker ((algebraMap p.ResidueField Ω).comp
      (algebraMap C p.ResidueField)) = p
    rw [RingHom.ker_comp_of_injective _ (algebraMap p.ResidueField Ω).injective,
      Ideal.ker_algebraMap_residueField]
  let I := RingHom.PointsOver φ R
  have hker (t : I) : (RingHom.ker t.1).comap (algebraMap C R) = p := by
    rw [RingHom.comap_ker, t.comp_algebraMap, hφ]
  have hfinite : Finite I := by
    apply Set.finite_univ_iff.mp
    refine Set.Finite.of_finite_fibers (fun t : I ↦ RingHom.ker t.1)
      (hf.subset ?_) ?_
    · rintro q ⟨t, _, rfl⟩
      exact ⟨inferInstance, hker t⟩
    · rintro q ⟨t₀, _, rfl⟩
      simp only [Set.univ_inter]
      change Finite {t : I // RingHom.ker t.1 = RingHom.ker t₀.1}
      let q := RingHom.ker t₀.1
      have hqp : q.comap (algebraMap C R) = p := hker t₀
      let f := Ideal.ResidueField.map p q (algebraMap C R) hqp.symm
      let : Algebra p.ResidueField q.ResidueField := f.toAlgebra
      have : Normal p.ResidueField q.ResidueField := (hres q inferInstance hqp).1
      have : Finite (q.ResidueField ≃ₐ[p.ResidueField] q.ResidueField) :=
        (hres q inferInstance hqp).2
      let liftPoint (t : I) (ht : RingHom.ker t.1 = q) :
          q.ResidueField →ₐ[p.ResidueField] Ω :=
        { t.residueFieldLift q ht with
          commutes' := by
            intro x
            have hh : (t.residueFieldLift q ht).comp f = algebraMap p.ResidueField Ω := by
              apply Ideal.ResidueField.ringHom_ext
              ext a
              simp only [RingHom.comp_apply, f, Ideal.ResidueField.map_algebraMap,
                RingHom.PointsOver.residueFieldLift_algebraMap,
                RingHom.PointsOver.apply_algebraMap]
              rfl
            exact RingHom.congr_fun hh x }
      let τ := liftPoint t₀ rfl
      let : Algebra q.ResidueField Ω := τ.toRingHom.toAlgebra
      have : IsScalarTower p.ResidueField q.ResidueField Ω :=
        IsScalarTower.of_algebraMap_eq fun x ↦ (τ.commutes x).symm
      have : Finite (q.ResidueField →ₐ[p.ResidueField] Ω) :=
        Finite.of_equiv _ (Normal.algHomEquivAut p.ResidueField Ω q.ResidueField).symm
      have hfin : Finite {t : I // RingHom.ker t.1 = q} := by
        apply Finite.of_injective (fun t ↦ liftPoint t.1 t.2)
        intro t t' he
        apply Subtype.ext
        exact RingHom.PointsOver.ext_of_residueFieldLift q t.2 t'.2
          (congrArg AlgHom.toRingHom he)
      exact hfin
  let : Fintype I := Fintype.ofFinite I
  have hsep (t t' : I) (h : t ≠ t') : ∃ r : R, t r ≠ t' r := by
    by_contra! hh
    exact h (RingHom.PointsOver.ext hh)
  let sep (z : I × I) : R := if h : z.1 = z.2 then 0 else (hsep z.1 z.2 h).choose
  have sep_ne (t t' : I) (h : t ≠ t') : t (sep (t, t')) ≠ t' (sep (t, t')) := by
    simpa only [sep, dif_neg h] using (hsep t t' h).choose_spec
  let D : Subalgebra C R := Algebra.adjoin C (Set.range sep)
  have : Module.Finite C D :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range sep)
      (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  let res : I → RingHom.PointsOver φ D := fun t ↦
    ⟨t.1.comp D.val.toRingHom, by
      ext c
      exact t.apply_algebraMap c⟩
  have hres_inj : Function.Injective res := by
    intro t t' hh
    by_contra hne
    apply sep_ne t t' hne
    exact congrArg
      (fun v : RingHom.PointsOver φ D ↦
        v ⟨sep (t, t'), Algebra.subset_adjoin ⟨(t, t'), rfl⟩⟩) hh
  have : Algebra.IsIntegral D R :=
    ⟨fun r ↦ (Algebra.IsIntegral.isIntegral (R := C) r).tower_top⟩
  have hres_surj : Function.Surjective res := by
    intro v
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective D R
      ⟨RingHom.ker v.1, inferInstance⟩
    have : q.asIdeal.LiesOver (RingHom.ker v.1) :=
      ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
    obtain ⟨t, _⟩ := RingHom.PointsOver.exists_ker_eq (φ := v.1) q.asIdeal
    let tC : I := ⟨t.1, by
      rw [IsScalarTower.algebraMap_eq C D R, ← RingHom.comp_assoc, t.comp_algebraMap,
        v.comp_algebraMap]⟩
    exact ⟨tC, Subtype.ext t.comp_algebraMap⟩
  let ε : I ≃ RingHom.PointsOver φ D := Equiv.ofBijective res ⟨hres_inj, hres_surj⟩
  let : Fintype (RingHom.PointsOver φ D) := Fintype.ofFinite _
  obtain ⟨A, _, _, _, α, hα, e, he, hval⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_tensor_eq (B := D) φ
  let S := A ⊗[C] R
  let f : A ⊗[C] D →ₐ[C] S :=
    Algebra.TensorProduct.map (AlgHom.id C A) D.val
  have hmap (t : I) (x : A ⊗[C] D) :
      (t.tensor hα) (f x) = ((res t).tensor hα) x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a d =>
      change (t.tensor hα) (a ⊗ₜ[C] (d : R)) =
        ((res t).tensor hα) (a ⊗ₜ[C] d)
      rw [RingHom.PointsOver.tensor_tmul, RingHom.PointsOver.tensor_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  let δ : I → S := fun t ↦ f (e (ε t))
  have hδ : CompleteOrthogonalIdempotents δ :=
    ((CompleteOrthogonalIdempotents.equiv ε).mpr he).map f.toRingHom
  have hδval (t t' : I) : (t'.tensor hα) (δ t) = if t' = t then 1 else 0 := by
    change (t'.tensor hα) (f (e (ε t))) = _
    rw [hmap]
    change ((ε t').tensor hα) (e (ε t)) = _
    rw [hval]
    simp only [Equiv.apply_eq_iff_eq]
  let J (t : I) : Ideal S := Ideal.span {1 - δ t}
  let Q (t : I) := S ⧸ J t
  have hQ (t : I) : Algebra.IsIntegral A (Q t) := inferInstance
  let π (t : I) : S →ₐ[A] Q t := Ideal.Quotient.mkₐ A (J t)
  let ψ : S ≃ₐ[A] ∀ t, Q t :=
    AlgEquiv.ofBijective (AlgHom.pi π) hδ.bijective_pi
  have hkill (t : I) : J t ≤ RingHom.ker (t.tensor hα).1 := by
    rw [Ideal.span_le]
    rintro x (rfl : x = 1 - δ t)
    change (t.tensor hα) (1 - δ t) = 0
    simp [hδval]
  let ft (t : I) : RingHom.PointsOver α (Q t) :=
    ⟨Ideal.Quotient.lift (J t) (t.tensor hα).1 (fun x hx ↦ hkill t hx), by
      ext a
      change (t.tensor hα) (algebraMap A S a) = α a
      exact (t.tensor hα).apply_algebraMap a⟩
  have hunique (t : I) (g : RingHom.PointsOver α (Q t)) : g = ft t := by
    let v : RingHom.PointsOver α S :=
      ⟨g.1.comp (π t).toRingHom, by
        ext a
        exact g.apply_algebraMap a⟩
    let u : I := RingHom.PointsOver.restrictTensor hα v
    have hv : v = u.tensor hα := (RingHom.PointsOver.tensorEquiv hα).symm_apply_apply v |>.symm
    have hve : v (δ t) = 1 := by
      have hz : π t (1 - δ t) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
      have heq : π t (δ t) = 1 := by
        rw [map_sub, map_one, sub_eq_zero] at hz
        exact hz.symm
      change g (π t (δ t)) = 1
      rw [heq, map_one]
    have hut : u = t := by
      by_contra h
      rw [hv, hδval, if_neg h] at hve
      exact zero_ne_one hve
    apply Subtype.ext
    apply RingHom.ext
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    change v s = (t.tensor hα) s
    rw [hv, hut]
  let p' := RingHom.ker α
  have hp' : p'.comap (algebraMap C A) = p := by
    rw [RingHom.comap_ker, hα, hφ]
  have hfactor (t : I) : Algebra.IsIntegral A (Q t) ∧
      ∃ (qi : Ideal (Q t)) (_ : qi.IsPrime)
        (hqi : qi.comap (algebraMap A (Q t)) = p'),
        (∀ qi' : Ideal (Q t), qi'.IsPrime →
          qi'.comap (algebraMap A (Q t)) = p' → qi' = qi) ∧
        (Ideal.ResidueField.map p' qi (algebraMap A (Q t))
          hqi.symm).IsPurelyInseparable := by
    let qi := RingHom.ker (ft t).1
    have hqi : qi.comap (algebraMap A (Q t)) = p' := (ft t).under_ker
    refine ⟨hQ t, qi, inferInstance, hqi, ?_, ?_⟩
    · intro qi' hprime hcomap
      have : qi'.LiesOver (RingHom.ker α) := ⟨hcomap.symm⟩
      obtain ⟨g, hg⟩ := RingHom.PointsOver.exists_ker_eq (φ := α) qi'
      rw [← hg, hunique t g]
    · exact RingHom.PointsOver.isPurelyInseparable_of_forall_eq' (ft t)
        (fun g _ ↦ hunique t g) p' rfl qi rfl hqi.symm
  have hlift (q : Ideal R) (hq : q.IsPrime) (hqp : q.comap (algebraMap C R) = p) :
      ∃ q' : Ideal S, q'.IsPrime ∧
        q'.comap (algebraMap A S) = p' ∧
        q'.comap (Algebra.TensorProduct.includeRight (R := C) (A := A)
          (B := R)).toRingHom = q := by
    have : q.LiesOver (RingHom.ker φ) := ⟨by rw [hφ]; exact hqp.symm⟩
    obtain ⟨t, ht⟩ := RingHom.PointsOver.exists_ker_eq (φ := φ) q
    refine ⟨RingHom.ker (t.tensor hα).1, inferInstance, (t.tensor hα).under_ker, ?_⟩
    rw [RingHom.PointsOver.ker_tensor_comap_includeRight, ht]
  let m := Fintype.card I
  let ι : Fin m ≃ I := (Fintype.equivFin I).symm
  refine ⟨A, inferInstance, inferInstance, ?_, p', inferInstance, hp', m,
    fun i ↦ Q (ι i), inferInstance, inferInstance, ?_, ?_, hlift⟩
  · exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  · exact ⟨ψ.trans (AlgEquiv.piCongrLeft A Q ι).symm⟩
  · exact fun i ↦ hfactor (ι i)

end Algebra
