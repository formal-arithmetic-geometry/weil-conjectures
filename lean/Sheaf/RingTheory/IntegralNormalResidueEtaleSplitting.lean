/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.PurelyInseparable
import Sheaf.FieldTheory.NormalFiniteAutSeparableSubfield
import Sheaf.RingTheory.IntegralFiniteResidueModel
import WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting

/-!
# Étale splitting for integral algebras with normal residue extensions

Source: Stacks Project, More on Morphisms, Tag 0BSR,
`lemma-etale-makes-integral-split`, and Fundamental Groups, Tag 0BST,
`lemma-inertia-invariants-etale`, second reduction paragraph
(blueprint: lem-dl-a1-integral-normal-residue-etale-splitting).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

private theorem residue_maps_agree_on_model
    {C D Ω : Type*} [CommRing C] [CommRing D] [Field Ω]
    (f : C →+* D) (t₁ t₂ : D →+* Ω) (ht : t₁.comp f = t₂.comp f)
    (r : Ideal D) [r.IsPrime] (h₁ : RingHom.ker t₁ = r) (h₂ : RingHom.ker t₂ = r) :
    let s := r.comap f
    let ψ := Ideal.ResidueField.map s r f rfl
    let ι₁ := Ideal.ResidueField.lift r t₁ h₁.ge (fun x hx ↦
      (IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.mpr (by
        simpa [Ideal.primeCompl, ← h₁, RingHom.mem_ker] using hx)))
    let ι₂ := Ideal.ResidueField.lift r t₂ h₂.ge (fun x hx ↦
      (IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.mpr (by
        simpa [Ideal.primeCompl, ← h₂, RingHom.mem_ker] using hx)))
    ι₁.comp ψ = ι₂.comp ψ := by
  dsimp only
  apply Ideal.ResidueField.ringHom_ext
  ext c
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap,
    Ideal.ResidueField.lift_algebraMap]
  exact RingHom.congr_fun ht c

private theorem field_maps_eq_of_range
    {k E K Ω : Type*} [Field k] [Field E] [Field K] [Field Ω] [Algebra k E]
    (L : IntermediateField k E) [IsPurelyInseparable L E]
    (ψ : K →+* E) (hL : L.toSubfield = ψ.fieldRange)
    (ι₁ ι₂ : E →+* Ω) (h : ι₁.comp ψ = ι₂.comp ψ) : ι₁ = ι₂ := by
  apply IsPurelyInseparable.injective_comp_algebraMap L E Ω
  ext x
  obtain ⟨y, hy⟩ := show (x : E) ∈ ψ.fieldRange from hL ▸ x.property
  change ι₁ (x : E) = ι₂ (x : E)
  rw [← hy]
  exact RingHom.congr_fun h y

private theorem points_restrict_injective
    {A : Type u} {D Ω : Type*} [CommRing A] [CommRing D] [Field Ω]
    [Algebra A D] (p : PrimeSpectrum A) (C : Subalgebra A D)
    (hbij : Set.InjOn (fun r : Ideal D ↦ r.comap C.val) (p.asIdeal.primesOver D))
    (L : ∀ r : p.asIdeal.primesOver D,
      @IntermediateField p.asIdeal.ResidueField r.1.ResidueField _ _
        (Ideal.ResidueField.map p.asIdeal r.1 (algebraMap A D)
          (r.1.over_def p.asIdeal)).toAlgebra)
    (hL : ∀ r, (@IntermediateField.toSubfield _ _ _ _
      (Ideal.ResidueField.map p.asIdeal r.1 (algebraMap A D)
        (r.1.over_def p.asIdeal)).toAlgebra (L r)) =
        (Ideal.ResidueField.map (r.1.comap C.val) r.1 C.val rfl).fieldRange)
    (hpure : ∀ r, IsPurelyInseparable (L r) r.1.ResidueField)
    (φ : A →+* Ω) (hφ : RingHom.ker φ = p.asIdeal)
    (t₁ t₂ : RingHom.PointsOver φ D)
    (ht : t₁.1.comp C.val.toRingHom = t₂.1.comp C.val.toRingHom) : t₁ = t₂ := by
  have hmem (t : RingHom.PointsOver φ D) : RingHom.ker t.1 ∈ p.asIdeal.primesOver D := by
    refine ⟨RingHom.ker_isPrime _, ⟨?_⟩⟩
    rw [Ideal.under, RingHom.comap_ker, t.property, hφ]
  let r : p.asIdeal.primesOver D := ⟨RingHom.ker t₁.1, hmem t₁⟩
  have hr : RingHom.ker t₂.1 = r.val := by
    apply hbij (hmem t₂) (hmem t₁)
    ext c
    change t₂.1 (C.val c) = 0 ↔ t₁.1 (C.val c) = 0
    rw [show t₁.1 (C.val c) = t₂.1 (C.val c) from RingHom.congr_fun ht c]
  have : r.val.LiesOver p.asIdeal := r.property.2
  let ι₁ := t₁.residueFieldLift r.val rfl
  let ι₂ := t₂.residueFieldLift r.val hr
  have hι : ι₁ = ι₂ := by
    let := (Ideal.ResidueField.map p.asIdeal r.val (algebraMap A D)
      (r.val.over_def p.asIdeal)).toAlgebra
    have := hpure r
    apply field_maps_eq_of_range (L r)
      (Ideal.ResidueField.map (r.val.comap C.val) r.val C.val rfl) (hL r)
    exact residue_maps_agree_on_model C.val.toRingHom t₁.1 t₂.1 ht r.val rfl hr
  exact RingHom.PointsOver.ext_of_residueFieldLift r.val rfl hr hι

private theorem points_restrict_surjective
    {A D Ω : Type*} [CommRing A] [CommRing D] [Field Ω] [IsAlgClosed Ω]
    [Algebra A D] (C : Subalgebra A D) [Algebra.IsIntegral C D]
    (φ : A →+* Ω) (s : RingHom.PointsOver φ C) :
    ∃ t : RingHom.PointsOver φ D, t.1.comp C.val.toRingHom = s.1 := by
  obtain ⟨r, hr⟩ := Algebra.IsIntegral.comap_surjective C D
    (⟨RingHom.ker s.1, RingHom.ker_isPrime _⟩ : PrimeSpectrum C)
  have : r.asIdeal.LiesOver (RingHom.ker s.1) :=
    ⟨(congrArg PrimeSpectrum.asIdeal hr).symm⟩
  obtain ⟨t, _⟩ := RingHom.PointsOver.exists_ker_eq (φ := s.1) r.asIdeal
  refine ⟨⟨t.1, ?_⟩, t.property⟩
  rw [IsScalarTower.algebraMap_eq A C D, ← RingHom.comp_assoc, t.property]
  exact s.property

private theorem integral_factors_of_geometric_idempotents
    {B : Type*} {T : Type v} {Ω I : Type*} [CommRing B] [CommRing T]
    [Field Ω] [IsAlgClosed Ω] [Algebra B T] [Algebra.IsIntegral B T] [Fintype I]
    (φ : B →+* Ω) (e : I → T) (he : CompleteOrthogonalIdempotents e)
    (t : I → RingHom.PointsOver φ T) (ht : ∀ i, t i (e i) = 1)
    (huniq : ∀ i (t' : RingHom.PointsOver φ T), t' (e i) = 1 → t' = t i) :
    ∃ (Dj : I → Type v) (_ : ∀ i, CommRing (Dj i)) (_ : ∀ i, Algebra B (Dj i))
      (E : T ≃ₐ[B] ∀ i, Dj i) (qj : ∀ i, PrimeSpectrum (Dj i))
      (hlying : ∀ i, PrimeSpectrum.comap (algebraMap B (Dj i)) (qj i) =
        ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩),
      (∀ i, Algebra.IsIntegral B (Dj i)) ∧
      (∀ i (r : PrimeSpectrum (Dj i)), PrimeSpectrum.comap (algebraMap B (Dj i)) r =
        ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩ → r = qj i) ∧
      (∀ i, (Ideal.ResidueField.map (RingHom.ker φ) (qj i).asIdeal
        (algebraMap B (Dj i)) (congrArg PrimeSpectrum.asIdeal (hlying i)).symm
        ).IsPurelyInseparable) ∧
      ∀ i, (qj i).asIdeal.comap ((Pi.evalRingHom Dj i).comp E.toRingHom) =
        RingHom.ker (t i).1 := by
  classical
  let J (i : I) : Ideal T := Ideal.span {1 - e i}
  let Dj (i : I) := T ⧸ J i
  let π (i : I) : T →ₐ[B] Dj i := Ideal.Quotient.mkₐ B (J i)
  have hJ (i : I) : J i ≤ RingHom.ker (t i).1 := by
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change (t i).1 (1 - e i) = 0
    rw [map_sub, map_one, ht, sub_self]
  let τ (i : I) : RingHom.PointsOver φ (Dj i) :=
    ⟨Ideal.Quotient.lift (J i) (t i).1 (hJ i), by
      ext b
      exact (t i).apply_algebraMap b⟩
  have hτ (i : I) : (τ i).1.comp (π i).toRingHom = (t i).1 := by
    ext x
    rfl
  let E : T ≃ₐ[B] ∀ i, Dj i :=
    AlgEquiv.ofBijective (AlgHom.pi π) he.bijective_pi
  let qj (i : I) : PrimeSpectrum (Dj i) := ⟨RingHom.ker (τ i).1, RingHom.ker_isPrime _⟩
  have hlying (i : I) : PrimeSpectrum.comap (algebraMap B (Dj i)) (qj i) =
      ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩ := by
    apply PrimeSpectrum.ext
    exact (τ i).under_ker
  have hτuniq (i : I) (z : RingHom.PointsOver φ (Dj i)) : z = τ i := by
    let z' : RingHom.PointsOver φ T :=
      ⟨z.1.comp (π i).toRingHom, by ext b; exact z.apply_algebraMap b⟩
    have hπe : π i (e i) = 1 := by
      have hzero : π i (1 - e i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
      rw [map_sub, map_one, sub_eq_zero] at hzero
      exact hzero.symm
    have hz' : z' = t i := huniq i z' (by change z.1 (π i (e i)) = 1; rw [hπe, map_one])
    apply Subtype.ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun z : RingHom.PointsOver φ T ↦ z x) hz'
  refine ⟨Dj, inferInstance, inferInstance, E, qj, hlying, fun _ ↦ inferInstance, ?_, ?_, ?_⟩
  · intro i r hr
    have : r.asIdeal.LiesOver (RingHom.ker φ) :=
      ⟨(congrArg PrimeSpectrum.asIdeal hr).symm⟩
    obtain ⟨z, hz⟩ := RingHom.PointsOver.exists_ker_eq (φ := φ) r.asIdeal
    apply PrimeSpectrum.ext
    exact hz.symm.trans (congrArg (fun z ↦ RingHom.ker z.1) (hτuniq i z))
  · intro i
    exact (τ i).isPurelyInseparable_of_forall_eq' (fun z _ ↦ hτuniq i z)
      (RingHom.ker φ) rfl (qj i).asIdeal rfl
      (congrArg PrimeSpectrum.asIdeal (hlying i)).symm
  · intro i
    change (RingHom.ker (τ i).1).comap (π i).toRingHom = _
    rw [RingHom.comap_ker, hτ]

/-- An integral algebra with finite fibre and normal algebraic residue extensions with
finite automorphism groups splits after an étale base change into integral factors with
singleton, purely inseparable fibres. The prescribed prime lifts to the first factor.
`Normal` includes algebraicity. Every residue algebra structure below is the canonical map
induced by contraction; `Ideal.ResidueField` is the fraction field of the prime quotient.

Source: Stacks Project, Tags 0BSR and 0BST, second reduction paragraph
(blueprint: lem-dl-a1-integral-normal-residue-etale-splitting).

Proof plan:
1. Enumerate the finite fibre. For each residue extension E/k,
   `lem-dl-a1-normal-finite-aut-separable-subfield` gives a finite-dimensional separable
   subfield F. By `lem-weil-pbc-separable-first-purely-inseparable`, E/F is purely inseparable.
   This does not assert that E/k is finite-dimensional.
2. Apply `lem-dl-a1-integral-finite-residue-model`: choose a module-finite intermediate
   algebra C in D, with D integral over C, bijective contraction on the fibre, finite residue
   fields L over k, and E/L purely inseparable.
3. Apply `lem-weil-pbc-integral-fibre-etale-splitting` to Spec C over Spec A. This gives an
   affine étale neighbourhood Spec B and a clopen partition into factors C_j with singleton
   purely inseparable fibres. Use `def-weil-finite-integral-morphism` and
   `lem-weil-pbc-fibre-product-affine-spectra` to identify this base change with B tensor C.
4. By `lem-weil-pbc-integral-base-change`, B tensor D is integral over B. The clopen pieces
   give orthogonal idempotents summing to one (`lem-weil-pbc-spec-clopen-idempotent`).
   Their images e_j give factors D_j = e_j (B tensor D), with identity e_j. The maps
   x to (e_j x)_j and (x_j)_j to sum x_j are inverse B-algebra maps. The factors are quotients,
   so monic integral equations descend to them.
5. For each C_j fibre point t_j, the finite-model fibre bijection selects a unique original
   prime with residue E over L. Use `lem-weil-pbc-fibre-product-affine-spectra` over C and
   `lem-weil-pbc-fibre-product-points` to identify its remaining fibre with Spec of
   E tensor_L kappa(t_j). It has a prime by
   `lem-weil-common-extension-fields-tensor-nontrivial` and
   `lem-weil-common-extension-fields-maximal-ideal`. The purely inseparable map Spec E to
   Spec L is universally injective (`def-weil-radicial-morphism`), so this prime is unique.
6. Universal injectivity persists under further base change; its radicial characterization
   and `lem-weil-pbc-fibre-product-point-residue-field` show that kappa(q_j)/kappa(t_j) is
   purely inseparable. Combine with kappa(t_j)/kappa(p'): in characteristic p, compose the
   p-power exponents; in characteristic zero both extensions are trivial.
7. Lift the specified q using a prime of kappa(q) tensor_k kappa(p'), again by nontriviality
   and maximal-ideal existence, and the affine pullback and point correspondences. Exactly
   one factor idempotent survives at this prime, since they are orthogonal and sum to one.
   Thus the number of factors is positive. Permute them to put this factor first. Its unique
   prime over p' is the indicated q_j, giving the asserted contraction formula. -/
theorem exists_integral_normal_residue_etale_splitting
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.IsIntegral A D] (p : PrimeSpectrum A) (q : PrimeSpectrum D)
    (hq : PrimeSpectrum.comap (algebraMap A D) q = p)
    (hfibre : Set.Finite {r : PrimeSpectrum D |
      PrimeSpectrum.comap (algebraMap A D) r = p})
    (hnormal : ∀ (r : PrimeSpectrum D)
      (hr : PrimeSpectrum.comap (algebraMap A D) r = p),
      @Normal p.asIdeal.ResidueField r.asIdeal.ResidueField _ _
        (Ideal.ResidueField.map p.asIdeal r.asIdeal (algebraMap A D)
          (congrArg PrimeSpectrum.asIdeal hr).symm).toAlgebra)
    (hauto : ∀ (r : PrimeSpectrum D)
      (hr : PrimeSpectrum.comap (algebraMap A D) r = p),
      Finite (@AlgEquiv p.asIdeal.ResidueField r.asIdeal.ResidueField r.asIdeal.ResidueField
        _ _ _
        (Ideal.ResidueField.map p.asIdeal r.asIdeal (algebraMap A D)
          (congrArg PrimeSpectrum.asIdeal hr).symm).toAlgebra
        (Ideal.ResidueField.map p.asIdeal r.asIdeal (algebraMap A D)
          (congrArg PrimeSpectrum.asIdeal hr).symm).toAlgebra)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      AlgebraicGeometry.Etale
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
      ∃ (p' : PrimeSpectrum B), PrimeSpectrum.comap (algebraMap A B) p' = p ∧
      ∃ (q' : PrimeSpectrum (B ⊗[A] D)),
        PrimeSpectrum.comap (Algebra.TensorProduct.includeRight.toRingHom) q' = q ∧
        PrimeSpectrum.comap (algebraMap B (B ⊗[A] D)) q' = p' ∧
      ∃ (n : ℕ) (hn : 0 < n) (Dj : Fin n → Type (max u v))
        (_ : ∀ j, CommRing (Dj j)) (_ : ∀ j, Algebra B (Dj j))
        (e : (B ⊗[A] D) ≃ₐ[B] (∀ j, Dj j))
        (qj : ∀ j, PrimeSpectrum (Dj j))
        (hlying : ∀ j, PrimeSpectrum.comap (algebraMap B (Dj j)) (qj j) = p'),
        (∀ j, Algebra.IsIntegral B (Dj j)) ∧
        (∀ (j : Fin n) (r : PrimeSpectrum (Dj j)),
          PrimeSpectrum.comap (algebraMap B (Dj j)) r = p' → r = qj j) ∧
        (∀ j, (Ideal.ResidueField.map p'.asIdeal (qj j).asIdeal
          (algebraMap B (Dj j)) (congrArg PrimeSpectrum.asIdeal (hlying j)).symm
          ).IsPurelyInseparable) ∧
        q'.asIdeal = ((qj ⟨0, hn⟩).asIdeal.comap
          ((Pi.evalRingHom Dj ⟨0, hn⟩).comp e.toRingHom))  := by
  classical
  have hp : p.asIdeal.IsPrime := p.isPrime
  have hprimes : (p.asIdeal.primesOver D).Finite := by
    apply (hfibre.image PrimeSpectrum.asIdeal).subset
    intro r hr
    have : r.IsPrime := hr.1
    refine ⟨⟨r, hr.1⟩, ?_, rfl⟩
    exact PrimeSpectrum.ext hr.2.over.symm
  let R := p.asIdeal.primesOver D
  let a (r : R) : Algebra p.asIdeal.ResidueField r.val.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal r.val (algebraMap A D)
      (r.val.over_def p.asIdeal)).toAlgebra
  let F (r : R) : @IntermediateField p.asIdeal.ResidueField r.val.ResidueField _ _ (a r) :=
    @separableClosure p.asIdeal.ResidueField r.val.ResidueField _ _ (a r)
  have hnormal' (r : R) : @Normal p.asIdeal.ResidueField r.val.ResidueField _ _ (a r) := by
    let z : PrimeSpectrum D := ⟨r.val, r.property.1⟩
    have hz : PrimeSpectrum.comap (algebraMap A D) z = p :=
      PrimeSpectrum.ext (r.val.over_def p.asIdeal).symm
    exact hnormal z hz
  have hauto' (r : R) : @Finite
      (@AlgEquiv p.asIdeal.ResidueField r.val.ResidueField r.val.ResidueField _ _ _
        (a r) (a r)) := by
    exact hauto ⟨r.val, r.property.1⟩
      (PrimeSpectrum.ext (r.val.over_def p.asIdeal).symm)
  obtain ⟨C, hC, hbij, ⟨L, hL⟩, hCD⟩ := exists_integral_finite_residue_model p.asIdeal hprimes F
    (fun r ↦ by
      let := a r
      let := hnormal' r
      let := hauto' r
      exact separableClosure.finiteDimensional_of_normal_of_finite_aut _ _)
    (fun r ↦ by let := a r; exact separableClosure.isSeparable _ _)
    (fun r ↦ by
      let := a r
      let := hnormal' r
      have : Algebra.IsAlgebraic p.asIdeal.ResidueField r.val.ResidueField :=
        ⟨fun x ↦ (hnormal' r).isIntegral x |>.isAlgebraic⟩
      exact separableClosure.isPurelyInseparable _ _)
  let := hCD
  let Ω := AlgebraicClosure q.asIdeal.ResidueField
  let tq₀ : D →+* Ω := (algebraMap q.asIdeal.ResidueField Ω).comp
    (algebraMap D q.asIdeal.ResidueField)
  let φ : A →+* Ω := tq₀.comp (algebraMap A D)
  have htq : RingHom.ker tq₀ = q.asIdeal := by
    ext d
    simp [tq₀, RingHom.mem_ker, Ideal.algebraMap_residueField_eq_zero]
  have hφ : RingHom.ker φ = p.asIdeal := by
    rw [← RingHom.comap_ker, htq]
    exact congrArg PrimeSpectrum.asIdeal hq
  let tq : RingHom.PointsOver φ D := ⟨tq₀, rfl⟩
  let rest : RingHom.PointsOver φ D → RingHom.PointsOver φ C := fun t ↦
    ⟨t.1.comp C.val.toRingHom, by
      ext a
      change t.1 (algebraMap A D a) = φ a
      exact t.apply_algebraMap a⟩
  have hrest : Function.Bijective rest := by
    refine ⟨fun t₁ t₂ ht ↦ points_restrict_injective p C hbij.2.1 L
      (fun r ↦ (hL r).1) (fun r ↦ (hL r).2.2.2) φ hφ t₁ t₂
      (congrArg Subtype.val ht), ?_⟩
    intro t
    obtain ⟨z, hz⟩ := points_restrict_surjective C φ t
    exact ⟨z, Subtype.ext hz⟩
  let := hC
  let I := RingHom.PointsOver φ C
  let : Fintype I := Fintype.ofFinite I
  let ρ : RingHom.PointsOver φ D ≃ I := Equiv.ofBijective rest hrest
  obtain ⟨B, cB, aB, hB, φB, hφB, ε, hε, hval⟩ :=
    exists_etale_completeOrthogonalIdempotents_forall_tensor_eq (B := C) φ
  let := cB
  let := aB
  have := hB
  let f : (B ⊗[A] C) →ₐ[A] (B ⊗[A] D) :=
    Algebra.TensorProduct.map (AlgHom.id A B) C.val
  have hval' (t : RingHom.PointsOver φ D) (x : B ⊗[A] C) :
      t.tensor hφB (f x) = (rest t).tensor hφB x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => simp [f, rest, RingHom.PointsOver.tensor_tmul]
    | add x y hx hy => simp [hx, hy]
  have hn : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨rest tq⟩
  let b : Fin (Fintype.card I) ≃ I :=
    (Equiv.swap ⟨0, hn⟩ (Fintype.equivFin I (rest tq))).trans (Fintype.equivFin I).symm
  have hb : b ⟨0, hn⟩ = rest tq := by simp [b]
  let e : Fin (Fintype.card I) → B ⊗[A] D := fun i ↦ f (ε (b i))
  have he : CompleteOrthogonalIdempotents e :=
    ((CompleteOrthogonalIdempotents.equiv b).mpr hε).map f.toRingHom
  let t : Fin (Fintype.card I) → RingHom.PointsOver φB (B ⊗[A] D) :=
    fun i ↦ (ρ.symm (b i)).tensor hφB
  have ht (i) : t i (e i) = 1 := by
    change (ρ.symm (b i)).tensor hφB (f (ε (b i))) = 1
    rw [hval']
    have hr : rest (ρ.symm (b i)) = b i := ρ.apply_symm_apply _
    rw [hr, hval]
    simp
  have huniq (i) (z : RingHom.PointsOver φB (B ⊗[A] D)) (hz : z (e i) = 1) : z = t i := by
    obtain ⟨z, rfl⟩ := (RingHom.PointsOver.tensorEquiv hφB).symm.surjective z
    have hz' : rest z = b i := by
      change z.tensor hφB (f (ε (b i))) = 1 at hz
      rw [hval', hval] at hz
      split_ifs at hz with hh
      · exact hh
      · exact (zero_ne_one hz).elim
    have hzρ : z = ρ.symm (b i) := ρ.injective (hz'.trans (ρ.apply_symm_apply _).symm)
    exact congrArg (fun z : RingHom.PointsOver φ D ↦ z.tensor hφB) hzρ
  obtain ⟨Dj, cDj, aDj, E, qj, hlying, hint, hsingle, hpure, hcomap⟩ :=
    integral_factors_of_geometric_idempotents φB e he t ht huniq
  let := cDj
  let := aDj
  let p' : PrimeSpectrum B := ⟨RingHom.ker φB, RingHom.ker_isPrime _⟩
  let q' : PrimeSpectrum (B ⊗[A] D) :=
    ⟨RingHom.ker (tq.tensor hφB).1, RingHom.ker_isPrime _⟩
  refine ⟨B, cB, aB, ?_, p', ?_, q', ?_, ?_, Fintype.card I, hn, Dj,
    cDj, aDj, E, qj, hlying, hint, hsingle, hpure, ?_⟩
  · exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr hB)
  · apply PrimeSpectrum.ext
    change (RingHom.ker φB).comap (algebraMap A B) = p.asIdeal
    rw [RingHom.comap_ker, hφB, hφ]
  · apply PrimeSpectrum.ext
    exact (RingHom.PointsOver.ker_tensor_comap_includeRight hφB tq).trans htq
  · exact PrimeSpectrum.ext (tq.tensor hφB).under_ker
  · rw [hcomap]
    have hzero : t ⟨0, hn⟩ = tq.tensor hφB := by
      dsimp only [t]
      rw [hb]
      exact congrArg (fun z : RingHom.PointsOver φ D ↦ z.tensor hφB)
        (ρ.symm_apply_apply tq)
    rw [hzero]

end Algebra
