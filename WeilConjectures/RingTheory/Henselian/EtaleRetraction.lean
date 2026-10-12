/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Henselian local rings: étale retractions and idempotent lifting

Let `(R, 𝔪, κ)` be a local ring. We prove the following characterisations of henselian local
rings (Stacks, Lemma 04GG), following the blueprint.

* If simple roots of monic polynomials lift from `κ` to `R` (Mathlib's `HenselianLocalRing`),
  then every étale `R`-algebra `S` has, through every prime `q` over `𝔪` with trivial residue
  field extension, exactly one `R`-algebra retraction `τ : S →ₐ[R] R` with `τ⁻¹(𝔪) = q`.
* If étale `R`-algebras have such retractions, every finite `R`-algebra is a finite product of
  local rings.
* `R` is henselian (in Mathlib's sense of root lifting) if and only if idempotents of
  `B / 𝔪B` lift uniquely to `B` for every finite `R`-algebra `B`.

## Main results

- `IsLocalRing.existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot`
- `HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_eq`
- `IsLocalRing.exists_algEquiv_pi_isLocalRing_of_forall_exists_algHom`
- `IsLocalRing.forall_existsUnique_isIdempotentElem_iff_forall_exists_isRoot`
- `HenselianLocalRing.iff_forall_existsUnique_isIdempotentElem`

## References

- Stacks Project, Lemma 10.153.3, <https://stacks.math.columbia.edu/tag/04GG>
-/

@[expose] public section

universe u v

open Polynomial IsLocalRing
open scoped TensorProduct

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **Finite algebras over a local ring: maximal ideals lie over the maximal ideal.** If `B` is
a finite `R`-algebra over the local ring `(R, 𝔪)`, every maximal ideal of `B` has preimage `𝔪`
in `R`.

(blueprint: `lem-weil-pbc-finite-algebra-local-radical`) -/
theorem comap_eq_maximalIdeal_of_finite {B : Type v} [CommRing B] [Algebra R B]
    [Module.Finite R B] (n : Ideal B) [n.IsMaximal] :
    n.comap (algebraMap R B) = maximalIdeal R :=
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) n
  IsLocalRing.eq_maximalIdeal this

/-- **Finite algebras over a local ring: `𝔪B` lies in the Jacobson radical.** If `B` is a
finite `R`-algebra over the local ring `(R, 𝔪)`, then `𝔪B` is contained in the Jacobson
radical of `B`.

(blueprint: `lem-weil-pbc-finite-algebra-local-radical`) -/
theorem map_maximalIdeal_le_jacobson_of_finite {B : Type v} [CommRing B] [Algebra R B]
    [Module.Finite R B] :
    (maximalIdeal R).map (algebraMap R B) ≤ Ideal.jacobson ⊥ := by
  refine le_sInf fun n ⟨_, hn⟩ ↦ ?_
  rw [Ideal.map_le_iff_le_comap, comap_eq_maximalIdeal_of_finite n]

/-- **Uniqueness of retractions of unramified algebras over a local ring.** Two `R`-algebra
maps from a formally unramified, essentially of finite type `R`-algebra `S` to the local ring
`R` with the same preimage of the maximal ideal are equal.
(blueprint: `lem-weil-pbc-henselian-etale-retraction-uniqueness`) -/
theorem algHom_ext_of_comap_maximalIdeal_eq {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] {σ₁ σ₂ : S →ₐ[R] R}
    (h : (maximalIdeal R).comap σ₁ = (maximalIdeal R).comap σ₂) : σ₁ = σ₂ := by
  obtain ⟨t, ht, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.mp ‹_›
  have hmod (s : S) : σ₂ s - σ₁ s ∈ maximalIdeal R := by
    have hs : s - algebraMap R S (σ₁ s) ∈ (maximalIdeal R).comap σ₁ := by
      simp [Ideal.mem_comap]
    rwa [h, Ideal.mem_comap, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply] at hs
  let φ : S ⊗[R] S →ₐ[R] R := Algebra.TensorProduct.lift σ₁ σ₂ fun _ _ ↦ Commute.all _ _
  have hφ : (IsScalarTower.toAlgHom R R (ResidueField R)).comp φ =
      ((IsScalarTower.toAlgHom R R (ResidueField R)).comp σ₁).comp
        (Algebra.TensorProduct.lmul' R) := by
    refine Algebra.TensorProduct.ext' fun a b ↦ ?_
    have hb : residue R (σ₂ b) = residue R (σ₁ b) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hmod b
    simp [φ, ResidueField.algebraMap_eq, hb]
  have hunit : IsUnit (φ t) := by
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq]
    have := congr($hφ t)
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this, ht1, map_one, map_one]
    exact one_ne_zero
  ext s
  have := congr(φ $(ht s))
  rw [map_mul, map_sub, map_zero] at this
  simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at this
  exact (sub_eq_zero.mp (hunit.mul_left_eq_zero.mp this)).symm

/-- **Sections of étale algebras through residue field points.** Let `(R, 𝔪, κ)` be a local
ring in which simple roots in `κ` of monic polynomials over `R` lift to roots in `R`. Then every
`R`-algebra map `χ : S →ₐ[R] κ` from an étale `R`-algebra `S` is the reduction of an
`R`-algebra map `S →ₐ[R] R`. -/
theorem exists_algHom_comp_eq_of_forall_exists_isRoot
    (H : ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
      aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀)
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (χ : S →ₐ[R] ResidueField R) :
    ∃ σ : S →ₐ[R] R, (IsScalarTower.toAlgHom R R (ResidueField R)).comp σ = χ := by
  have : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime _
  have : Algebra.IsEtaleAt R (RingHom.ker χ) :=
    inferInstanceAs (Algebra.FormallyEtale R (Localization (RingHom.ker χ).primeCompl))
  obtain ⟨h, hh, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (RingHom.ker χ)
  have hu (y : Submonoid.powers h) : IsUnit (χ y) := by
    obtain ⟨y, n, rfl⟩ := y
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr fun e ↦ hh (RingHom.mem_ker.mpr e)).pow n
  let χₗ : Localization.Away h →ₐ[R] ResidueField R :=
    IsLocalization.liftAlgHom (M := Submonoid.powers h) (f := χ) hu
  obtain ⟨Pres⟩ := hstd.nonempty_standardEtalePresentation
  have hx := Pres.hasMap.map χₗ
  obtain ⟨a, ha, hares⟩ := H Pres.P.f Pres.P.monic_f (χₗ Pres.x) hx.1
    hx.isUnit_derivative_f.ne_zero
  have haP : Pres.P.HasMap a := by
    refine ⟨by simpa [aeval_def] using ha, ?_⟩
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, ← aeval_algebraMap_apply,
      ResidueField.algebraMap_eq, hares]
    exact hx.2.ne_zero
  let σ₀ : Localization.Away h →ₐ[R] R := (Pres.P.lift a haP).comp Pres.equivRing.toAlgHom
  have key : (IsScalarTower.toAlgHom R R (ResidueField R)).comp σ₀ = χₗ := by
    refine Pres.hom_ext ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Pres.equivRing_x, Pres.P.lift_X, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq,
      hares]
  refine ⟨σ₀.comp (IsScalarTower.toAlgHom R S (Localization.Away h)), ?_⟩
  rw [← AlgHom.comp_assoc, key]
  refine AlgHom.ext fun y ↦ ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  exact IsLocalization.lift_eq hu y

/-- **Étale retractions over a local ring in which simple roots lift.** Let `(R, 𝔪, κ)` be a
local ring in which simple roots in `κ` of monic polynomials over `R` lift to roots in `R`, let
`S` be an étale `R`-algebra and `q` a prime of `S` lying over `𝔪` such that `κ → κ(q)` is
bijective. Then there is exactly one `R`-algebra map `τ : S →ₐ[R] R` with `τ⁻¹(𝔪) = q`.

(blueprint: `lem-weil-pbc-root-lifting-etale-retraction`) -/
theorem existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot
    (H : ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
      aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀)
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      hq.symm)) :
    ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap τ = q := by
  let e₁ : ResidueField R ≃ₐ[R] (maximalIdeal R).ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ maximalIdeal R) _)
      (maximalIdeal R).bijective_algebraMap_quotient_residueField
  let e₂ := AlgEquiv.ofBijective _ hκ
  let χ : S →ₐ[R] ResidueField R := (e₁.symm.toAlgHom.comp e₂.symm.toAlgHom).comp
    (IsScalarTower.toAlgHom R S q.ResidueField)
  obtain ⟨σ, hσ⟩ := exists_algHom_comp_eq_of_forall_exists_isRoot H χ
  have hσq : (maximalIdeal R).comap σ = q := by
    ext s
    have hs := congr($hσ s)
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq] at hs
    rw [Ideal.mem_comap, ← residue_eq_zero_iff, hs]
    simp [χ]
  exact ⟨σ, hσq, fun σ' hσ' ↦ algHom_ext_of_comap_maximalIdeal_eq (hσ'.trans hσq.symm)⟩

/-- **Quotients by complements of idempotents with a unique maximal ideal are local.** Let `x`
be a nonzero idempotent of a commutative ring `B` such that at most one maximal ideal of `B`
does not contain `x`. Then `B ⧸ (1 - x)` is a local ring. -/
theorem _root_.IsIdempotentElem.isLocalRing_quotient_span_one_sub {B : Type*} [CommRing B]
    {x : B}
    (hx : IsIdempotentElem x) (hx0 : x ≠ 0)
    (H : ∀ M₁ M₂ : Ideal B, M₁.IsMaximal → M₂.IsMaximal → x ∉ M₁ → x ∉ M₂ → M₁ = M₂) :
    IsLocalRing (B ⧸ Ideal.span {1 - x}) := by
  have : Nontrivial (B ⧸ Ideal.span {1 - x}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr fun h ↦ hx0 ?_
    rw [Ideal.span_singleton_eq_top] at h
    simpa using h.mul_left_eq_zero.mp hx.mul_one_sub_self
  refine .of_unique_max_ideal ?_
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (B ⧸ Ideal.span {1 - x})
  have hnot (N : Ideal (B ⧸ Ideal.span {1 - x})) (hN : N.IsMaximal) :
      x ∉ N.comap (Ideal.Quotient.mk _) := by
    intro hxN
    have h1 : 1 - x ∈ N.comap (Ideal.Quotient.mk _) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
      exact N.zero_mem
    have h2 := add_mem h1 hxN
    rw [sub_add_cancel, Ideal.mem_comap, map_one] at h2
    exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr h2)
  refine ⟨M, hM, fun N hN ↦ Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_⟩
  exact H _ _ (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) (hnot N hN) (hnot M hM)
/-- **Étale retractions give product decompositions of finite algebras.** Let `(R, 𝔪, κ)` be a
local ring such that for every étale `R`-algebra `R'` and every prime `𝔪'` of `R'` over `𝔪`
with `κ → κ(𝔪')` bijective there is an `R`-algebra map `τ : R' →ₐ[R] R` with `τ⁻¹(𝔪) = 𝔪'`.
Then every finite `R`-algebra is isomorphic to a finite product of local rings.

(blueprint: `lem-weil-pbc-etale-retraction-finite-product-local`) -/
theorem exists_algEquiv_pi_isLocalRing_of_forall_exists_algHom
    (H : ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (m' : Ideal R')
      [m'.IsPrime] (hm' : m'.comap (algebraMap R R') = maximalIdeal R),
      Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) m' (Algebra.ofId R R')
        hm'.symm) →
      ∃ τ : R' →ₐ[R] R, (maximalIdeal R).comap τ = m')
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] :
    ∃ (r : ℕ) (B' : Fin r → Type u) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra R (B' i))
      (_ : ∀ i, IsLocalRing (B' i)), Nonempty (B ≃ₐ[R] ∀ i, B' i) := by
  classical
  obtain ⟨R', _, _, _, P, _, hPm, n, e, he, P', _, _, hP, -, hP''⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq (S := B)
      (maximalIdeal R)
  obtain ⟨τ, hτ⟩ := H R' P (P.over_def (maximalIdeal R)).symm hP
  let φ : R' ⊗[R] B →ₐ[R] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId R B).comp τ) (AlgHom.id R B)
      fun _ _ ↦ Commute.all _ _
  have hφs : Function.Surjective φ := fun b ↦ ⟨1 ⊗ₜ b, by simp [φ]⟩
  have hlies (M : Ideal B) [M.IsMaximal] : (M.comap φ).LiesOver P := by
    refine ⟨?_⟩
    rw [← hτ]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, ← comap_eq_maximalIdeal_of_finite M,
      Ideal.mem_comap]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
  have hkey (i : Fin (n + 1)) (M₁ M₂ : Ideal B) (h₁ : M₁.IsMaximal) (h₂ : M₂.IsMaximal)
      (hM₁ : φ (e i) ∉ M₁) (hM₂ : φ (e i) ∉ M₂) : M₁ = M₂ := by
    have H₁ := hP'' (M₁.comap φ) inferInstance (hlies M₁)
    have H₂ := hP'' (M₂.comap φ) inferInstance (hlies M₂)
    refine Ideal.comap_injective_of_surjective φ hφs ?_
    obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · rw [H₁.2 j hM₁, H₂.2 j hM₂]
    · exact absurd H₁.1 hM₁
  let J := {i : Fin (n + 1) // φ (e i) ≠ 0}
  have hJ : CompleteOrthogonalIdempotents fun j : J ↦ φ (e j) := by
    have hfe := he.map φ.toRingHom
    refine ⟨hfe.1.embedding (Function.Embedding.subtype _), ?_⟩
    calc ∑ j : J, φ (e j) = ∑ i ∈ Finset.univ.filter (fun i ↦ φ (e i) ≠ 0), φ (e i) :=
          (Finset.sum_subtype (p := fun i ↦ φ (e i) ≠ 0) _ (fun _ ↦ by simp)
            fun i ↦ φ (e i)).symm
      _ = ∑ i, φ (e i) := Finset.sum_filter_ne_zero _
      _ = 1 := hfe.complete
  let Q (j : J) := B ⧸ Ideal.span {1 - φ (e j)}
  let eJ := Fintype.equivFin J
  refine ⟨Fintype.card J, fun k ↦ Q (eJ.symm k), fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun k ↦ (he.idem _).map φ |>.isLocalRing_quotient_span_one_sub (eJ.symm k).2
      (hkey _), ⟨?_⟩⟩
  exact (AlgEquiv.ofBijective (AlgHom.pi fun j ↦ Ideal.Quotient.mkₐ R _)
    hJ.bijective_pi).trans (AlgEquiv.piCongrLeft R Q eJ.symm).symm

/-- **Henselian local rings: idempotent lifting versus root lifting.** For a local ring
`(R, 𝔪, κ)` the following are equivalent:
(i) for every finite `R`-algebra `B`, every idempotent of `B / 𝔪B` lifts uniquely to an
idempotent of `B`;
(ii) for every monic `f ∈ R[X]` and every simple root `a₀ ∈ κ` of `f mod 𝔪` there is a root
`a ∈ R` of `f` lifting `a₀`.

(blueprint: `lem-weil-pbc-henselian-local-root-lifting`) -/
theorem forall_existsUnique_isIdempotentElem_iff_forall_exists_isRoot :
    (∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
      (e : B ⧸ (maximalIdeal R).map (algebraMap R B)), IsIdempotentElem e →
        ∃! e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk _ e' = e) ↔
    ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
      aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀ :=
  sorry

end IsLocalRing

namespace HenselianLocalRing

variable {R : Type u} [CommRing R]

/-- **Étale retractions over a henselian local ring.** Let `(R, 𝔪, κ)` be a henselian local
ring, `S` an étale `R`-algebra and `q` a prime of `S` lying over `𝔪` such that `κ → κ(q)` is
bijective. Then there is exactly one `R`-algebra map `σ : S →ₐ[R] R` with `σ⁻¹(𝔪) = q`.

(blueprint: `lem-weil-pbc-henselian-etale-retraction`) -/
theorem existsUnique_algHom_comap_maximalIdeal_eq [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      hq.symm)) :
    ∃! σ : S →ₐ[R] R, (maximalIdeal R).comap σ = q :=
  IsLocalRing.existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot
    (((HenselianLocalRing.TFAE R).out 0 1).mp ‹HenselianLocalRing R›) q hq hκ

/-- **Existence of étale retractions over a henselian local ring**: the existence half of
`HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_eq`.
(blueprint: `lem-weil-pbc-henselian-etale-retraction-existence`) -/
theorem exists_algHom_comap_maximalIdeal_eq [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      hq.symm)) :
    ∃ σ : S →ₐ[R] R, (maximalIdeal R).comap σ = q :=
  (existsUnique_algHom_comap_maximalIdeal_eq q hq hκ).exists

/-- **Henselian local rings lift idempotents.** A local ring `(R, 𝔪)` is henselian (in Mathlib's
sense of lifting simple roots) if and only if for every finite `R`-algebra `B` every idempotent
of `B / 𝔪B` lifts uniquely to an idempotent of `B`.

(blueprint: `lem-weil-pbc-henselian-local-root-lifting`) -/
theorem iff_forall_existsUnique_isIdempotentElem [IsLocalRing R] :
    HenselianLocalRing R ↔
      ∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
        (e : B ⧸ (maximalIdeal R).map (algebraMap R B)), IsIdempotentElem e →
          ∃! e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk _ e' = e :=
  sorry

end HenselianLocalRing

namespace IsStrictlyHenselianLocalRing

variable {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]

/-- **Maps from étale algebras into a strictly henselian local ring.** Let `(R, 𝔪)` be a strictly
henselian local ring, `K` a field over `R` with `ker(R → K) = 𝔪` and `S` an étale `R`-algebra.
Every `R`-algebra map `χ : S → K` lifts uniquely to an `R`-algebra map `S → R`.

This is the single-étale-algebra case of the blueprint lemma, with the residue condition
`τ : κ(q) → κ` automatic since `κ` is separably closed.

(blueprint: `lem-weil-pbc-map-into-henselian-colimit`) -/
theorem existsUnique_algHom_comp_eq {K : Type*} [Field K] [Algebra R K]
    (hK : RingHom.ker (algebraMap R K) = maximalIdeal R) {S : Type v} [CommRing S]
    [Algebra R S] [Algebra.Etale R S] (χ : S →ₐ[R] K) :
    ∃! τ : S →ₐ[R] R, (Algebra.ofId R K).comp τ = χ := by
  have : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime _
  have hq : (RingHom.ker χ).comap (algebraMap R S) = maximalIdeal R := by
    ext r
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, ← RingHom.mem_ker, hK]
  have : (RingHom.ker χ).LiesOver (maximalIdeal R) := ⟨hq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) (RingHom.ker χ)
  have : IsSepClosed (maximalIdeal R).ResidueField := by
    let e : ResidueField R ≃+* (maximalIdeal R).ResidueField :=
      RingEquiv.ofBijective (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
        (maximalIdeal R).bijective_algebraMap_quotient_residueField
    exact IsSepClosed.of_ringEquiv e
  have hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) (RingHom.ker χ)
      (Algebra.ofId R S) hq.symm) :=
    ⟨RingHom.injective _, IsSepClosed.algebraMap_surjective (maximalIdeal R).ResidueField
      (RingHom.ker χ).ResidueField⟩
  obtain ⟨τ, hτ, -⟩ :=
    HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_eq (RingHom.ker χ) hq hκ
  have key : (Algebra.ofId R K).comp τ = χ := by
    ext d
    have : d - algebraMap R S (τ d) ∈ RingHom.ker χ := by
      rw [← hτ, Ideal.mem_comap, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
      exact zero_mem _
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    simp [this]
  refine ⟨τ, key, fun τ' hτ' ↦ IsLocalRing.algHom_ext_of_comap_maximalIdeal_eq ?_⟩
  ext d
  rw [Ideal.mem_comap, Ideal.mem_comap, ← hK, RingHom.mem_ker, RingHom.mem_ker,
    ← Algebra.ofId_apply, ← Algebra.ofId_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hτ', key]

end IsStrictlyHenselianLocalRing
