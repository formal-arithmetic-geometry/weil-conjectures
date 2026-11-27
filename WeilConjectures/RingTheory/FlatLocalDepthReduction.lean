/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.FlatModInjective
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.RingTheory.DepthQuotSMulTop
import WeilConjectures.RingTheory.DepthOverQuotientRing

/-!
# Quotients reducing the depth induction for a flat local map

For a flat local homomorphism `R → S` of Noetherian local rings with positive
`depth R + depth (S / m_R S)`, we construct compatible proper quotients `R / J → S / K` that
remain flat and local and on which the depth of the target and the source-plus-fibre depth sum
both drop by one. These are the two inductive cases of the flat local depth formula.

## Implementation details

If the closed fibre `F = S / m_R S` has positive depth, a regular element of `m_F` is lifted
to `y ∈ m_S`; the local injectivity criterion makes `y` regular on `S` and `S / y S` flat over
`R`, and we take `J = 0`, `K = (y)`. Otherwise `depth R` is positive, a regular element
`x ∈ m_R` is chosen, and we take `J = (x)`, `K = (φ x)`, using flat base change along
`R → R / J`. In both cases the new closed fibre is identified by double quotient
isomorphisms, and the depth drops come from the regular-element depth drop and change of
rings. Quotient-ring identifications preserve depth by transporting regular sequences.

## References

* [Stacks, Tag 0338], the two positive-depth cases of the proof
* [Stacks, Tag 00ME]
* [Stacks, Tag 07T8]
* [Stacks, Tag 090R]
* [Stacks, Tag 0AUK]
-/

@[expose] public section

universe u v

namespace IsLocalRing

private theorem maximal_smul_top_ne_top (A : Type*) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
  rw [Ideal.smul_top_eq_map]
  change (maximalIdeal A).map (algebraMap A A) ≠ ⊤
  simpa only [Algebra.algebraMap_self, Ideal.map_id] using
    (maximalIdeal.isMaximal A).ne_top

private theorem depth_le_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    depth (R := A) A ≤ depth (R := B) B := by
  classical
  simp only [depth, Ideal.depth, maximal_smul_top_ne_top, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [← map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hmem a ha)

private theorem depth_eq_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    depth (R := A) A = depth (R := B) B :=
  le_antisymm (depth_le_of_ringEquiv e) (depth_le_of_ringEquiv e.symm)

private theorem exists_regular_of_depth_pos (A : Type*) [CommRing A] [IsLocalRing A]
    (hpos : 0 < depth (R := A) A) :
    ∃ x ∈ maximalIdeal A, IsSMulRegular A x := by
  classical
  by_contra h
  push Not at h
  have hz : depth (R := A) A ≤ 0 := by
    simp only [depth, Ideal.depth, maximal_smul_top_ne_top, ↓reduceIte]
    apply sSup_le
    rintro n ⟨rs, hreg, hmem, rfl⟩
    cases rs with
    | nil => simp
    | cons x xs =>
      exact False.elim (h x (hmem x (by simp))
        ((RingTheory.Sequence.isRegular_cons_iff A x xs).mp hreg).1)
  exact (not_lt_of_ge hz) hpos

open scoped Pointwise in
private theorem depth_principal_quotient (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (x : A) (hx : x ∈ maximalIdeal A)
    (hreg : IsSMulRegular A x) [IsLocalRing (A ⧸ Ideal.span {x})] :
    depth (R := A) A = depth (R := A ⧸ Ideal.span {x}) (A ⧸ Ideal.span {x}) + 1 := by
  have hspan : Ideal.span {x} ≤ maximalIdeal A := by simpa using hx
  have hsub : x • (⊤ : Submodule A A) = Ideal.span {x} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
    simp
  obtain ⟨_, d, hd, hA, hQ⟩ := depth_quotSMulTop_of_isSMulRegular A x hx hreg
  change depth (R := A) (A ⧸ x • (⊤ : Submodule A A)) = _ at hQ
  rw [hsub] at hQ
  have hzero : Module.IsTorsionBySet A (A ⧸ Ideal.span {x}) (Ideal.span {x}) := by
    intro y a
    induction y using Quotient.inductionOn with
    | h y =>
      change Ideal.Quotient.mk _ (a.val * y) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.span {x}).mul_mem_right y a.property)
  have heq := (depth_over_quotient_ring A (Ideal.span {x}) hspan
    (A ⧸ Ideal.span {x}) hzero).2
  rw [heq, hQ, hA]
  norm_cast
  omega

/-- Lifting a regular closed-fibre element gives a flat principal quotient and
identifies its new closed fibre, without any assertion about depth. -/
private theorem exists_fibre_regular_flat_quotients
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat)
    [IsLocalRing (S ⧸ (maximalIdeal R).map φ)]
    (x : S ⧸ (maximalIdeal R).map φ)
    (hx : x ∈ maximalIdeal (S ⧸ (maximalIdeal R).map φ))
    (hreg : IsSMulRegular (S ⧸ (maximalIdeal R).map φ) x) :
    ∃ (y : S) (hy : y ∈ maximalIdeal S),
      Ideal.Quotient.mk ((maximalIdeal R).map φ) y = x ∧ IsSMulRegular S y ∧
      let J : Ideal R := ⊥
      let K : Ideal S := Ideal.span {y}
      let hJ : J ≤ maximalIdeal R := bot_le
      let hK : K ≤ maximalIdeal S := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy)
    letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
    letI : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
    letI : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    letI : IsLocalRing (S ⧸ K) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
    ∃ (ψ : (R ⧸ J) →+* (S ⧸ K)) (_hψ : IsLocalHom ψ),
      ψ.Flat ∧ ∃ _hF : IsLocalRing ((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ),
        ψ.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk K).comp φ ∧
        Nonempty (((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ) ≃+*
          ((S ⧸ (maximalIdeal R).map φ) ⧸ Ideal.span {x})) := by
  classical
  let : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hflat
  let I : Ideal S := (maximalIdeal R).map φ
  obtain ⟨y, hxy⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk I y = x at hxy
  have hy : y ∈ maximalIdeal S := by
    have : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hmem : y ∈ (maximalIdeal (S ⧸ I)).comap (Ideal.Quotient.mk I) := by
      change Ideal.Quotient.mk I y ∈ maximalIdeal (S ⧸ I)
      simpa [I, hxy] using hx
    rwa [maximalIdeal_comap] at hmem
  let u : S →ₗ[R] S := (LinearMap.mulLeft S y).restrictScalars R
  let P := maximalIdeal R • (⊤ : Submodule R S)
  let v := P.mapQ P u (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) u)
  let eP : (S ⧸ P) ≃ₗ[R] (S ⧸ I) :=
    (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map (maximalIdeal R))).trans
      (Submodule.Quotient.restrictScalarsEquiv R I)
  have hv : Function.Injective v := by
    have he (z : S ⧸ P) : eP (v z) = x * eP z := by
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        change Ideal.Quotient.mk I (y * z) = x * Ideal.Quotient.mk I z
        rw [map_mul, hxy]
    intro z w hzw
    apply eP.injective
    exact hreg (by simpa only [smul_eq_mul] using ((he z).symm.trans
      ((congrArg eP hzw).trans (he w))))
  obtain ⟨hinj, hflatQ⟩ := flat_mod_injective φ (fun r hr ↦ map_nonunit φ r hr) u hv
  have hyreg : IsSMulRegular S y := hinj
  let J : Ideal R := ⊥
  let K : Ideal S := Ideal.span {y}
  have hJ : J ≤ maximalIdeal R := bot_le
  have hK : K ≤ maximalIdeal S := by simpa [K] using hy
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
  let : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsLocalRing (S ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have hrange : LinearMap.range u = K.restrictScalars R := by
    ext z
    change (∃ w, y * w = z) ↔ z ∈ Ideal.span {y}
    simp only [Ideal.mem_span_singleton, dvd_def, eq_comm]
  let eQ : (S ⧸ LinearMap.range u) ≃ₗ[R] (S ⧸ K) :=
    (Submodule.quotEquivOfEq _ _ hrange).trans
      (Submodule.Quotient.restrictScalarsEquiv R K)
  have : Module.Flat R (S ⧸ LinearMap.range u) := hflatQ
  have : Module.Flat R (S ⧸ K) := Module.Flat.of_linearEquiv eQ.symm
  let β : R →+* (S ⧸ K) := (Ideal.Quotient.mk K).comp φ
  have hβflat : β.Flat := by
    change Module.Flat R (S ⧸ K)
    infer_instance
  let ψ : (R ⧸ J) →+* (S ⧸ K) := β.comp (RingEquiv.quotientBot R).toRingHom
  have : IsLocalHom (Ideal.Quotient.mk K) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hlocal : IsLocalHom ψ := by
    dsimp [ψ, β]
    infer_instance
  let := hlocal
  have hcomm : ψ.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk K).comp φ := by
    ext r
    rfl
  have hFideal : (maximalIdeal (R ⧸ J)).map ψ = I.map (Ideal.Quotient.mk K) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, Ideal.map_map, hcomm, ← Ideal.map_map]
  have hKmap : K.map (Ideal.Quotient.mk I) = Ideal.span {x} := by
    simp [K, Ideal.map_span, hxy]
    rfl
  let e : ((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ) ≃+*
      ((S ⧸ I) ⧸ Ideal.span {x}) :=
    (Ideal.quotEquivOfEq hFideal).trans ((DoubleQuot.quotQuotEquivComm K I).trans
      (Ideal.quotEquivOfEq hKmap))
  have hxspan : Ideal.span {x} ≤ maximalIdeal (S ⧸ I) := by simpa [I] using hx
  let : Nontrivial ((S ⧸ I) ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal (S ⧸ I)).ne_top hxspan)
  let : IsLocalRing ((S ⧸ I) ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hF := e.symm.isLocalRing
  refine ⟨y, hy, hxy, hyreg, ψ, hlocal, ?_, hF, hcomm, ⟨e⟩⟩
  exact (RingHom.Flat.of_bijective (RingEquiv.quotientBot R).bijective).comp hβflat



/-- A principal quotient by a source element preserves flatness and the closed fibre.
The regularity assumption concerns the source element, not a depth formula. -/
private theorem exists_source_regular_flat_quotients
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat)
    [IsLocalRing (S ⧸ (maximalIdeal R).map φ)]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular R x) :
    let J : Ideal R := Ideal.span {x}
    let K : Ideal S := Ideal.span {φ x}
    let hJ : J ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    let hK : K ≤ maximalIdeal S := Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr (map_nonunit φ x hx))
    letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
    letI : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
    letI : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    letI : IsLocalRing (S ⧸ K) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
    ∃ (ψ : (R ⧸ J) →+* (S ⧸ K)) (_hψ : IsLocalHom ψ),
      ψ.Flat ∧ ∃ _hF : IsLocalRing ((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ),
        ψ.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk K).comp φ ∧
        IsSMulRegular S (φ x) ∧
        Nonempty (((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ) ≃+*
          (S ⧸ (maximalIdeal R).map φ)) := by
  classical
  let : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hflat
  let J : Ideal R := Ideal.span {x}
  let K : Ideal S := Ideal.span {φ x}
  have hJ : J ≤ maximalIdeal R := by simpa [J] using hx
  have hK : K ≤ maximalIdeal S := by simpa [K] using map_nonunit φ x hx
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
  let : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsLocalRing (S ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have hmap : J.map φ = K := by simp [J, K, Ideal.map_span]
  have hJK : J ≤ K.comap φ := Ideal.map_le_iff_le_comap.mp hmap.le
  let ψ := Ideal.quotientMap K φ hJK
  have hcomm : ψ.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk K).comp φ :=
    Ideal.quotientMap_comp_mk hJK
  have hlocal : IsLocalHom ψ := by
    apply ((local_hom_TFAE ψ).out 4 1).mp
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, Ideal.map_le_iff_le_comap,
      Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
    have : IsLocalHom (Ideal.Quotient.mk K) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [maximalIdeal_comap, maximalIdeal_comap]
  let := hlocal
  have hFideal : (maximalIdeal (R ⧸ J)).map ψ =
      ((maximalIdeal R).map φ).map (Ideal.Quotient.mk K) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, Ideal.map_map, hcomm, ← Ideal.map_map]
  have hKI : K ≤ (maximalIdeal R).map φ := by
    rw [← hmap]
    exact Ideal.map_mono hJ
  let e : ((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ) ≃+*
      (S ⧸ (maximalIdeal R).map φ) :=
    (Ideal.quotEquivOfEq hFideal).trans (DoubleQuot.quotQuotEquivQuotOfLE hKI)
  have hF := e.symm.isLocalRing
  have hyreg : IsSMulRegular S (φ x) := hreg.of_flat
  refine ⟨ψ, hlocal, ?_, hF, hcomm, hyreg, ⟨e⟩⟩
  let E := S ⧸ J.map φ
  let : Algebra (R ⧸ J) E :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let f : (R ⧸ J) →+* E := algebraMap (R ⧸ J) E
  have hf : f.Flat := by
    change (algebraMap (R ⧸ J) E).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S J).toLinearEquiv
  let eK : E ≃+* (S ⧸ K) := Ideal.quotEquivOfEq hmap
  have heK : eK.toRingHom.Flat := RingHom.Flat.of_bijective eK.bijective
  have hψeq : ψ = eK.toRingHom.comp f := by
    ext r
    rfl
  rw [hψeq]
  exact hf.comp heK



/-- A positive source-plus-fibre depth sum admits compatible proper quotients for
which both target depth and the source-plus-fibre depth sum decrease by one. -/
theorem exists_depth_reducing_flat_local_quotients {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat)
    [IsLocalRing (S ⧸ (maximalIdeal R).map φ)]
    (hpos : 0 < depth (R := R) R +
      depth (R := S ⧸ (maximalIdeal R).map φ) (S ⧸ (maximalIdeal R).map φ)) :
    ∃ (J : Ideal R) (K : Ideal S) (hJ : J ≤ maximalIdeal R) (hK : K ≤ maximalIdeal S),
      letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
      letI : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
      letI : IsLocalRing (R ⧸ J) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      letI : IsLocalRing (S ⧸ K) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
      ∃ (ψ : (R ⧸ J) →+* (S ⧸ K)) (_hψ : IsLocalHom ψ),
        ψ.Flat ∧
        ∃ hF : IsLocalRing ((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ),
          letI := hF
          ψ.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk K).comp φ ∧
          depth (R := S) S = depth (R := S ⧸ K) (S ⧸ K) + 1 ∧
          depth (R := R) R +
              depth (R := S ⧸ (maximalIdeal R).map φ) (S ⧸ (maximalIdeal R).map φ) =
            (depth (R := R ⧸ J) (R ⧸ J) +
              depth (R := (S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ)
                ((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ)) + 1 := by
  classical
  let F := S ⧸ (maximalIdeal R).map φ
  have : IsNoetherianRing F := inferInstanceAs (IsNoetherianRing
    (S ⧸ (maximalIdeal R).map φ))
  change 0 < depth (R := R) R + depth (R := F) F at hpos
  by_cases hFpos : 0 < depth (R := F) F
  · obtain ⟨x, hx, hxreg⟩ := exists_regular_of_depth_pos F hFpos
    obtain ⟨y, hy, _, hyreg, hquot⟩ :=
      exists_fibre_regular_flat_quotients φ hflat x hx hxreg
    let J : Ideal R := ⊥
    let K : Ideal S := Ideal.span {y}
    have hJ : J ≤ maximalIdeal R := bot_le
    have hK : K ≤ maximalIdeal S := by simpa [K] using hy
    refine ⟨J, K, hJ, hK, ?_⟩
    let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
    let : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
    let : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let : IsLocalRing (S ⧸ K) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
    obtain ⟨ψ, hψ, hψflat, hG, hcomm, ⟨e⟩⟩ := hquot
    let := hψ
    let := hG
    have hxspan : Ideal.span {x} ≤ maximalIdeal F := by simpa using hx
    let : Nontrivial (F ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal F).ne_top hxspan)
    let : IsLocalRing (F ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hS := depth_principal_quotient S y hy hyreg
    have hF := depth_principal_quotient F x hx hxreg
    have hR := depth_eq_of_ringEquiv (RingEquiv.quotientBot R)
    have hGdepth := depth_eq_of_ringEquiv e
    refine ⟨ψ, hψ, hψflat, hG, hcomm, hS, ?_⟩
    rw [hF, ← hR, ← hGdepth, add_assoc]
  · have hFzero : depth (R := F) F = 0 := le_antisymm (not_lt.mp hFpos) bot_le
    have hRpos : 0 < depth (R := R) R := by simpa [hFzero] using hpos
    obtain ⟨x, hx, hxreg⟩ := exists_regular_of_depth_pos R hRpos
    let J : Ideal R := Ideal.span {x}
    let K : Ideal S := Ideal.span {φ x}
    have hJ : J ≤ maximalIdeal R := by simpa [J] using hx
    have hy : φ x ∈ maximalIdeal S := map_nonunit φ x hx
    have hK : K ≤ maximalIdeal S := by simpa [K] using hy
    refine ⟨J, K, hJ, hK, ?_⟩
    let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
    let : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
    let : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let : IsLocalRing (S ⧸ K) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
    obtain ⟨ψ, hψ, hψflat, hG, hcomm, hyreg, ⟨e⟩⟩ :=
      exists_source_regular_flat_quotients φ hflat x hx hxreg
    let := hψ
    let := hG
    have hS := depth_principal_quotient S (φ x) hy hyreg
    have hR := depth_principal_quotient R x hx hxreg
    have hGdepth := depth_eq_of_ringEquiv e
    refine ⟨ψ, hψ, hψflat, hG, hcomm, hS, ?_⟩
    rw [hR, ← hGdepth]
    ac_rfl

end IsLocalRing
