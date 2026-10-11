/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.SimpleRing.Principal
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!
# Henselian rings and strictly henselian local rings via sections of étale algebras

The zero ideal of any commutative ring is henselian (`HenselianRing.bot`).

A local ring `R` such that every étale `R`-algebra `B` has, through every prime of `B` over the
closed point, an `R`-algebra section `B →ₐ[R] R`, is henselian with separably closed residue
field. Both statements are tested on standard étale algebras `R[X][1/f']/(f)` for a monic `f`:
a section sends `X` to a root of `f`.

## Main results

- `HenselianRing.bot`: the zero ideal of any ring is henselian.
- `HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq`: such a local ring is henselian.
- `IsLocalRing.isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq`: such a local
  ring has separably closed residue field.

The henselian pairs `(A, I)` of the blueprint (`def-weil-pbc-henselian-terminology`) are
Mathlib's `HenselianRing A I`; a henselian local ring is `HenselianLocalRing`, and it is
strictly henselian when moreover `IsSepClosed (IsLocalRing.ResidueField A)`.
-/

@[expose] public section

/-- The zero ideal of any ring is henselian. -/
instance HenselianRing.bot (R : Type*) [CommRing R] : HenselianRing R ⊥ where
  jac := bot_le
  is_henselian f _ a₀ h _ := ⟨a₀, by simpa using h, by simp⟩

universe u

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Let `R` be a local ring such that every prime of an étale `R`-algebra lying over the maximal
ideal is the preimage of the maximal ideal under an `R`-algebra map to `R`. If `K` is a field
over `R` whose structure map has kernel the maximal ideal, then every simple root `x : K` of a
monic `f : R[X]` is the image of a root of `f` in `R`. -/
theorem IsLocalRing.exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q)
    {K : Type*} [Field K] [Algebra R K] (hK : RingHom.ker (algebraMap R K) = maximalIdeal R)
    {f : R[X]} (hf : f.Monic) {x : K} (hx : aeval x f = 0) (hx' : aeval x (derivative f) ≠ 0) :
    ∃ a : R, f.IsRoot a ∧ algebraMap R K a = x := by
  let P := StandardEtalePair.ofMonic hf 1
  have hP : P.HasMap x := ⟨hx, by simpa [P, StandardEtalePair.ofMonic] using hx'⟩
  let χ := P.lift x hP
  have hq : (RingHom.ker χ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    rw [← hK, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, AlgHom.commutes]
  have := RingHom.ker_isPrime χ
  obtain ⟨ψ, hψ⟩ := H P.Ring (RingHom.ker χ) hq
  refine ⟨ψ P.X, ?_, ?_⟩
  · have h := congr_arg ψ (StandardEtalePair.hasMap_X (P := P)).1
    rwa [← aeval_algHom_apply, map_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] at h
  · have hmem : P.X - algebraMap R P.Ring (ψ P.X) ∈ (maximalIdeal R).comap ψ := by
      simp [Ideal.mem_comap]
    rw [hψ, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hmem
    rw [← hmem]
    exact P.lift_X x hP

/-- A local ring `R` is henselian if every prime `q` lying over the maximal ideal of an étale
`R`-algebra `B` is the preimage of the maximal ideal under an `R`-algebra map `B →ₐ[R] R`. -/
theorem HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q) :
    HenselianLocalRing R := by
  refine ((HenselianLocalRing.TFAE R).out 1 0).mp fun f hf a₀ h₁ h₂ ↦ ?_
  have hK : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  simpa [ResidueField.algebraMap_eq] using
    exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq H hK hf h₁ h₂

/-- A local ring `R` has separably closed residue field if every prime `q` lying over the
maximal ideal of an étale `R`-algebra `B` is the preimage of the maximal ideal under an
`R`-algebra map `B →ₐ[R] R`. -/
theorem IsLocalRing.isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q) :
    IsSepClosed (ResidueField R) := by
  refine IsSepClosed.of_exists_root _ fun h hm hirr hsep ↦ ?_
  obtain ⟨f, rfl, -, hf⟩ := lifts_and_natDegree_eq_and_monic
    (map_surjective _ residue_surjective h) hm
  have := Fact.mk hirr
  have hK : RingHom.ker (algebraMap R (AdjoinRoot (f.map (residue R)))) = maximalIdeal R := by
    ext r
    rw [← ker_residue, RingHom.mem_ker, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply R (ResidueField R),
      map_eq_zero, ResidueField.algebraMap_eq]
  have hroot₀ : aeval (AdjoinRoot.root (f.map (residue R))) (f.map (residue R)) = 0 :=
    AdjoinRoot.aeval_eq _ |>.trans AdjoinRoot.mk_self
  have hroot : aeval (AdjoinRoot.root (f.map (residue R))) f = 0 := by
    rw [← aeval_map_algebraMap (ResidueField R), ResidueField.algebraMap_eq]
    exact hroot₀
  have hroot' : aeval (AdjoinRoot.root (f.map (residue R))) (derivative f) ≠ 0 := by
    rw [← aeval_map_algebraMap (ResidueField R), ResidueField.algebraMap_eq, ← derivative_map]
    exact hsep.aeval_derivative_ne_zero hroot₀
  obtain ⟨a, ha, -⟩ := exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq H hK hf
    hroot hroot'
  exact ⟨residue R a, by simpa using congr(residue R $ha)⟩

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.RingTheory.Henselian`) -/

/-- A local ring is strictly henselian if it is henselian with separably closed residue field. -/
class IsStrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop
    extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField R)

instance (R : Type*) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsSepClosed (IsLocalRing.ResidueField R) :=
  IsStrictlyHenselianLocalRing.isSepClosed_residueField

/-- A local ring is strictly Henselian if and only if it is Henselian and its residue
field is separably closed. -/
theorem isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed
    (R : Type*) [CommRing R] [IsLocalRing R] :
    IsStrictlyHenselianLocalRing R ↔
      HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
    fun h ↦ have := h.1; ⟨h.2⟩⟩

/-- `HenselianLocalRing` transfers along a ring isomorphism. -/
theorem HenselianLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := by
  have : IsLocalRing S := e.isLocalRing
  refine HenselianLocalRing.mk fun f hf a₀ hmem hunit => ?_
  let f' : Polynomial R := f.map e.symm.toRingHom
  have heval : f'.eval (e.symm a₀) = e.symm (f.eval a₀) :=
    Polynomial.eval_map_apply (p := f) e.symm.toRingHom a₀
  have hderiv : f'.derivative.eval (e.symm a₀) = e.symm (f.derivative.eval a₀) := by
    rw [Polynomial.derivative_map (f := e.symm.toRingHom)]
    exact Polynomial.eval_map_apply (p := f.derivative) e.symm.toRingHom a₀
  have hmem' : f'.eval (e.symm a₀) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal] at hmem
    rw [heval, IsLocalRing.mem_maximalIdeal]
    intro hu
    exact hmem (by simpa using hu.map e)
  have hunit' : IsUnit (f'.derivative.eval (e.symm a₀)) :=
    hderiv ▸ hunit.map e.symm.toRingHom
  obtain ⟨a, ha_root, ha_diff⟩ :=
    HenselianLocalRing.is_henselian f' (hf.map _) (e.symm a₀) hmem' hunit'
  refine ⟨e a, ?_, ?_⟩
  · have hf_eq : f'.map e.toRingHom = f := by
      simp [f', Polynomial.map_map]
    have key : f.eval (e a) = e (f'.eval a) := by
      rw [← hf_eq]; exact Polynomial.eval_map_apply (p := f') e.toRingHom a
    rw [Polynomial.IsRoot.def, key, Polynomial.IsRoot.def.mp ha_root, map_zero]
  · rw [IsLocalRing.mem_maximalIdeal] at ha_diff ⊢
    intro hu
    apply ha_diff
    have : a - e.symm a₀ = e.symm (e a - a₀) := by simp
    rw [this]
    exact hu.map e.symm.toRingHom

/-- `IsStrictlyHenselianLocalRing` transfers along a ring isomorphism. -/
theorem IsStrictlyHenselianLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsStrictlyHenselianLocalRing R] (e : R ≃+* S) : IsStrictlyHenselianLocalRing S :=
  have : HenselianLocalRing S := .of_ringEquiv e
  ⟨IsSepClosed.of_ringEquiv (IsLocalRing.ResidueField.mapEquiv e)⟩
