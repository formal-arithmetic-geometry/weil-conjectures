/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

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

We also record the idempotent-lifting form of a henselian pair, `Ideal.IsHenselianPair`: every
idempotent of `B ⧸ IB` lifts uniquely to an idempotent of `B`, for every finite `A`-algebra
`B`. It passes to finite `A`-algebras (`Ideal.IsHenselianPair.map`).
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

/-- **Henselian pairs, via idempotents.** A pair `(A, I)` of a commutative ring and an ideal is
*henselian* if, for every finite `A`-algebra `B`, every idempotent of `B ⧸ IB` lifts uniquely
to an idempotent of `B`. A local ring is henselian when its maximal-ideal pair is henselian
(`HenselianLocalRing`), and *strictly henselian* when moreover its residue field is
separably closed; for `T = Spec A` the closed member of the pair is `T₀ = Spec (A ⧸ I)`.
This is equivalent to `HenselianRing A I` [Stacks 09XI]; the comparison is not formalised.
(blueprint: `def-weil-pbc-henselian-terminology`) -/
def Ideal.IsHenselianPair {A : Type u} [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B]
    (e : B ⧸ I.map (algebraMap A B)), IsIdempotentElem e →
      ∃! e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk _ e' = e

/-- If `(A, I)` is a henselian pair and `B` is a finite `A`-algebra, then `(B, IB)` is a
henselian pair: a finite `B`-algebra `C` is a finite `A`-algebra, and `(IB)C = IC`.
This is Step 2 of the blueprint lemma `lemma-weil-pbc-stein-connectedness`. -/
theorem Ideal.IsHenselianPair.map {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] {I : Ideal A} (hI : I.IsHenselianPair) :
    (I.map (algebraMap A B)).IsHenselianPair := by
  intro C _ _ _
  let : Algebra A C := Algebra.compHom C (algebraMap A B)
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite A C := Module.Finite.trans B C
  have h : (I.map (algebraMap A B)).map (algebraMap B C) = I.map (algebraMap A C) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have key : ∀ J : Ideal C, J = I.map (algebraMap A C) → ∀ e : C ⧸ J, IsIdempotentElem e →
      ∃! e' : C, IsIdempotentElem e' ∧ Ideal.Quotient.mk J e' = e := by
    rintro J rfl
    exact hI C
  exact key _ h

