/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.Invariant.Reynolds
public import WeilConjectures.RingTheory.Etale.InvariantsDescentAux

/-!
# Descent of étaleness along a tame cover with trivial residue action

Let `R` be a Noetherian local ring, `R'` a local `R`-algebra finite over `R` and `Γ` a finite group
of order invertible in `R`, acting on `R'` by `R`-algebra automorphisms with `R'^Γ = R` and
trivially on the residue field `κ(R')` (e.g. a totally ramified tame Kummer cover, see
`WeilConjectures.RingTheory.Etale.KummerDescent`). Let `T'` be a finite étale `R'`-algebra with a
semilinear `Γ`-action and `T = T'^Γ`. If the closed fibre of `T'` is split by `k = rank T'`
pairwise distinct `Γ`-invariant points `T' → κ(R')`, then `T` is finite étale over `R`
(`RingTheory.InvariantsDescent.etale_and_finite_of_isInvariant`). This is the trait case of the
spreading theorem for finite étale Galois covers (blueprint
`sbc-thm-spreading-finite-etale-galois`, [Stacks 0EYJ], first paragraph).

## Proof

* The points lift uniquely to points `L : T' → R' ⧸ 𝔪ⁿ R'` (formal étaleness, the kernel of
  `R' ⧸ 𝔪ⁿ R' → κ(R')` being nilpotent), which are `Γ`-equivariant by uniqueness
  (`lift_smul`), jointly surjective (`surjective_pi_of_injective`) and with kernel `𝔪 T'` for
  `n = 1` by the rank bound (`mem_map_of_forall_eq_zero`).
* Averaging over `Γ` (`Algebra.IsInvariant.exists_sub_algebraMap_mem_map`), they descend to
  points `T → R ⧸ 𝔪ⁿ` (`descendPoint`) which are jointly surjective and have kernel `𝔪 T` for
  `n = 1`. Hence `T ≅ Rᵏ` (`nonempty_linearEquiv_pi_of_surjective`, using Krull's intersection
  theorem).
* The compatible points define points `T → R^` to the completion, giving a surjection
  `R^ ⊗ T → (R^)ᵏ` (`surjective_liftPiTop_of_isUnit`) of free modules of rank `k`, hence an
  isomorphism. Étaleness descends along the faithfully flat `R → R^`.
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace RingTheory.InvariantsDescent

section Descent

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R'] [Algebra R R']
  {Γ : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ R'] [SMulCommClass Γ R R']
  [Algebra.IsInvariant R R' Γ]
  {T : Type*} [CommRing T] [Algebra R T] {T' : Type*} [CommRing T'] [Algebra R' T']
  [Algebra R T'] [IsScalarTower R R' T'] [Algebra T T'] [IsScalarTower R T T']
  [MulSemiringAction Γ T'] [SMulCommClass Γ T T']

variable (R') in
/-- The map `R ⧸ I → R' ⧸ I R'`. -/
noncomputable abbrev quotientMapIdeal (I : Ideal R) : R ⧸ I →ₐ[R] R' ⧸ I.map (algebraMap R R') :=
  Ideal.quotientMapₐ _ (Algebra.ofId R R') Ideal.le_comap_map

lemma quotientMapIdeal_mk (I : Ideal R) (a : R) :
    quotientMapIdeal R' I (Ideal.Quotient.mk I a) = Ideal.Quotient.mk _ (algebraMap R R' a) :=
  rfl

variable (Γ) in
lemma injective_quotientMapIdeal (hR : Function.Injective (algebraMap R R'))
    (hΓ : IsUnit (Fintype.card Γ : R)) (I : Ideal R) :
    Function.Injective (quotientMapIdeal R' I) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [quotientMapIdeal_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Algebra.IsInvariant.mem_of_algebraMap_mem_map (G := Γ) hΓ hR I hy)

omit [SMulCommClass Γ R R'] [Algebra R T] [Algebra R T'] [IsScalarTower R R' T']
  [IsScalarTower R T T'] in
lemma quotientMapIdeal_mem_range (hΓ : IsUnit (Fintype.card Γ : R)) (I : Ideal R)
    (L : T' →ₐ[R'] R' ⧸ I.map (algebraMap R R'))
    (hL : ∀ (g : Γ) (t : T') (x : R'), L t = Ideal.Quotient.mk _ x →
      L (g • t) = Ideal.Quotient.mk _ (g • x)) (t : T) :
    L (algebraMap T T' t) ∈ (quotientMapIdeal R' I).range := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (L (algebraMap T T' t))
  have hinv (g : Γ) : g • x - x ∈ I.map (algebraMap R R') := by
    rw [← Ideal.Quotient.eq, ← hL g _ x hx.symm, smul_algebraMap, hx]
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.exists_sub_algebraMap_mem_map hΓ I hinv
  refine ⟨Ideal.Quotient.mk I a, ?_⟩
  exact (Ideal.Quotient.eq.2 ha).symm.trans hx

/-- A `Γ`-equivariant point `T' → R' ⧸ I R'` restricts to a point `T → R ⧸ I` of the invariants
`T = T'^Γ`. -/
noncomputable def descendPoint (hR : Function.Injective (algebraMap R R'))
    (hΓ : IsUnit (Fintype.card Γ : R)) (I : Ideal R)
    (L : T' →ₐ[R'] R' ⧸ I.map (algebraMap R R'))
    (hL : ∀ (g : Γ) (t : T') (x : R'), L t = Ideal.Quotient.mk _ x →
      L (g • t) = Ideal.Quotient.mk _ (g • x)) : T →ₐ[R] R ⧸ I :=
  (AlgEquiv.ofInjective _ (injective_quotientMapIdeal Γ hR hΓ I)).symm.toAlgHom.comp
    (((L.restrictScalars R).comp (IsScalarTower.toAlgHom R T T')).codRestrict _
      (quotientMapIdeal_mem_range hΓ I L hL))

lemma quotientMapIdeal_descendPoint (hR : Function.Injective (algebraMap R R'))
    (hΓ : IsUnit (Fintype.card Γ : R)) (I : Ideal R)
    (L : T' →ₐ[R'] R' ⧸ I.map (algebraMap R R'))
    (hL : ∀ (g : Γ) (t : T') (x : R'), L t = Ideal.Quotient.mk _ x →
      L (g • t) = Ideal.Quotient.mk _ (g • x)) (t : T) :
    quotientMapIdeal R' I (descendPoint hR hΓ I L hL t) = L (algebraMap T T' t) :=
  congrArg Subtype.val
    ((AlgEquiv.ofInjective _ (injective_quotientMapIdeal Γ hR hΓ I)).apply_symm_apply
    ⟨L (algebraMap T T' t), quotientMapIdeal_mem_range hΓ I L hL t⟩)

/-- The descended points are compatible with reduction. -/
lemma factorₐ_comp_descendPoint (hR : Function.Injective (algebraMap R R'))
    (hΓ : IsUnit (Fintype.card Γ : R)) {I₁ I₂ : Ideal R} (h : I₂ ≤ I₁)
    (L₁ : T' →ₐ[R'] R' ⧸ I₁.map (algebraMap R R')) (L₂ : T' →ₐ[R'] R' ⧸ I₂.map (algebraMap R R'))
    (hL₁ : ∀ (g : Γ) (t : T') (x : R'), L₁ t = Ideal.Quotient.mk _ x →
      L₁ (g • t) = Ideal.Quotient.mk _ (g • x))
    (hL₂ : ∀ (g : Γ) (t : T') (x : R'), L₂ t = Ideal.Quotient.mk _ x →
      L₂ (g • t) = Ideal.Quotient.mk _ (g • x))
    (hcomp : (Ideal.Quotient.factorₐ R' (Ideal.map_mono h)).comp L₂ = L₁) :
    (Ideal.Quotient.factorₐ R h).comp (descendPoint (T := T) hR hΓ I₂ L₂ hL₂) =
      descendPoint (T := T) hR hΓ I₁ L₁ hL₁ := by
  have key (y : R ⧸ I₂) : quotientMapIdeal R' I₁ (Ideal.Quotient.factorₐ R h y) =
      Ideal.Quotient.factorₐ R' (Ideal.map_mono h) (quotientMapIdeal R' I₂ y) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rfl
  ext t
  apply injective_quotientMapIdeal Γ hR hΓ I₁
  rw [AlgHom.comp_apply, key, quotientMapIdeal_descendPoint, quotientMapIdeal_descendPoint,
    ← hcomp, AlgHom.comp_apply]

/-- Surjectivity of `T' → (R' ⧸ I R')ᵏ` descends to `T → (R ⧸ I)ᵏ` by averaging. -/
lemma exists_descendPoint_eq [Algebra.IsInvariant T T' Γ]
    (hR : Function.Injective (algebraMap R R'))
    (hΓ : IsUnit (Fintype.card Γ : R)) (I : Ideal R) {k : ℕ}
    (L : Fin k → (T' →ₐ[R'] R' ⧸ I.map (algebraMap R R')))
    (hL : ∀ j (g : Γ) (t : T') (x : R'), L j t = Ideal.Quotient.mk _ x →
      L j (g • t) = Ideal.Quotient.mk _ (g • x))
    (hsurj : Function.Surjective (AlgHom.pi L)) (a : Fin k → R ⧸ I) :
    ∃ t : T, ∀ j, descendPoint hR hΓ I (L j) (hL j) t = a j := by
  choose α hα using fun j ↦ Ideal.Quotient.mk_surjective (a j)
  obtain ⟨t', ht'⟩ := hsurj fun j ↦ Ideal.Quotient.mk _ (algebraMap R R' (α j))
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : T, algebraMap T T' t₀ = ∑ g : Γ, g • t' :=
    Algebra.IsInvariant.exists_algebraMap_eq_sum_smul Γ t'
  refine ⟨(↑hΓ.unit⁻¹ : R) • t₀, fun j ↦ injective_quotientMapIdeal Γ hR hΓ I ?_⟩
  have hj : L j t' = Ideal.Quotient.mk _ (algebraMap R R' (α j)) := congrFun ht' j
  rw [quotientMapIdeal_descendPoint, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    ← Algebra.smul_def, ht₀, AlgHom.map_smul_of_tower, map_sum]
  simp_rw [hL j _ _ _ hj, smul_algebraMap]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    IsUnit.val_inv_mul, one_smul, ← hα, quotientMapIdeal_mk]

/-- If `T' → (R' ⧸ I R')ᵏ` has kernel `I T'`, then `T → (R ⧸ I)ᵏ` has kernel `I T`. -/
lemma mem_smul_top_of_descendPoint_eq_zero [Algebra.IsInvariant T T' Γ]
    (hR : Function.Injective (algebraMap R R'))
    (hT : Function.Injective (algebraMap T T')) (hΓ : IsUnit (Fintype.card Γ : R))
    (I : Ideal R) {k : ℕ} (L : Fin k → (T' →ₐ[R'] R' ⧸ I.map (algebraMap R R')))
    (hL : ∀ j (g : Γ) (t : T') (x : R'), L j t = Ideal.Quotient.mk _ x →
      L j (g • t) = Ideal.Quotient.mk _ (g • x))
    (hker : ∀ t' : T', (∀ j, L j t' = 0) →
      t' ∈ (I.map (algebraMap R R')).map (algebraMap R' T'))
    {t : T} (ht : ∀ j, descendPoint hR hΓ I (L j) (hL j) t = 0) :
    t ∈ I • (⊤ : Submodule R T) := by
  have h1 (j : Fin k) : L j (algebraMap T T' t) = 0 := by
    rw [← quotientMapIdeal_descendPoint hR hΓ I _ (hL j), ht j, map_zero]
  have h2 := hker _ h1
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R T T',
    ← Ideal.map_map] at h2
  have hΓT : IsUnit (Fintype.card Γ : T) := by simpa using hΓ.map (algebraMap R T)
  rw [Ideal.smul_top_eq_map]
  exact Algebra.IsInvariant.mem_of_algebraMap_mem_map hΓT hT _ h2

end Descent

section Main

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  {R' : Type*} [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.Finite R R']
  {Γ : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ R'] [SMulCommClass Γ R R']
  [Algebra.IsInvariant R R' Γ]
  {T : Type*} [CommRing T] [Algebra R T] {T' : Type*} [CommRing T'] [Algebra R' T']
  [Algebra R T'] [IsScalarTower R R' T'] [Algebra T T'] [IsScalarTower R T T']
  [MulSemiringAction Γ T'] [SMulDistribClass Γ R' T'] [SMulCommClass Γ T T']
  [Algebra.IsInvariant T T' Γ] [Algebra.Etale R' T'] [Module.Finite R' T']

/-- In a local ring `B` with a surjection `ε : B → K` onto a field, an element with nonzero
image is a unit. -/
lemma isUnit_of_map_ne_zero {B K F : Type*} [CommRing B] [IsLocalRing B] [Field K] [FunLike F B K]
    [RingHomClass F B K]
    (ε : F) (hε : Function.Surjective ε) {x : B} (hx : ε x ≠ 0) : IsUnit x := by
  by_contra h
  apply hx
  rw [← RingHom.mem_ker, eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε hε)]
  exact (mem_maximalIdeal x).2 h

/-- **Descent of étaleness along a tame Galois cover with trivial residue action.**
Let `R` be a Noetherian local ring and `R'` a local `R`-algebra, finite over `R`, with an action
of a finite group `Γ` by `R`-algebra automorphisms such that `R = R'^Γ` (`R → R'` injective,
`Algebra.IsInvariant R R' Γ`), `|Γ|` is invertible in `R` and `Γ` acts trivially on the residue
field `κ(R')`. Let `T'` be a finite étale `R'`-algebra of rank at most `k` with a semilinear
`Γ`-action, and `T = T'^Γ` its invariants. If `T'` has `k` pairwise distinct `Γ`-invariant points
`T' → κ(R')` (the closed fibre is split, with trivial `Γ`-action), then `T` is finite étale
over `R`.

This is the trait case of the spreading theorem for finite étale Galois covers
(blueprint `sbc-thm-spreading-finite-etale-galois`, [Stacks 0EYJ], first paragraph).

The points lift uniquely to `Γ`-equivariant points `T' → R' ⧸ 𝔪ⁿ R'`, which split `T'`
modulo `𝔪ⁿ`, and descend to points `T → R ⧸ 𝔪ⁿ` splitting `T` modulo `𝔪ⁿ` (averaging over
`Γ`). Hence `T` is free of rank `k`, the limit points `T → R^` split `R^ ⊗ T ≅ (R^)ᵏ`, and `T` is
étale by faithfully flat descent along the completion `R → R^`. -/
theorem etale_and_finite_of_isInvariant (hR : Function.Injective (algebraMap R R'))
    (hT : Function.Injective (algebraMap T T')) (hΓ : IsUnit (Fintype.card Γ : R))
    (hκ : ∀ (g : Γ) (x : R'), residue R' (g • x) = residue R' x)
    {k : ℕ} (hk : Module.finrank R' T' ≤ k)
    (φ : Fin k → (T' →ₐ[R'] ResidueField R')) (hφ : Function.Injective φ)
    (hφΓ : ∀ j (g : Γ) (t : T'), φ j (g • t) = φ j t) :
    Algebra.Etale R T ∧ Module.Finite R T := by
  classical
  have : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  set 𝔪 := maximalIdeal R
  let := Ideal.Quotient.field (maximalIdeal R)
  -- the ideals `J n = 𝔪ⁿ⁺¹ R'`
  let J (n : ℕ) : Ideal R' := (𝔪 ^ (n + 1)).map (algebraMap R R')
  have hJle (n : ℕ) : J n ≤ maximalIdeal R' :=
    (Ideal.map_mono (Ideal.pow_le_self n.succ_ne_zero)).trans map_maximalIdeal_le
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (maximalIdeal_le_radical_map (R := R) (R' := R')) (IsNoetherian.noetherian _)
  have hnil (n : ℕ) := isNilpotent_ker_residueOfLE (J n) (hJle n) (N := N * (n + 1)) (by
    rw [pow_mul]
    simp only [J, Ideal.map_pow]
    exact Ideal.pow_right_mono hN _)
  have hJΓ (n : ℕ) (g : Γ) (x : R') (hx : x ∈ J n) : g • x ∈ J n := by
    have : J n ≤ (J n).comap (MulSemiringAction.toRingHom Γ R' g) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap, MulSemiringAction.toRingHom_apply, smul_algebraMap]
      exact Ideal.mem_map_of_mem _ hr
    exact this hx
  -- the lifts `T' → R' ⧸ J n` of the points
  let L (n : ℕ) (j : Fin k) : T' →ₐ[R'] R' ⧸ J n :=
    Algebra.FormallySmooth.liftOfSurjective (φ j) (residueOfLE (J n) (hJle n))
      (Ideal.Quotient.factor_surjective (hJle n)) (hnil n)
  have hLφ (n : ℕ) (j : Fin k) : (residueOfLE (J n) (hJle n)).comp (L n j) = φ j :=
    Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hLuniq (n : ℕ) (j : Fin k) (L' : T' →ₐ[R'] R' ⧸ J n)
      (h : (residueOfLE (J n) (hJle n)).comp L' = φ j) : L' = L n j :=
    Algebra.FormallyUnramified.lift_unique' _ (hnil n) _ _ (h.trans (hLφ n j).symm)
  have hLΓ (n : ℕ) (j : Fin k) (g : Γ) (t : T') (x : R')
      (hx : L n j t = Ideal.Quotient.mk _ x) : L n j (g • t) = Ideal.Quotient.mk _ (g • x) :=
    lift_smul (J n) (hJle n) (hnil n) (hJΓ n) hκ (L n j) (fun g t ↦ by
      rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hLφ, hφΓ]) g t x hx
  have hLsurj (n : ℕ) : Function.Surjective (AlgHom.pi (L n)) := by
    refine surjective_pi_of_injective (J n) (hJle n) (L n) ?_
    have : (fun j ↦ (residueOfLE (J n) (hJle n)).comp (L n j)) = φ := funext (hLφ n)
    rw [this]
    exact hφ
  have hLker (n : ℕ) (t : T') (ht : ∀ j, L n j t = 0) : t ∈ (J n).map (algebraMap R' T') :=
    mem_map_of_forall_eq_zero hk (J n)
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R').ne_top (hJle n)) (L n) (hLsurj n) ht
  -- the descended points `T → R ⧸ 𝔪ⁿ⁺¹`
  let χ (n : ℕ) (j : Fin k) : T →ₐ[R] R ⧸ 𝔪 ^ (n + 1) :=
    descendPoint (T := T) hR hΓ (𝔪 ^ (n + 1)) (L n j) (hLΓ n j)
  have hχcomp (j : Fin k) (n n' : ℕ) (h : n ≤ n') :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega : n + 1 ≤ n' + 1))).comp
        (χ n' j) = χ n j := by
    refine factorₐ_comp_descendPoint hR hΓ _ (L n j) (L n' j) (hLΓ n j) (hLΓ n' j) ?_
    refine hLuniq n j _ ?_
    rw [← AlgHom.comp_assoc, ← hLφ n' j]
    congr 1
    exact Ideal.Quotient.algHom_ext _ (by ext)
  let χlin (n : ℕ) : T →ₗ[R] (Fin k → R ⧸ 𝔪 ^ (n + 1)) := (AlgHom.pi (χ n)).toLinearMap
  have hχsurj (n : ℕ) : Function.Surjective (χlin n) := fun a ↦ by
    obtain ⟨t, ht⟩ := exists_descendPoint_eq (T := T) hR hΓ _ (L n) (hLΓ n) (hLsurj n) a
    exact ⟨t, funext ht⟩
  have : Module.Finite R T' := Module.Finite.trans R' T'
  have hfin : Module.Finite R T :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom R T T').toLinearMap hT
  have h0 (x : T) (hx : χlin 0 x = 0) : x ∈ 𝔪 • (⊤ : Submodule R T) := by
    have := mem_smul_top_of_descendPoint_eq_zero hR hT hΓ (𝔪 ^ (0 + 1)) (L 0) (hLΓ 0)
      (hLker 0) (t := x) (fun j ↦ congrFun hx j)
    simpa using this
  obtain ⟨e⟩ := nonempty_linearEquiv_pi_of_surjective χlin hχsurj h0
  -- the points `T → R^` with values in the completion
  set B := AdicCompletion 𝔪 R
  let f (j : Fin k) (n : ℕ) : T →ₐ[R] R ⧸ 𝔪 ^ n :=
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)).comp (χ n j)
  have hf (j : Fin k) {a b : ℕ} (hab : a ≤ b) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hab)).comp (f j b) = f j a := by
    simp only [f, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
    rw [← hχcomp j a b hab, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  let ψ (j : Fin k) : T →ₐ[R] B := AdicCompletion.liftAlgHom 𝔪 (f j) (hf j)
  have hψ (j : Fin k) (t : T) : AdicCompletion.evalOneₐ 𝔪 (ψ j t) =
      Ideal.Quotient.factorₐ R (Ideal.pow_le_self one_ne_zero) (χ 0 j t) := by
    rw [AdicCompletion.evalOneₐ_liftAlgHom, ← hχcomp j 0 1 zero_le_one]
  have hunit (j l : Fin k) (hjl : j ≠ l) : ∃ t, IsUnit (ψ j t - ψ l t) := by
    obtain ⟨t, ht⟩ := hχsurj 0 (Pi.single j 1)
    refine ⟨t, isUnit_of_map_ne_zero (AdicCompletion.evalOneₐ 𝔪)
      (AdicCompletion.evalOneₐ_surjective 𝔪) ?_⟩
    have hj : χ 0 j t = 1 := (congrFun ht j).trans (Pi.single_eq_same j 1)
    have hl : χ 0 l t = 0 := (congrFun ht l).trans (Pi.single_eq_of_ne hjl.symm 1)
    rw [map_sub, hψ, hψ, hj, hl, map_one, map_zero, sub_zero]
    exact one_ne_zero
  -- the splitting `R^ ⊗ T ≅ (R^)ᵏ`
  have hsurj := surjective_liftPiTop_of_isUnit ψ hunit
  let eB : (Fin k → B) ≃ₗ[B] B ⊗[R] T :=
    (TensorProduct.piScalarRight R B B (Fin k)).symm.trans (LinearEquiv.baseChange R B _ _ e)
  have hinj : Function.Injective (DepthTwo.liftPiTop ψ) := by
    have h := OrzechProperty.injective_of_surjective_endomorphism
      ((DepthTwo.liftPiTop ψ).toLinearMap.comp eB.toLinearMap) (by
        rw [LinearMap.coe_comp]
        exact hsurj.comp eB.surjective)
    rw [LinearMap.coe_comp] at h
    intro x y hxy
    simpa using h (a₁ := eB.symm x) (a₂ := eB.symm y) (by simpa using hxy)
  let eT : B ⊗[R] T ≃ₐ[B] (Fin k → B) := AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have : Algebra.Etale B (B ⊗[R] T) := .of_equiv eT.symm
  have : Module.FaithfullyFlat R B :=
    DepthTwo.faithfullyFlat_adicCompletion 𝔪 (maximalIdeal.isMaximal R).ne_top
  exact ⟨.of_etale_tensorProduct_of_faithfullyFlat B, hfin⟩

end Main

end RingTheory.InvariantsDescent
