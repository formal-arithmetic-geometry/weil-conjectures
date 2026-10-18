/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS, SHEAF group K9
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Scalar extension of degree-zero homogeneous localization

Source: Stacks Project, constructions.tex, Tag 01N2 (lemma-base-change-map-proj),
standard-open calculation, with the chart fractions of Tag 01M4 (lemma-standard-open).
(blueprint: lem-nagata-homogeneous-localization-scalar-extension)
-/

@[expose] public section

universe u v w

open TensorProduct

namespace HomogeneousLocalization

section Construction

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

private local instance scalarExtensionAlgebra :
    Algebra R (Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)) :=
  ((algebraMap S _).comp (algebraMap R S)).toAlgebra

private local instance scalarExtensionTower :
    IsScalarTower R S (Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)) :=
  .of_algebraMap_eq' rfl

private noncomputable def scalarExtensionMap :
    (S ⊗[R] Away 𝒜 f) →ₐ[S]
      Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) := by
  let g : 𝒜 →+*ᵍ (fun n ↦ (𝒜 n).baseChange S) :=
    { Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A) with
      map_mem := fun ha ↦ Submodule.tmul_mem_baseChange_of_mem 1 ha }
  let h : Away 𝒜 f →ₐ[R]
      Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) :=
    { Away.map g f with
      commutes' := by
        intro r
        change Away.map g f (fromZeroRingHom 𝒜 _ (algebraMap R (𝒜 0) r)) =
          fromZeroRingHom (fun n ↦ (𝒜 n).baseChange S) _
            (algebraMap S ((𝒜 0).baseChange S) (algebraMap R S r))
        rw [← RingHom.comp_apply, Away.map_comp_fromZeroRingHom]
        change fromZeroRingHom (fun n ↦ (𝒜 n).baseChange S) _
          (g.gradeZeroRingHom (algebraMap R (𝒜 0) r)) = _
        apply congrArg (fromZeroRingHom (fun n ↦ (𝒜 n).baseChange S) _)
        apply Subtype.ext
        change (1 : S) ⊗ₜ[R] algebraMap R A r = algebraMap R S r ⊗ₜ[R] (1 : A)
        simp [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul'] }
  exact AlgHom.liftEquiv R S _ _ h

private lemma scalarExtensionMap_tmul (s : S) (m : ℕ) (a : A)
    (ha : a ∈ 𝒜 (m • d)) :
    scalarExtensionMap (S := S) 𝒜 (s ⊗ₜ[R] Away.mk 𝒜 hf m a ha) =
      Away.mk (fun n ↦ (𝒜 n).baseChange S)
        (Submodule.tmul_mem_baseChange_of_mem 1 hf) m (s ⊗ₜ[R] a)
        (Submodule.tmul_mem_baseChange_of_mem s ha) := by
  change s • Away.map
    (show 𝒜 →+*ᵍ (fun n ↦ (𝒜 n).baseChange S) from
      { Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A) with
        map_mem := fun ha ↦ Submodule.tmul_mem_baseChange_of_mem 1 ha }) f
    (Away.mk 𝒜 hf m a ha) = _
  rw [Away.map_mk]
  apply val_injective
  simp [val_smul, Away.val_mk, Localization.smul_mk, TensorProduct.smul_tmul']

private def fractionLinearMap (m : ℕ) : 𝒜 (m • d) →ₗ[R] Away 𝒜 f where
  toFun a := Away.mk 𝒜 hf m a a.property
  map_add' a b := by
    apply val_injective
    simp [Away.val_mk, Localization.add_mk_self]
  map_smul' r a := by
    apply val_injective
    simpa only [Away.val_mk, val_smul, Submodule.coe_smul_of_tower, RingHom.id_apply] using
      (Localization.smul_mk r (a : A) (⟨f ^ m, by use m⟩ : Submonoid.powers f)).symm

private def transition (m k : ℕ) : 𝒜 (m • d) →ₗ[R] 𝒜 ((m + k) • d) where
  toFun a := ⟨(a : A) * f ^ k, by
    simpa only [add_smul] using SetLike.mul_mem_graded a.property
      (SetLike.pow_mem_graded k hf)⟩
  map_add' a b := Subtype.ext (add_mul _ _ _)
  map_smul' r a := Subtype.ext (smul_mul_assoc _ _ _)

private lemma fractionLinearMap_transition (m k : ℕ) (a : 𝒜 (m • d)) :
    fractionLinearMap 𝒜 hf (m + k) (transition 𝒜 hf m k a) =
      fractionLinearMap 𝒜 hf m a :=
  Away.mk_mul_pow_cancel 𝒜 hf m k a a.property _

private lemma baseChange_fraction_transition (m k : ℕ) (c : S ⊗[R] 𝒜 (m • d)) :
    (fractionLinearMap 𝒜 hf (m + k)).baseChange S
        ((transition 𝒜 hf m k).baseChange S c) =
      (fractionLinearMap 𝒜 hf m).baseChange S c := by
  induction c with
  | zero => simp only [map_zero]
  | tmul s a => simp only [LinearMap.baseChange_tmul, fractionLinearMap_transition]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma scalarExtensionMap_fraction (m : ℕ) (c : S ⊗[R] 𝒜 (m • d)) :
    scalarExtensionMap (S := S) 𝒜 ((fractionLinearMap 𝒜 hf m).baseChange S c) =
      fractionLinearMap (fun n ↦ (𝒜 n).baseChange S)
        (Submodule.tmul_mem_baseChange_of_mem 1 hf) m ((𝒜 (m • d)).toBaseChange S c) := by
  induction c with
  | zero => simp only [map_zero]
  | tmul s a => exact scalarExtensionMap_tmul 𝒜 hf s m a a.property
  | add x y hx hy => simp only [map_add, hx, hy]

include hf in
private lemma exists_fraction_tensor (x : S ⊗[R] Away 𝒜 f) :
    ∃ (m : ℕ) (c : S ⊗[R] 𝒜 (m • d)),
      (fractionLinearMap 𝒜 hf m).baseChange S c = x := by
  induction x with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul s a =>
    obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf a
    exact ⟨m, s ⊗ₜ[R] ⟨a, ha⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨m, c, rfl⟩ := hx
    obtain ⟨n, c', rfl⟩ := hy
    have hn : ∃ c'' : S ⊗[R] 𝒜 ((m + n) • d),
        (fractionLinearMap 𝒜 hf (m + n)).baseChange S c'' =
          (fractionLinearMap 𝒜 hf n).baseChange S c' := by
      rw [Nat.add_comm m n]
      exact ⟨(transition 𝒜 hf n m).baseChange S c',
        baseChange_fraction_transition 𝒜 hf n m c'⟩
    obtain ⟨c'', hn⟩ := hn
    refine ⟨m + n, (transition 𝒜 hf m n).baseChange S c + c'', ?_⟩
    rw [map_add, baseChange_fraction_transition, hn]

private lemma toBaseChange_transition (m k : ℕ) (c : S ⊗[R] 𝒜 (m • d)) :
    ((𝒜 ((m + k) • d)).toBaseChange S ((transition 𝒜 hf m k).baseChange S c) :
        S ⊗[R] A) =
      ((𝒜 (m • d)).toBaseChange S c : S ⊗[R] A) * (1 ⊗ₜ[R] f) ^ k := by
  induction c with
  | zero => simp only [map_zero, ZeroMemClass.coe_zero, zero_mul]
  | tmul s a =>
    change s ⊗ₜ[R] ((a : A) * f ^ k) = (s ⊗ₜ[R] (a : A)) * (1 ⊗ₜ[R] f) ^ k
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [one_pow, mul_one]
  | add x y hx hy =>
    simp only [map_add, Submodule.coe_add, hx, hy, add_mul]

include hf in
private lemma scalarExtensionMap_surjective :
    Function.Surjective (scalarExtensionMap (S := S) 𝒜 (f := f)) := by
  intro y
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective (fun n ↦ (𝒜 n).baseChange S)
    (Submodule.tmul_mem_baseChange_of_mem 1 hf) y
  obtain ⟨c, hc⟩ := (𝒜 (m • d)).toBaseChange_surjective S ⟨a, ha⟩
  refine ⟨(fractionLinearMap 𝒜 hf m).baseChange S c, ?_⟩
  rw [scalarExtensionMap_fraction, hc]
  rfl

include hf in
private lemma scalarExtensionMap_injective :
    Function.Injective (scalarExtensionMap (S := S) 𝒜 (f := f)) := by
  suffices h : ∀ x, scalarExtensionMap (S := S) 𝒜 x = 0 → x = 0 from
    fun x y hxy ↦ sub_eq_zero.mp (h (x - y) (by rw [map_sub, hxy, sub_self]))
  intro x hx
  obtain ⟨m, c, rfl⟩ := exists_fraction_tensor 𝒜 hf x
  rw [scalarExtensionMap_fraction] at hx
  have hv := congrArg val hx
  simp only [fractionLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Away.val_mk,
    val_zero, Localization.mk_eq_mk'] at hv
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hv
  have hz : (transition 𝒜 hf m k).baseChange S c = 0 := by
    apply DirectSum.toBaseChange_injective 𝒜 (S := S) ((m + k) • d)
    apply Subtype.ext
    rw [toBaseChange_transition, map_zero, ZeroMemClass.coe_zero]
    simpa only [mul_comm] using hk
  rw [← baseChange_fraction_transition 𝒜 hf m k c, hz, map_zero]

end Construction

/-- Scalar extension commutes with degree-zero homogeneous localization, with its prescribed
formula on pure tensors of fractions. Source: Stacks Project, constructions.tex, Tag 01N2,
proof of lemma-base-change-map-proj; fraction convention of Tag 01M4.
(blueprint: lem-nagata-homogeneous-localization-scalar-extension)

Proof: The graded map a ↦ 1 ⊗ a induces an R-algebra map on homogeneous
localizations. Extending scalars gives an S-algebra map λ with the displayed formula.
For each m, the R-linear map u_m : A_(md) → Away 𝒜 f sends a to a/f^m.
Its scalar extension q_m sends s ⊗ a to s ⊗ (a/f^m). Multiplication by f^k
on numerators gives q_(m+k)((1 ⊗ f)^k c) = q_m(c). Induction on tensors,
putting two denominators m,n over m+n, shows that every source element is q_m(c).
The map from S ⊗ A_(md) onto the base-changed graded piece is bijective, by
Mathlib's DirectSum.toBaseChange_bijective; no flatness is needed. Thus every target
fraction has a preimage under λ. If λ(q_m(c)) = 0, the localization zero criterion
gives k with (1 ⊗ f)^k times the image of c equal to zero. Injectivity of the
graded-piece identification makes the transitioned tensor numerator zero. Applying
q_(m+k) and the transition identity gives q_m(c) = 0. Hence λ is injective and
surjective, and therefore defines the desired algebra equivalence. All fraction
calculations use the ordinary localization relation, allowing zero divisors. -/
theorem exists_away_scalarExtension_equiv
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    ∃ e : (S ⊗[R] Away 𝒜 f) ≃ₐ[S]
        Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f),
      ∀ (s : S) (m : ℕ) (a : A) (ha : a ∈ 𝒜 (m • d)),
        e (s ⊗ₜ[R] Away.mk 𝒜 hf m a ha) =
          Away.mk (fun n ↦ (𝒜 n).baseChange S)
            (Submodule.tmul_mem_baseChange_of_mem 1 hf) m (s ⊗ₜ[R] a)
            (Submodule.tmul_mem_baseChange_of_mem s ha) := by
  have _hd : 0 < d := hd
  refine ⟨AlgEquiv.ofBijective (scalarExtensionMap (S := S) 𝒜 (f := f))
    ⟨scalarExtensionMap_injective 𝒜 hf, scalarExtensionMap_surjective 𝒜 hf⟩, ?_⟩
  exact scalarExtensionMap_tmul 𝒜 hf

end HomogeneousLocalization
