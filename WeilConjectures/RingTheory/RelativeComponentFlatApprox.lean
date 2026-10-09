/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Noetherian approximation of a flat algebra along a fibre

Let `B` be a flat, finitely presented `A`-algebra with a section `s`, and `y` a prime of `A`.
Then `B` and `s` descend to a finite type algebra `B₁` with a section `s₁` over a noetherian
subring `A₁` of `A`, such that `B₁` is flat over `A₁` at the points lying under `y`.

## Main statements

- `Module.Flat.localization_tensorProduct_map`: flatness at a point of `R ⊗[R₀] S₀` over `R` is
  preserved by enlarging `R`.
- `PrimeSpectrum.isOpen_setOf_flat_localization`: the flat locus of a finite type algebra over a
  noetherian ring is open.
- `PrimeSpectrum.exists_fg_forall_flat_localization_tensor`: flatness along a whole fibre
  descends to a finitely generated subring (Stacks `00R6` and quasi-compactness of the fibre).
- `PrimeSpectrum.exists_comap_eq_of_isPushout`: points of a fibre lift along base change.
- `PrimeSpectrum.exists_isPushout_forall_flat`: noetherian approximation along a fibre.

## References

- Stacks Project, Tags `00R6`, `055Q`
-/

@[expose] public section

universe u

open TensorProduct

/-- **Flatness at a point along an enlargement of the base.** Let `f : R → R'` be a map of
`R₀`-algebras and `Q` a prime of `R' ⊗[R₀] S₀`. If `R ⊗[R₀] S₀` is flat over `R` at the prime
below `Q`, then `R' ⊗[R₀] S₀` is flat over `R'` at `Q`. -/
theorem Module.Flat.localization_tensorProduct_map {R₀ R R' S₀ : Type*} [CommRing R₀]
    [CommRing R] [CommRing R'] [CommRing S₀] [Algebra R₀ R] [Algebra R₀ R'] [Algebra R₀ S₀]
    (f : R →ₐ[R₀] R') (Q : Ideal (R' ⊗[R₀] S₀)) [Q.IsPrime] (P : Ideal (R ⊗[R₀] S₀)) [P.IsPrime]
    (hPQ : Q.comap (Algebra.TensorProduct.map f (AlgHom.id R₀ S₀)).toRingHom = P)
    (h : Module.Flat R (Localization.AtPrime P)) :
    Module.Flat R' (Localization.AtPrime Q) := by
  subst hPQ
  let : Algebra R R' := f.toRingHom.toAlgebra
  have : IsScalarTower R₀ R R' := .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  let : Algebra (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) :=
    (Algebra.TensorProduct.map f (AlgHom.id R₀ S₀)).toRingHom.toAlgebra
  have : IsScalarTower R (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have : Algebra.IsPushout R R' (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) :=
    Algebra.IsPushout.tensorProduct_tensorProduct R₀ S₀ R R' (by
      ext x
      simp [RingHom.algebraMap_toAlgebra])
  exact Module.Flat.localization_of_isPushout Q h

namespace PrimeSpectrum

/-- **Openness of the flat locus** (Stacks `00RC`). For a finite type algebra `S` over a
noetherian ring `R`, the set of primes `q` of `S` such that `S_q` is flat over `R` is open. -/
theorem isOpen_setOf_flat_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (Localization.AtPrime q.asIdeal)} := by
  rw [isOpen_iff_forall_mem_open]
  intro q (hq : Module.Flat R _)
  have hP : Module.Flat R (LocalizedModule q.asIdeal.primeCompl S) := Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso q.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime q.asIdeal))).restrictScalars R)
  obtain ⟨g, hg, hopen⟩ :=
    Module.Flat.exists_notMem_forall_flat_localizedModule (M := S) q.asIdeal hP
  refine ⟨basicOpen g, fun Q hQ ↦ ?_, isOpen_basicOpen, hg⟩
  have := hopen Q.asIdeal hQ
  exact Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso Q.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime Q.asIdeal))).restrictScalars R).symm

/-- Flatness of `R ⊗[R₀] S₀` over `R` at the prime below a prime `q` of `A ⊗[R₀] S₀` is preserved
by enlarging the subalgebra `R` of `A`. -/
theorem flat_localization_tensorProduct_of_le {R₀ A S₀ : Type*} [CommRing R₀] [CommRing A]
    [CommRing S₀] [Algebra R₀ A] [Algebra R₀ S₀] {R R' : Subalgebra R₀ A} (h : R ≤ R')
    (q : PrimeSpectrum (A ⊗[R₀] S₀))
    (hq : Module.Flat R (Localization.AtPrime (comap (Algebra.TensorProduct.map R.val
        (AlgHom.id R₀ S₀) : R ⊗[R₀] S₀ →+* A ⊗[R₀] S₀) q).asIdeal)) :
    Module.Flat R' (Localization.AtPrime (comap (Algebra.TensorProduct.map R'.val
        (AlgHom.id R₀ S₀) : R' ⊗[R₀] S₀ →+* A ⊗[R₀] S₀) q).asIdeal) := by
  refine Module.Flat.localization_tensorProduct_map (Subalgebra.inclusion h) _ _ ?_ hq
  rw [comap_asIdeal, comap_asIdeal, Ideal.comap_comap]
  congr 1
  ext x
  · rfl
  · rfl

/-- For a finitely generated subalgebra `R` of `A` over a noetherian ring `R₀` and a finite type
`R₀`-algebra `S₀`, the primes `q` of `A ⊗[R₀] S₀` such that `R ⊗[R₀] S₀` is flat over `R` at the
prime below `q` form an open set. -/
theorem isOpen_setOf_flat_localization_tensorProduct {R₀ A S₀ : Type*} [CommRing R₀]
    [CommRing A] [CommRing S₀] [Algebra R₀ A] [Algebra R₀ S₀] [IsNoetherianRing R₀]
    [Algebra.FiniteType R₀ S₀] {R : Subalgebra R₀ A} (hR : R.FG) :
    IsOpen {q : PrimeSpectrum (A ⊗[R₀] S₀) | Module.Flat R (Localization.AtPrime
      (comap (Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀) : R ⊗[R₀] S₀ →+* A ⊗[R₀] S₀)
        q).asIdeal)} := by
  have : Algebra.FiniteType R₀ R := (Subalgebra.fg_iff_finiteType _).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing R₀ R
  exact (isOpen_setOf_flat_localization (R := R) (S := R ⊗[R₀] S₀)).preimage
    (continuous_comap _)

/-- **Flatness along a fibre descends to a finitely generated subring** (Stacks `00R6`). Let `R₀`
be noetherian, `S₀` a finite type `R₀`-algebra and `A` an `R₀`-algebra such that `A ⊗[R₀] S₀` is
flat over `A`. For a prime `y` of `A` there is a finitely generated subalgebra `R₁` of `A` such that
`R₁ ⊗[R₀] S₀` is flat over `R₁` at every prime lying under a prime of `A ⊗[R₀] S₀` over `y`.

Each prime has a neighbourhood on which some `R ⊗[R₀] S₀` is flat
(`Module.exists_fg_flat_localization_tensor` and openness of the flat locus), flatness persists
when `R` grows, and the fibre over `y` is quasi-compact. -/
theorem exists_fg_forall_flat_localization_tensor {R₀ A S₀ : Type u} [CommRing R₀] [CommRing A]
    [CommRing S₀] [Algebra R₀ A] [Algebra R₀ S₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀]
    [Module.Flat A (A ⊗[R₀] S₀)] (y : PrimeSpectrum A) :
    ∃ R₁ : Subalgebra R₀ A, R₁.FG ∧ ∀ q : PrimeSpectrum (A ⊗[R₀] S₀),
      comap (algebraMap A (A ⊗[R₀] S₀)) q = y →
      Module.Flat R₁ (Localization.AtPrime (comap (Algebra.TensorProduct.map R₁.val
        (AlgHom.id R₀ S₀) : R₁ ⊗[R₀] S₀ →+* A ⊗[R₀] S₀) q).asIdeal) := by
  classical
  let W (R : Subalgebra R₀ A) : Set (PrimeSpectrum (A ⊗[R₀] S₀)) :=
    {q | Module.Flat R (Localization.AtPrime (comap (Algebra.TensorProduct.map R.val
        (AlgHom.id R₀ S₀) : R ⊗[R₀] S₀ →+* A ⊗[R₀] S₀) q).asIdeal)}
  have hWcov (q : PrimeSpectrum (A ⊗[R₀] S₀)) :
      ∃ R : {R : Subalgebra R₀ A // R.FG}, q ∈ W R.1 := by
    obtain ⟨R, hR, -, hflat⟩ := Module.exists_fg_flat_localization_tensor (S₀ := S₀) q.asIdeal
    exact ⟨⟨R, hR⟩, hflat⟩
  have hF : IsCompact (comap (algebraMap A (A ⊗[R₀] S₀)) ⁻¹' {y}) := by
    rw [isCompact_iff_compactSpace]
    exact (preimageHomeomorphFiber A (A ⊗[R₀] S₀) y).symm.compactSpace
  have : Nonempty {R : Subalgebra R₀ A // R.FG} := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  obtain ⟨⟨R₁, hR₁⟩, hK⟩ := hF.elim_directed_cover (fun R ↦ W R.1)
    (fun R ↦ isOpen_setOf_flat_localization_tensorProduct R.2)
    (fun q _ ↦ Set.mem_iUnion.mpr (hWcov q))
    fun (R R' : {R : Subalgebra R₀ A // R.FG}) ↦ ⟨⟨R.1 ⊔ R'.1, R.2.sup R'.2⟩,
      flat_localization_tensorProduct_of_le le_sup_left,
      flat_localization_tensorProduct_of_le le_sup_right⟩
  exact ⟨R₁, hR₁, fun q hq ↦ hK hq⟩

/-- **Points of a fibre lift along base change.** Let `B = A ⊗[A₁] B₁`, let `y` be a prime of `A`
and `K` a field over `A` with kernel `y`. Every prime `q₁` of `B₁` lying over `y ∩ A₁` lies under a
prime of `B` lying over `y`: take a prime of `B₁ ⊗[A₁] K` over `q₁` and pull it back along
`B → B₁ ⊗[A₁] K`. -/
theorem exists_comap_eq_of_isPushout {A₁ A B₁ B : Type*} [CommRing A₁] [CommRing A]
    [CommRing B₁] [CommRing B] [Algebra A₁ A] [Algebra A₁ B₁] [Algebra A B] [Algebra B₁ B]
    [Algebra A₁ B] [IsScalarTower A₁ A B] [IsScalarTower A₁ B₁ B] [Algebra.IsPushout A₁ A B₁ B]
    {y : PrimeSpectrum A} (K : Type*) [Field K] [Algebra A K]
    (hK : RingHom.ker (algebraMap A K) = y.asIdeal) (q₁ : PrimeSpectrum B₁)
    (hq₁ : comap (algebraMap A₁ B₁) q₁ = comap (algebraMap A₁ A) y) :
    ∃ q : PrimeSpectrum B, comap (algebraMap A B) q = y ∧ comap (algebraMap B₁ B) q = q₁ := by
  let : Algebra A₁ K := ((algebraMap A K).comp (algebraMap A₁ A)).toAlgebra
  have : IsScalarTower A₁ A K := .of_algebraMap_eq fun _ ↦ rfl
  have hker : RingHom.ker (algebraMap A₁ K) = q₁.asIdeal.comap (algebraMap A₁ B₁) := by
    rw [IsScalarTower.algebraMap_eq A₁ A K, ← RingHom.comap_ker, hK, ← comap_asIdeal,
      ← comap_asIdeal, hq₁]
  obtain ⟨P, hP, hPq⟩ :=
    Algebra.exists_isPrime_comap_includeLeft_eq (Field.toIsField K) q₁.asIdeal hker
  let f : A →ₐ[A₁] B₁ ⊗[A₁] K :=
    (Algebra.TensorProduct.includeRight : K →ₐ[A₁] B₁ ⊗[A₁] K).comp
      (IsScalarTower.toAlgHom A₁ A K)
  let ψ : B →ₐ[A₁] B₁ ⊗[A₁] K := Algebra.pushoutDesc B f Algebra.TensorProduct.includeLeft
    fun _ _ ↦ mul_comm _ _
  have hbot : P.comap (Algebra.TensorProduct.includeRight : K →ₐ[A₁] B₁ ⊗[A₁] K).toRingHom = ⊥ :=
    Ideal.eq_bot_of_prime _
  have hψA (a : A) : ψ (algebraMap A B a) = f a := Algebra.pushoutDesc_left _ _ _ _ a
  have hψB (b : B₁) : ψ (algebraMap B₁ B b) = Algebra.TensorProduct.includeLeft b :=
    Algebra.pushoutDesc_right _ _ _ _ b
  refine ⟨comap (ψ : B →+* B₁ ⊗[A₁] K) ⟨P, hP⟩, ?_, ?_⟩
  · ext a
    rw [comap_asIdeal, comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap]
    erw [hψA]
    rw [← hK, RingHom.mem_ker, ← Ideal.mem_bot, ← hbot, Ideal.mem_comap]
    rfl
  · ext b
    rw [comap_asIdeal, comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap]
    erw [hψB]
    rw [← hPq, Ideal.mem_comap]
    rfl

/-- **Descending a flat model along a fibre.** Let `B = A ⊗[R₀] B₀` with a section `s` induced by
a section `s₀` of `B₀`, and let `A₁` be a noetherian `R₀`-algebra mapping to `A` such that
`A₁ ⊗[R₀] B₀` is flat over `A₁` at every prime lying under a prime of `A ⊗[R₀] B₀` over `y`.
Then `B₁ = A₁ ⊗[R₀] B₀` with the section induced by `s₀` is a model of `B` over `A₁` which is
flat over `A₁` at every prime lying over `y ∩ A₁`: such primes lie under primes of `B` over `y`. -/
theorem exists_isPushout_forall_flat_of_tensorProduct {R₀ A₁ A B₀ B : Type u} [CommRing R₀]
    [CommRing A₁] [CommRing A] [CommRing B₀] [CommRing B] [Algebra R₀ A₁] [Algebra A₁ A]
    [Algebra R₀ A] [IsScalarTower R₀ A₁ A] [Algebra R₀ B₀] [Algebra A B] [Algebra B₀ B]
    [Algebra R₀ B] [IsScalarTower R₀ A B] [IsScalarTower R₀ B₀ B] [Algebra.IsPushout R₀ A B₀ B]
    [IsNoetherianRing A₁] [Algebra.FiniteType R₀ B₀] (s : B →ₐ[A] A) (s₀ : B₀ →ₐ[R₀] R₀)
    (hs : ∀ b, algebraMap R₀ A (s₀ b) = s (algebraMap B₀ B b)) (y : PrimeSpectrum A)
    (hflat : ∀ q : PrimeSpectrum (A ⊗[R₀] B₀), comap (algebraMap A (A ⊗[R₀] B₀)) q = y →
      Module.Flat A₁ (Localization.AtPrime (comap (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R₀ A₁ A) (AlgHom.id R₀ B₀) : A₁ ⊗[R₀] B₀ →+* A ⊗[R₀] B₀)
          q).asIdeal)) :
    ∃ (A₁ B₁ : Type u) (_ : CommRing A₁) (_ : CommRing B₁) (_ : Algebra A₁ A) (_ : Algebra A₁ B₁)
      (_ : Algebra B₁ B) (_ : Algebra A₁ B) (_ : IsScalarTower A₁ A B)
      (_ : IsScalarTower A₁ B₁ B),
      IsNoetherianRing A₁ ∧ Algebra.FiniteType A₁ B₁ ∧ Algebra.IsPushout A₁ A B₁ B ∧
      ∃ s₁ : B₁ →ₐ[A₁] A₁, (∀ b, algebraMap A₁ A (s₁ b) = s (algebraMap B₁ B b)) ∧
        ∀ q : PrimeSpectrum B₁,
          comap (algebraMap A₁ B₁) q = comap (algebraMap A₁ A) y →
          Module.Flat A₁ (Localization.AtPrime q.asIdeal) := by
  classical
  let e₀ : A ⊗[R₀] B₀ ≃ₐ[A] B := Algebra.IsPushout.equiv R₀ A B₀ B
  let φ : A₁ ⊗[R₀] B₀ →ₐ[R₀] B := (e₀.toAlgHom.restrictScalars R₀).comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ A₁ A) (AlgHom.id R₀ B₀))
  let : Algebra (A₁ ⊗[R₀] B₀) B := φ.toRingHom.toAlgebra
  let : Algebra A₁ B := ((algebraMap A B).comp (algebraMap A₁ A)).toAlgebra
  have : IsScalarTower A₁ A B := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A₁ (A₁ ⊗[R₀] B₀) B := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ, e₀, Algebra.IsPushout.equiv_tmul,
      Algebra.TensorProduct.algebraMap_apply]
  have : Algebra.IsPushout A₁ A (A₁ ⊗[R₀] B₀) B := by
    let : Algebra (A₁ ⊗[R₀] B₀) (A ⊗[A₁] (A₁ ⊗[R₀] B₀)) := Algebra.TensorProduct.rightAlgebra
    refine Algebra.IsPushout.of_equiv
      ((Algebra.TensorProduct.cancelBaseChange R₀ A₁ A A B₀).trans e₀) (RingHom.ext fun x ↦ ?_)
    induction x with
    | zero => simp
    | tmul a b =>
      simp [RingHom.algebraMap_toAlgebra, φ, e₀, Algebra.IsPushout.equiv_tmul,
        Algebra.algebraMap_eq_smul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let s₁ : A₁ ⊗[R₀] B₀ →ₐ[A₁] A₁ := Algebra.TensorProduct.lift (Algebra.ofId A₁ A₁)
    ((Algebra.ofId R₀ A₁).comp s₀) fun _ _ ↦ Commute.all _ _
  refine ⟨A₁, A₁ ⊗[R₀] B₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, s₁, fun b ↦ ?_, fun q₁ hq₁ ↦ ?_⟩
  · induction b with
    | zero => simp
    | tmul r b =>
      simp only [s₁, RingHom.algebraMap_toAlgebra, φ, e₀]
      simp [Algebra.IsPushout.equiv_tmul, ← IsScalarTower.algebraMap_apply, hs]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  · obtain ⟨q, hqy, hqq₁⟩ := exists_comap_eq_of_isPushout (B := B) y.asIdeal.ResidueField
      (Ideal.ker_algebraMap_residueField _) q₁ hq₁
    have h₁ : comap (algebraMap A (A ⊗[R₀] B₀)) (comap (e₀ : A ⊗[R₀] B₀ →+* B) q) = y := by
      rw [← comap_comp_apply, ← hqy]
      congr 1
      exact RingHom.ext fun a ↦ e₀.commutes a
    have h₂ : comap (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ A₁ A)
        (AlgHom.id R₀ B₀) : A₁ ⊗[R₀] B₀ →+* A ⊗[R₀] B₀) (comap (e₀ : A ⊗[R₀] B₀ →+* B) q) =
        q₁ := by
      rw [← comap_comp_apply, ← hqq₁]
      rfl
    have := hflat _ h₁
    rwa [h₂] at this

/-- **Noetherian approximation along a fibre.** Let `B` be a flat, finitely presented `A`-algebra
with a section `s`, and `y` a prime of `A`. Then `B` and `s` descend to a finite type algebra `B₁`
with a section `s₁` over a noetherian ring `A₁` mapping to `A`, such that `B₁` is flat over `A₁`
at the points lying over `y ∩ A₁`.

Each point of `Spec B` has a neighbourhood on which some noetherian model is flat (Stacks `00R6`,
`Module.exists_fg_flat_localization_tensor`, and openness of the flat locus). The fibre over `y`
is quasi-compact, so a single model suffices, and every point of the fibre of the model lies under
a point of the fibre of `B`. -/
theorem exists_isPushout_forall_flat (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] (s : B →ₐ[A] A) (y : PrimeSpectrum A) :
    ∃ (A₁ B₁ : Type u) (_ : CommRing A₁) (_ : CommRing B₁) (_ : Algebra A₁ A) (_ : Algebra A₁ B₁)
      (_ : Algebra B₁ B) (_ : Algebra A₁ B) (_ : IsScalarTower A₁ A B)
      (_ : IsScalarTower A₁ B₁ B),
      IsNoetherianRing A₁ ∧ Algebra.FiniteType A₁ B₁ ∧ Algebra.IsPushout A₁ A B₁ B ∧
      ∃ s₁ : B₁ →ₐ[A₁] A₁, (∀ b, algebraMap A₁ A (s₁ b) = s (algebraMap B₁ B b)) ∧
        ∀ q : PrimeSpectrum B₁,
          comap (algebraMap A₁ B₁) q = comap (algebraMap A₁ A) y →
          Module.Flat A₁ (Localization.AtPrime q.asIdeal) := by
  classical
  obtain ⟨A₀, B₀, _, _, _, _, hA₀, hB₀, hpush, s₀, hs⟩ :=
    Algebra.FinitePresentation.exists_fg_subalgebra_with_section s
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : Module.Flat A (A ⊗[A₀] B₀) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv A₀ A B₀ B).toLinearEquiv
  obtain ⟨R₁, hR₁, hflat⟩ := exists_fg_forall_flat_localization_tensor (R₀ := A₀) (S₀ := B₀) y
  have : Algebra.FiniteType A₀ R₁ := (Subalgebra.fg_iff_finiteType _).mp hR₁
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing A₀ R₁
  exact exists_isPushout_forall_flat_of_tensorProduct (A₁ := R₁) s s₀ hs y hflat

end PrimeSpectrum
