/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.RingTheory.RelativeComponentConstructible
public import WeilConjectures.RingTheory.DiscreteValuationRing.Dominating
public import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# The relative connected component of a section is stable under generalization

Let `B` be a flat, finitely presented `A`-algebra whose fibres are geometrically reduced, and
`s : B →ₐ[A] A` a section. The relative connected component of `s` (the primes `q` of `B` lying in
the connected component of `s⁻¹ (q ∩ A)` in their fibre) is stable under generalization
(Stacks `055Q`).

The proof follows Stacks. Over a discrete valuation ring, an idempotent of the generic fibre of a
flat algebra with reduced special fibre extends to the algebra (Stacks `055J`,
`IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem`), so two sections meeting the
same connected component of the special fibre meet the same connected component of the generic
fibre. Over a noetherian base, a specialisation is traced by a discrete valuation ring
(`Ideal.exists_isDiscreteValuationRing_of_lt`) and the relative component is compatible with base
change (Stacks `055M`). The general case reduces to the noetherian one by noetherian approximation,
flatness descending at the finitely many points needed to cover the relative component of a fibre
(Stacks `00R6`).

## Main statements

- `PrimeSpectrum.mem_relativeComponent_of_isDiscreteValuationRing`: the discrete valuation ring
  case.
- `PrimeSpectrum.mem_relativeComponent_of_le_of_isNoetherianRing`: the noetherian case.
- `PrimeSpectrum.stableUnderGeneralization_relativeComponent`: the general case (Stacks `055Q`).

## References

- Stacks Project, Tags `055J`, `055Q`
-/

@[expose] public section

universe u

open TensorProduct Topology IsLocalRing

/-- **Flatness at a point is stable under base change.** Let `S' = R' ⊗[R] S` and let `Q` be a
prime of `S'` lying over the prime `Q ∩ S` of `S`. If `S` is flat over `R` at `Q ∩ S`, then `S'` is
flat over `R'` at `Q`: the localization `S'_Q` is a localization of the flat `R'`-algebra
`R' ⊗[R] S_{Q ∩ S}`. -/
theorem Module.Flat.localization_of_isPushout {R R' S S' : Type*} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S] [Algebra R' S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
    (Q : Ideal S') [Q.IsPrime]
    (h : Module.Flat R (Localization.AtPrime (Q.comap (algebraMap S S')))) :
    Module.Flat R' (Localization.AtPrime Q) := by
  exact Module.Flat.localization_of_isPushout_aux Q h

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace PrimeSpectrum

/-- **The relative component over a discrete valuation ring** (Stacks `055J`). Let `R` be a
discrete valuation ring, `C` a finite type `R`-algebra with reduced special fibre, and `σ, τ` two
sections of `C`. Assume that `C` is flat over `R` at the points of the relative component of `σ`
in the special fibre. If the special point of `τ` lies in the relative component of `σ`, then so
does its generic point.

The connected component `Z` of the special point of `σ` in the noetherian special fibre is open
and closed there, so there is `g ∈ C` with `D(g) ∩ V(𝔪 C) = Z` and `C_g` flat over `R`. An
idempotent of `C_g[1/ϖ]` separating the generic points of `σ` and `τ` comes from an idempotent of
`C_g`, which would separate their special points in `Z`. -/
theorem mem_relativeComponent_of_isDiscreteValuationRing {R C : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing C] [Algebra R C] [Algebra.FiniteType R C]
    (σ τ : C →ₐ[R] R) (hred : IsReduced (ResidueField R ⊗[R] C))
    (hflat : ∀ q ∈ relativeComponent σ, comap (algebraMap R C) q = closedPoint R →
      Module.Flat R (Localization.AtPrime q.asIdeal))
    (hτ : comap (τ : C →+* R) (closedPoint R) ∈ relativeComponent σ) :
    comap (τ : C →+* R) ⟨⊥, Ideal.isPrime_bot⟩ ∈ relativeComponent σ := by
  sorry

/-- **The relative component is stable under generalization over a noetherian base.** Let `A` be
noetherian, `B` a finite type `A`-algebra with a section `s`, and `x' ≤ x` primes of `B` with `x`
in the relative component of `s`, lying over `y`. Assume that the fibre over `y` is geometrically
reduced and that `B` is flat over `A` at the points of the relative component lying over `y`.
Then `x'` lies in the relative component of `s`.

A discrete valuation ring `R` traces the specialisation `x' ⤳ x`, giving a second section `τ` of
`R ⊗[A] B` over `R`, and we conclude by
`PrimeSpectrum.mem_relativeComponent_of_isDiscreteValuationRing` and the compatibility of the
relative component with base change. -/
theorem mem_relativeComponent_of_le_of_isNoetherianRing {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B] (s : B →ₐ[A] A)
    {x x' : PrimeSpectrum B} (hle : x' ≤ x) (hx : x ∈ relativeComponent s)
    (hred : ∀ (L : Type u) [Field L] [Algebra A L],
      RingHom.ker (algebraMap A L) = (comap (algebraMap A B) x).asIdeal → IsReduced (L ⊗[A] B))
    (hflat : ∀ q ∈ relativeComponent s, comap (algebraMap A B) q = comap (algebraMap A B) x →
      Module.Flat A (Localization.AtPrime q.asIdeal)) :
    x' ∈ relativeComponent s := by
  classical
  rcases eq_or_ne x' x with rfl | hxx
  · exact hx
  have hlt : x'.asIdeal < x.asIdeal :=
    lt_of_le_of_ne hle fun h ↦ hxx (PrimeSpectrum.ext h)
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  obtain ⟨R, _, _, _, φ, hker, hmax⟩ := Ideal.exists_isDiscreteValuationRing_of_lt hlt
  letI : Algebra A R := (φ.comp (algebraMap A B)).toAlgebra
  let φA : B →ₐ[A] R := { φ with commutes' := fun _ ↦ rfl }
  let C := R ⊗[A] B
  let σ : C →ₐ[R] R := Algebra.TensorProduct.lift (Algebra.ofId R R)
    ((Algebra.ofId A R).comp s) fun _ _ ↦ Commute.all _ _
  let τ : C →ₐ[R] R := Algebra.TensorProduct.lift (Algebra.ofId R R) φA
    fun _ _ ↦ Commute.all _ _
  have hσ (b : B) : algebraMap A R (s b) = σ (algebraMap B C b) := by
    change _ = σ ((1 : R) ⊗ₜ[A] b)
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hrel := relativeComponent_eq_preimage_of_isPushout σ s hσ
  have hτφ (b : B) : τ (algebraMap B C b) = φ b := by
    change τ ((1 : R) ⊗ₜ[A] b) = φ b
    rw [Algebra.TensorProduct.lift_tmul]
    simp [φA]
  have hτB : (τ : C →+* R).comp (algebraMap B C) = φ := RingHom.ext hτφ
  have h₁ : comap (algebraMap B C) (comap (τ : C →+* R) (closedPoint R)) = x := by
    ext1
    rw [← comap_comp_apply, hτB]
    exact hmax
  have h₂ : comap (algebraMap B C) (comap (τ : C →+* R) ⟨⊥, Ideal.isPrime_bot⟩) = x' := by
    ext1
    rw [← comap_comp_apply, hτB]
    exact hker
  have hAR : comap (algebraMap A R) (closedPoint R) = comap (algebraMap A B) x := by
    ext1
    change Ideal.comap ((φ.comp (algebraMap A B))) (maximalIdeal R) = _
    rw [← Ideal.comap_comap, hmax]
    rfl
  have hCB (q : PrimeSpectrum C) : comap (algebraMap A B) (comap (algebraMap B C) q) =
      comap (algebraMap A R) (comap (algebraMap R C) q) := by
    rw [← comap_comp_apply, ← comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have key := mem_relativeComponent_of_isDiscreteValuationRing σ τ ?_ ?_
    (by rw [hrel, Set.mem_preimage, h₁]; exact hx)
  · rwa [hrel, Set.mem_preimage, h₂] at key
  · -- the special fibre `κ ⊗[R] (R ⊗[A] B) = κ ⊗[A] B` is reduced
    letI : Algebra A (ResidueField R) :=
      ((algebraMap R (ResidueField R)).comp (algebraMap A R)).toAlgebra
    haveI : IsScalarTower A R (ResidueField R) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have := hred (ResidueField R) (by
      rw [← congrArg PrimeSpectrum.asIdeal hAR]
      change RingHom.ker ((residue R).comp (algebraMap A R)) = _
      rw [← RingHom.comap_ker, IsLocalRing.ker_residue]
      rfl)
    exact isReduced_of_injective
      (Algebra.TensorProduct.cancelBaseChange A R R (ResidueField R) B).toRingHom
      (Algebra.TensorProduct.cancelBaseChange A R R (ResidueField R) B).injective
  · intro q hq hqc
    have hq₁ : comap (algebraMap B C) q ∈ relativeComponent s := by
      rw [hrel] at hq
      exact hq
    have := hflat _ hq₁ (by rw [hCB, hqc, hAR])
    exact Module.Flat.localization_of_isPushout (R := A) (S := B) q.asIdeal this

/-- **Noetherian approximation along the relative component.** Let `B` be a flat, finitely
presented `A`-algebra with a section `s`, and `y` a prime of `A`. Then `B` and `s` descend to a
finite type algebra `B₁` with a section `s₁` over a noetherian subring `A₁` of `A`, such that `B₁`
is flat over `A₁` at the points of the relative component of `s₁` lying under `y`.

Each point of the relative component of `s` over `y` has a neighbourhood on which some
noetherian model is flat (Stacks `00R6`, `Module.exists_fg_flat_localization_tensor`, and openness
of the flat locus). This part of the fibre is quasi-compact, so finitely many models suffice. -/
theorem exists_isPushout_forall_flat (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] (s : B →ₐ[A] A) (y : PrimeSpectrum A) :
    ∃ (A₁ B₁ : Type u) (_ : CommRing A₁) (_ : CommRing B₁) (_ : Algebra A₁ A) (_ : Algebra A₁ B₁)
      (_ : Algebra B₁ B) (_ : Algebra A₁ B) (_ : IsScalarTower A₁ A B)
      (_ : IsScalarTower A₁ B₁ B),
      IsNoetherianRing A₁ ∧ Algebra.FiniteType A₁ B₁ ∧ Algebra.IsPushout A₁ A B₁ B ∧
      ∃ s₁ : B₁ →ₐ[A₁] A₁, (∀ b, algebraMap A₁ A (s₁ b) = s (algebraMap B₁ B b)) ∧
        ∀ q ∈ relativeComponent s₁,
          comap (algebraMap A₁ B₁) q = comap (algebraMap A₁ A) y →
          Module.Flat A₁ (Localization.AtPrime q.asIdeal) := by
  sorry

/-- **Geometrically reduced fibres descend along base change.** Let `B = A ⊗[A₁] B₁` and let `y` be
a prime of `A`. If `L ⊗[A] B` is reduced for every field `L` over `A`, then `L ⊗[A₁] B₁` is reduced
for every field `L` over `A₁` whose kernel is `y ∩ A₁`: a field `Ω` containing both `L` and `κ(y)`
gives an embedding of `L ⊗[A₁] B₁` into `Ω ⊗[A₁] B₁ = Ω ⊗[A] B`. -/
theorem isReduced_tensorProduct_of_isPushout {A₁ A B₁ B : Type u} [CommRing A₁] [CommRing A]
    [CommRing B₁] [CommRing B] [Algebra A₁ A] [Algebra A₁ B₁] [Algebra A B] [Algebra B₁ B]
    [Algebra A₁ B] [IsScalarTower A₁ A B] [IsScalarTower A₁ B₁ B] [Algebra.IsPushout A₁ A B₁ B]
    (hred : ∀ (L : Type u) [Field L] [Algebra A L], IsReduced (L ⊗[A] B)) (y : PrimeSpectrum A)
    (L : Type u) [Field L] [Algebra A₁ L]
    (hL : RingHom.ker (algebraMap A₁ L) = (comap (algebraMap A₁ A) y).asIdeal) :
    IsReduced (L ⊗[A₁] B₁) := by
  classical
  obtain ⟨P, hP, -⟩ := Algebra.exists_isPrime_comap_includeLeft_eq (A := A₁) (B := A) (K := L)
    (Field.toIsField L) y.asIdeal hL
  let Ω := P.ResidueField
  have := hred Ω
  let e₁ : Ω ⊗[A₁] B₁ ≃+* Ω ⊗[A] B :=
    (Algebra.TensorProduct.cancelBaseChange A₁ A Ω Ω B₁).symm.toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[A] Ω)
        (Algebra.IsPushout.equiv A₁ A B₁ B)).toRingEquiv
  let e₂ : Ω ⊗[L] (L ⊗[A₁] B₁) ≃+* Ω ⊗[A₁] B₁ :=
    (Algebra.TensorProduct.cancelBaseChange A₁ L Ω Ω B₁).toRingEquiv
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : L ⊗[A₁] B₁ →ₐ[L] Ω ⊗[L] (L ⊗[A₁] B₁)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap L Ω).injective
  exact isReduced_of_injective
    ((e₁.toRingHom.comp e₂.toRingHom).comp Algebra.TensorProduct.includeRight.toRingHom)
    ((e₁.injective.comp e₂.injective).comp hinj)

/-- **The relative component of a section is stable under generalization** (Stacks `055Q`). Let
`B` be a flat, finitely presented `A`-algebra with geometrically reduced fibres, and `s` a section
of `B`. Then the relative component of `s` is stable under generalization. -/
theorem stableUnderGeneralization_relativeComponent {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] [Algebra.FinitePresentation A B]
    (hred : ∀ (L : Type u) [Field L] [Algebra A L], IsReduced (L ⊗[A] B)) (s : B →ₐ[A] A) :
    StableUnderGeneralization (relativeComponent s) := by
  intro x x' hspec hx
  set y := comap (algebraMap A B) x
  obtain ⟨A₁, B₁, _, _, _, _, _, _, _, _, _, _, _, s₁, hs₁, hflat⟩ :=
    exists_isPushout_forall_flat A B s y
  have hy (q : PrimeSpectrum B) : comap (algebraMap A₁ B₁) (comap (algebraMap B₁ B) q) =
      comap (algebraMap A₁ A) (comap (algebraMap A B) q) := by
    rw [← comap_comp_apply, ← comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have hrel := relativeComponent_eq_preimage_of_isPushout s s₁ hs₁
  have hx₁ : comap (algebraMap B₁ B) x ∈ relativeComponent s₁ := by
    rw [hrel] at hx
    exact hx
  have hle : comap (algebraMap B₁ B) x' ≤ comap (algebraMap B₁ B) x := by
    rw [← asIdeal_le_asIdeal]
    exact Ideal.comap_mono ((le_iff_specializes x' x).mpr hspec)
  have key := mem_relativeComponent_of_le_of_isNoetherianRing s₁ hle hx₁
    (fun L _ _ hL ↦ isReduced_tensorProduct_of_isPushout hred y L (hL.trans (by rw [hy])))
    (fun q hq hqx ↦ hflat q hq (hqx.trans (hy x)))
  rw [hrel]
  exact key

end PrimeSpectrum
