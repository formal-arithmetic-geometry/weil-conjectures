/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.FiniteStability
import Sheaf.RingTheory.LocalCompleteIntersectionFieldChange

/-! # Tensor transition and complete-intersection fibres

Source: Stacks Project, Algebra, Tag 00SN (lemma-base-change-syntomic), with the
residue-fibre comparison in Tag 00SM (lemma-syntomic-descends).
(blueprint: lem-trf-lci-fibre-tensor-transition).

The transparent proposition `lciFibreTensorTransition` installs only the canonical algebra
structures, so its tensor products use precisely the specified maps. Mathlib's `Ideal.Fiber`
places the residue field on the left; the displayed fibre comparison is written with both
tensor products commuted. No choice of maps or algebra structures is quantified over.
-/

@[expose] public section

set_option autoImplicit false

universe u₀ uₖ uⱼ v w

open scoped TensorProduct

namespace Algebra

/-- The full tensor-transition assertion, with its canonical scalar actions made explicit.
Source: Stacks Project, Algebra, Tags 00SN and 00SM, and Definition 00S9.
(blueprint: lem-trf-lci-fibre-tensor-transition).

All `let` bindings here construct the specified rings, maps and scalar actions. They are
inside this transparent definition, not theorem binders. The existential finite-type witnesses
allow the recorded `IsLocalCompleteIntersection` predicate to be applied to the fibre rings.
The two equations for the fibre isomorphism preserve the maps from `Cₖ` and `κ(q)`.
-/
noncomputable def lciFibreTensorTransition
    (R₀ : Type u₀) (Rₖ : Type uₖ) (Rⱼ : Type uⱼ) (B₀ : Type v) (C₀ : Type w)
    [CommRing R₀] [CommRing Rₖ] [CommRing Rⱼ] [CommRing B₀] [CommRing C₀]
    [Algebra R₀ Rₖ] [Algebra R₀ Rⱼ] [Algebra R₀ B₀] [Algebra R₀ C₀]
    (α : Rₖ →ₐ[R₀] Rⱼ) (φ₀ : B₀ →ₐ[R₀] C₀) : Prop :=
  let Bₖ := Rₖ ⊗[R₀] B₀
  let Bⱼ := Rⱼ ⊗[R₀] B₀
  let Cₖ := Rₖ ⊗[R₀] C₀
  let Cⱼ := Rⱼ ⊗[R₀] C₀
  let φₖ := (Algebra.TensorProduct.lTensor (R := R₀) (S := Rₖ) Rₖ φ₀).toRingHom
  let φⱼ := (Algebra.TensorProduct.lTensor (R := R₀) (S := Rⱼ) Rⱼ φ₀).toRingHom
  let β := (Algebra.TensorProduct.map α (AlgHom.id R₀ B₀)).toRingHom
  let γ := (Algebra.TensorProduct.map α (AlgHom.id R₀ C₀)).toRingHom
  letI : Algebra Bₖ Cₖ := φₖ.toAlgebra
  letI : Algebra Bⱼ Cⱼ := φⱼ.toAlgebra
  letI : Algebra Bₖ Bⱼ := β.toAlgebra
  RingHom.Flat φₖ → RingHom.FinitePresentation φₖ →
    (∀ p : PrimeSpectrum Bₖ,
      ∃ h : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber Cₖ),
        @IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber Cₖ) _ _ _ h) →
    (∃ θ : (Bⱼ ⊗[Bₖ] Cₖ) ≃ₐ[Bⱼ] Cⱼ,
      (∀ (r : Rⱼ) (b : B₀) (s : Rₖ) (c : C₀),
        θ ((r ⊗ₜ[R₀] b) ⊗ₜ[Bₖ] (s ⊗ₜ[R₀] c)) =
          (r * α s) ⊗ₜ[R₀] (φ₀ b * c)) ∧
      (∀ (r : Rⱼ) (c : C₀),
        θ.symm (r ⊗ₜ[R₀] c) = (r ⊗ₜ[R₀] (1 : B₀)) ⊗ₜ[Bₖ] ((1 : Rₖ) ⊗ₜ[R₀] c)) ∧
      (∀ x : Bⱼ, θ (x ⊗ₜ[Bₖ] 1) = φⱼ x)) ∧
    (∀ q : PrimeSpectrum Bⱼ,
      let p := PrimeSpectrum.comap β q
      let ι := Ideal.ResidueField.map p.asIdeal q.asIdeal β rfl
      letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := ι.toAlgebra
      (∃ e : q.asIdeal.Fiber Cⱼ ≃ₐ[q.asIdeal.ResidueField]
          (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber Cₖ)),
        (∀ c : Cₖ, e (1 ⊗ₜ[Bⱼ] γ c) =
          1 ⊗ₜ[p.asIdeal.ResidueField] (1 ⊗ₜ[Bₖ] c)) ∧
        (∀ a : q.asIdeal.ResidueField, e (a ⊗ₜ[Bⱼ] 1) =
          a ⊗ₜ[p.asIdeal.ResidueField] (1 : p.asIdeal.Fiber Cₖ))) ∧
      Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber Cₖ)) ∧
    RingHom.Flat φⱼ ∧ RingHom.FinitePresentation φⱼ ∧
    (∀ q : PrimeSpectrum Bⱼ,
      ∃ h : Algebra.FiniteType q.asIdeal.ResidueField (q.asIdeal.Fiber Cⱼ),
        @IsLocalCompleteIntersection q.asIdeal.ResidueField (q.asIdeal.Fiber Cⱼ) _ _ _ h)

/-- Arbitrary scalar transition preserves flat finite presentation and complete-intersection
fibres, with the explicit tensor and residue-fibre comparisons.
Source: Stacks Project, Algebra, Tag 00SN and the displayed comparison of Tag 00SM.
(blueprint: lem-trf-lci-fibre-tensor-transition).

Proof (the six steps of the DAG node):
1. The maps `φⱼ` and `γ` agree on `Bₖ`. The tensor pushout universal property constructs
   `θ` with the displayed formula. Maps from `Rⱼ` and `C₀` construct its proposed inverse;
   balancing over `Bₖ` makes that inverse `Bⱼ`-linear.
2. Compute both composites on pure tensors. Balancing gives
   `((r ⊗ b) ⊗ (s ⊗ c)) = (r * α(s) ⊗ 1) ⊗ (1 ⊗ φ₀(b) * c)`.
   Pure tensors generate, so the maps are inverse; also `θ(x ⊗ 1) = φⱼ(x)`.
3. Contract a prime `q` along `β` to obtain `p`. The kernel and factorization clauses of
   lem-weil-pbc-prime-residue-field-algebra give the canonical residue-field map `ι`.
   Its kernel is zero since it is a unital field map.
4. Apply lem-weil-pbc-tensor-cancel-base-change to `Bₖ → Bⱼ → κ(q)` and to
   `Bₖ → κ(p) → κ(q)`, and commute the tensor factors. On canonical generators the
   resulting comparison sends `1 ⊗ γ(c)` to `1 ⊗ (1 ⊗ c)` and `a ⊗ 1` to `a ⊗ 1`.
5. Use lem-weil-pbc-flat-module-base-change and clause (1) of
   lem-weil-pbc-finite-presentation-base-change-composition, transporting across `θ`.
   Base changing to `κ(p)` also gives finite presentation, hence finite type of that fibre.
6. Apply lem-weil-pbc-lci-field-change to that finite-type fibre and `κ(p) → κ(q)`.
   Transport its principal-open cover, presentations and Krull dimensions across the fibre
   isomorphism. This includes zero fibres; no flatness or finiteness of `α` is used.
-/
theorem lci_fibre_tensor_transition
    (R₀ : Type u₀) (Rₖ : Type uₖ) (Rⱼ : Type uⱼ) (B₀ : Type v) (C₀ : Type w)
    [CommRing R₀] [CommRing Rₖ] [CommRing Rⱼ] [CommRing B₀] [CommRing C₀]
    [Algebra R₀ Rₖ] [Algebra R₀ Rⱼ] [Algebra R₀ B₀] [Algebra R₀ C₀]
    (α : Rₖ →ₐ[R₀] Rⱼ) (φ₀ : B₀ →ₐ[R₀] C₀) :
    lciFibreTensorTransition R₀ Rₖ Rⱼ B₀ C₀ α φ₀ := by
  sorry

end Algebra
