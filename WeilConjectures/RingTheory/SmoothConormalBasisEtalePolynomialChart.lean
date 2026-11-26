/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.RingTheory.ConormalChartUnramifiedLocalization
import WeilConjectures.RingTheory.UnramifiedSmoothConormalChartFlat
import Mathlib.RingTheory.Smooth.Fiber
/-!
# An étale polynomial chart along the zero section

We construct, for a smooth polynomial quotient whose equation classes form a basis of the
conormal module, a principal localization of a polynomial ring over the quotient that is étale
over a polynomial ring over the base, following the construction of `B'_g` in the proof of
[Stacks, Tag 07CH].

## References

* [Stacks, Tag 07CH]
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

private theorem exists_conormal_matrix
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (hb : ∀ j : Fin c,
      b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) :
    ∃ a : Fin n → Fin c → MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f),
      ∀ j k, ∑ i, Ideal.Quotient.mk (Ideal.span (Set.range f))
        (MvPolynomial.pderiv i (f j)) * a i k = if j = k then 1 else 0 := by
  classical
  let J := Ideal.span (Set.range f)
  let C := MvPolynomial (Fin n) R ⧸ J
  have hsurj : Function.Surjective (algebraMap (MvPolynomial (Fin n) R) C) :=
    Ideal.Quotient.mk_surjective
  obtain ⟨l₀, hl⟩ := (FormallySmooth.iff_split_injection (R := R) hsurj).mp
    (inferInstance : FormallySmooth R C)
  let K := RingHom.ker (algebraMap (MvPolynomial (Fin n) R) C)
  have hK : K = J := Ideal.mk_ker
  let q := Ideal.Cotangent.equivOfEq K J hK
  let l : (_root_.TensorProduct (MvPolynomial (Fin n) R) C
      (KaehlerDifferential R (MvPolynomial (Fin n) R)))
      →ₗ[C] J.Cotangent := (q.toLinearMap.comp l₀).extendScalarsOfSurjective hsurj
  let d := (KaehlerDifferential.mvPolynomialBasis R (Fin n)).baseChange C
  let a : Fin n → Fin c → C := fun i k ↦ b.repr (l (d i)) k
  refine ⟨a, ?_⟩
  intro j k
  let x : K := ⟨f j, by rw [hK]; exact Ideal.subset_span (Set.mem_range_self j)⟩
  have hq : q (K.toCotangent x) = b j := by
    rw [Ideal.Cotangent.equivOfEq_toCotangent, hb]
    congr 1
  have hd : _root_.TensorProduct.tmul (MvPolynomial (Fin n) R) (1 : C)
      (KaehlerDifferential.D R (MvPolynomial (Fin n) R) (f j)) =
      ∑ i, Ideal.Quotient.mk J (MvPolynomial.pderiv i (f j)) • d i := by
    apply d.repr.injective
    ext i
    rw [Module.Basis.baseChange_repr_tmul]
    simp only [KaehlerDifferential.mvPolynomialBasis_repr_apply, Algebra.smul_def,
      mul_one]
    simp only [map_sum, map_smul, Module.Basis.repr_self]
    simp [Finsupp.single_apply, eq_comm]
    rfl
  have he := congrArg (fun z ↦ b.repr (q z) k)
    (DFunLike.congr_fun hl (K.toCotangent x))
  change b.repr (l (_root_.TensorProduct.tmul (MvPolynomial (Fin n) R) (1 : C)
    (KaehlerDifferential.D R (MvPolynomial (Fin n) R) (f j)))) k =
    b.repr (q (K.toCotangent x)) k at he
  rw [hd, hq] at he
  simpa [a, map_sum, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply] using he

/-- For a smooth polynomial quotient `C = R[x]/(f)` whose equation classes form a basis of the
conormal module, adjoining one variable per equation admits a localization `C[y]_g`, with `g` of
constant coefficient one, together with an `R`-algebra map `θ : R[x] → C[y]_g` making `C[y]_g`
étale over `R[x]`; moreover `θ` restricts to the canonical map on constants. -/
/- Core construction of the chart, retaining the canonical map on constants.

The additional constant-map equation records the retraction part of the construction and is
used to extract the statement below.
-/
theorem exists_etale_polynomial_chart_core
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (hb : ∀ j : Fin c,
      b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) :
    ∃ g : MvPolynomial (Fin c) (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)),
      MvPolynomial.constantCoeff g = 1 ∧
      ∃ θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        @Etale (MvPolynomial (Fin n) R) (Localization.Away g) _ _
            θ.toRingHom.toAlgebra ∧
          θ.toRingHom.comp MvPolynomial.C = Algebra.ofId R (Localization.Away g) := by
  classical
  obtain ⟨a, ha⟩ := exists_conormal_matrix R n c f b hb
  obtain ⟨g, hg, hu⟩ := exists_unramified_conormal_polynomial_chart R n c f a ha
  let C := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let D := MvPolynomial (Fin c) C
  let θ₀ : MvPolynomial (Fin n) R →ₐ[R] D := MvPolynomial.aeval
    (fun i ↦ MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (Set.range f))
      (MvPolynomial.X i)) - ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X j)
  let θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g :=
    (IsScalarTower.toAlgHom R D (Localization.Away g)).comp θ₀
  let : Algebra (MvPolynomial (Fin n) R) (Localization.Away g) :=
    θ.toRingHom.toAlgebra
  let : SMul (MvPolynomial (Fin n) R) (Localization.Away g) :=
    θ.toRingHom.toAlgebra.toSMul
  let : Module (MvPolynomial (Fin n) R) (Localization.Away g) :=
    θ.toRingHom.toAlgebra.toModule
  have : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq' θ.comp_algebraMap.symm
  have : FormallyUnramified (MvPolynomial (Fin n) R) (Localization.Away g) := hu
  have : Module.Flat (MvPolynomial (Fin n) R) (Localization.Away g) :=
    flat_of_unramified_smooth_conormal_chart R n c f b g θ hu
  have : FinitePresentation D (Localization.Away g) :=
    IsLocalization.Away.finitePresentation g
  have : FinitePresentation R (Localization.Away g) :=
    FinitePresentation.trans R D (Localization.Away g)
  have : FinitePresentation (MvPolynomial (Fin n) R) (Localization.Away g) :=
    FinitePresentation.of_restrict_scalars_finitePresentation R
      (MvPolynomial (Fin n) R) (Localization.Away g)
  refine ⟨g, hg, θ, Etale.of_formallyUnramified_of_flat, ?_⟩
  exact θ.comp_algebraMap

/-- For a smooth polynomial quotient `C = R[x]/(f)` whose equation classes form a basis of the
conormal module, some localization `C[y]_g`, with `g` of constant coefficient one, is étale over
`R[x]` via an `R`-algebra map `θ : R[x] → C[y]_g`. -/
theorem exists_etale_polynomial_chart_of_conormal_basis
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (hb : ∀ j : Fin c,
      b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) :
    ∃ g : MvPolynomial (Fin c) (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)),
      MvPolynomial.constantCoeff g = 1 ∧
      ∃ θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        @Etale (MvPolynomial (Fin n) R) (Localization.Away g) _ _
          θ.toRingHom.toAlgebra := by
  obtain ⟨g, hg, θ, hθ, _⟩ :=
    exists_etale_polynomial_chart_core R n c f b hb
  exact ⟨g, hg, θ, hθ⟩

end Algebra
