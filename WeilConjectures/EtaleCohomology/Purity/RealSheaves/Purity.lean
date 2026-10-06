/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Purity of real lisse Weil sheaves on curves

This file states the climax of the block: an `ι`-real lisse Weil sheaf on a smooth
geometrically connected curve over a finite field is, constituent by constituent, punctually
`ι`-pure of the expected weight.

The route is the classical one. A rank-one lisse Weil sheaf has finite geometric image
(`AlgebraicGeometry.WeilGroup.IsLisse.finite_geometric_image`), hence is punctually pure of
the weight of its Frobenius scalar
(`AlgebraicGeometry.WeilGroup.IsLisse.isPunctuallyPure_of_finrank_eq_one`). The
Rankin–Selberg argument, applied to the even tensor powers of a real sheaf on an affine curve,
turns a bound on the determinant weights of the constituents into a bound on all local
eigenvalues (`AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_isReal`). Semi-continuity
propagates a weight bound across the boundary of an open subcurve
(`AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_of_hasWeightsAtMost`). Finally an
exterior power of the semisimplification squeezes the eigenvalues of a single weight block
from both sides
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`).

## Implementation notes

The arithmetic and geometric monodromy groups of `sk-d-real-monodromy` are the Zariski
closures of `ρ (W (C₀))` and `ρ (π₁ C)` inside `GL V`. Zariski closures of subgroups of `GL V`
are owned by the algebraic groups block (`sk-d-monodromy`, `sk-d-central`) and do not exist
here; only the map `AlgebraicGeometry.WeilGroup.toLinearAut` whose images they are closures of
is recorded, and the positive central Frobenius representative of `sk-d-central` is left to
that block.

The theorems below quantify over an arbitrary `AlgebraicGeometry.WeilGroup p`, whose data does
not record that `ker deg` is the geometric fundamental group of `C`. They are therefore not
consequences of that data alone: their proofs need the Grothendieck–Lefschetz trace formula
relating `AlgebraicGeometry.WeilGroup.eulerSeries` to compactly supported cohomology, and the
identification of `H¹(C)` with the dual of a Tate module. Both need the Galois category of
finite étale covers of a scheme, hence Mathlib's
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`, to even be stated. The statements
recorded here are the blueprint's; they become provable once `AlgebraicGeometry.WeilGroup` is
rebased on the étale fundamental group and the trace formula is available.

## Main definitions

- `AlgebraicGeometry.WeilGroup.toLinearAut`

## Main statements

- `AlgebraicGeometry.WeilGroup.IsLisse.finite_geometric_image`
- `AlgebraicGeometry.WeilGroup.IsLisse.isPunctuallyPure_of_finrank_eq_one`
- `AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_isReal`, and its unfolded form
  `AlgebraicGeometry.WeilGroup.sq_norm_le_rpow_of_isReal`
- `AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_of_hasWeightsAtMost`
- `AlgebraicGeometry.BoundaryDatum.isPunctuallyPure_of_isPunctuallyPure_restrict`
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V)

/-- Blueprint `sk-d-real-monodromy`: Arithmetic monodromy and a central representative.

The Weil representation `ρ` viewed as a homomorphism to the automorphism group of `V`: every
`ρ g` is invertible because `g` is invertible, so `ρ` factors through `GL V = (V →ₗ V)ˣ`,
which is multiplicatively equivalent to `V ≃ₗ V`. The arithmetic and geometric monodromy
groups of `sk-d-monodromy` are the Zariski closures of the images of `W (C₀)` and of `π₁ C`
under this map. -/
noncomputable def toLinearAut : W.carrier →* (V ≃ₗ[PadicAlgCl l] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (PadicAlgCl l) V).toMonoidHom.comp
    ρ.asGroupHom

variable (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `sk-p-real-rankone`: Purity of rank-one Weil sheaves.

The geometric image `χ (π₁ U)` of a rank-one lisse Weil sheaf on a smooth geometrically
connected curve `U₀ / 𝔽_q` is finite.

This is the heart of the matter: the `ℓ`-adic logarithm turns an `N`-th power of `χ`
restricted to `π₁ U` into a continuous additive map invariant under conjugation by `γ`, and
such a map is a Frobenius-fixed class in `H¹ (U, ℚ̄_ℓ)`, which vanishes because on a proper
curve `H¹` is dual to a Tate module with no Frobenius-fixed vector, and the boundary
contribution for an open curve is a nonzero power of `q`. -/
theorem IsLisse.finite_geometric_image [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] (hrank : Module.finrank (PadicAlgCl l) V = 1)
    (hρ : W.IsLisse l ρ) :
    (Set.range fun g : W.geometric ↦ ρ g).Finite := by
  sorry

/-- Blueprint `sk-p-real-rankone`: Purity of rank-one Weil sheaves.

A rank-one lisse Weil sheaf `L` on a smooth geometrically connected curve `U₀ / 𝔽_q`, with
character `χ : W (U₀) → ℚ̄_ℓ ˣ`, is punctually `ι`-pure of weight
`w = 2 log |ι c| / log q`, where `c = χ γ` is the value at the chosen degree-one lift.

Once the geometric image is finite (`AlgebraicGeometry.WeilGroup.IsLisse.finite_geometric_image`),
`χ` is a root of unity times the constant character `c ^ deg`, so the local scalar at a point
of degree `e` has complex modulus `|ι c| ^ e = q ^ (e * w / 2)`. -/
theorem IsLisse.isPunctuallyPure_of_finrank_eq_one [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] (hrank : Module.finrank (PadicAlgCl l) V = 1)
    (hρ : W.IsLisse l ρ) :
    W.IsPunctuallyPure l ρ ι
      (frobeniusWeight ι (Nat.card K) (LinearMap.det (ρ W.frobeniusLift))) := by
  sorry

end WeilGroup

namespace WeilGroup

section DetWeight

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V V' : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V] [AddCommGroup V']
  [Module (PadicAlgCl l) V'] [FiniteDimensional (PadicAlgCl l) V']
  {ρ : Representation (PadicAlgCl l) W.carrier V} (ι : PadicAlgCl l →+* ℂ)

omit [Finite K] [IsCurve p] in
/-- The determinant line `ULift ℚ̄_ℓ` is one-dimensional. -/
theorem finrank_ulift_padicAlgCl :
    Module.finrank (PadicAlgCl l) (ULift.{u} (PadicAlgCl l)) = 1 :=
  (ULift.moduleEquiv (R := PadicAlgCl l) (M := PadicAlgCl l)).finrank_eq.trans
    (Module.finrank_self _)

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The determinant line `ULift ℚ̄_ℓ` with `g` acting by `det ρ(g)` has determinant `det ρ`. -/
theorem det_ofCharacter_detCharacter (g : W.carrier) :
    LinearMap.det (Representation.ofCharacter ρ.detCharacter (ULift.{u} (PadicAlgCl l)) g) =
      LinearMap.det (ρ g) := by
  change LinearMap.det ((ρ.detCharacter g : PadicAlgCl l) •
    (LinearMap.id : ULift.{u} (PadicAlgCl l) →ₗ[PadicAlgCl l] ULift.{u} (PadicAlgCl l))) = _
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_ulift_padicAlgCl, pow_one,
    Representation.coe_detCharacter_apply]

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The local eigenvalue of the determinant line at `x` is `det ρ(F_x)`. -/
theorem det_mem_localEigenvalues_ofCharacter (x : C.finitePoints) :
    LinearMap.det (ρ (W.frobenius x)) ∈
      W.localEigenvalues l (Representation.ofCharacter ρ.detCharacter (ULift.{u} (PadicAlgCl l)))
        x := by
  rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ULift.up 1) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Representation.ofCharacter_apply,
      Representation.coe_detCharacter_apply]
  · exact fun h ↦ one_ne_zero (congrArg ULift.down h)

variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]

/-- Blueprint `sk-p-real-rankone` (`lem-wf-determinantal-weight-exists`): a lisse Weil
representation `ρ` has determinant weight `wt_{ι, q}(det ρ(γ)) / rank ρ`, for the degree-one
lift `γ`: its determinant line is a rank-one lisse sheaf, hence punctually pure of the weight
of its Frobenius scalar. -/
theorem IsLisse.hasDetWeight (hρ : W.IsLisse l ρ) :
    W.HasDetWeight l ρ ι (frobeniusWeight ι (Nat.card K) (LinearMap.det (ρ W.frobeniusLift)) /
      Module.finrank (PadicAlgCl l) V) := by
  intro x
  have h := IsLisse.isPunctuallyPure_of_finrank_eq_one W l _ ι finrank_ulift_padicAlgCl
    (hρ.ofCharacter_detCharacter _) x _ (det_mem_localEigenvalues_ofCharacter x)
  rw [det_ofCharacter_detCharacter] at h
  rw [h]
  rcases eq_or_ne (Module.finrank (PadicAlgCl l) V) 0 with h0 | h0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    simp [h0, LinearMap.det_eq_one_of_subsingleton, frobeniusWeight]
  · field_simp

/-- Blueprint `sk-p-real-rankone`: the determinant of a lisse Weil representation takes
finitely many values on the geometric fundamental group, since the determinant line has finite
geometric image. -/
theorem IsLisse.hasFiniteGeometricDet (hρ : W.IsLisse l ρ) :
    ρ.HasFiniteGeometricDet W.deg := by
  have hfin := IsLisse.finite_geometric_image W l _ finrank_ulift_padicAlgCl
    (hρ.ofCharacter_detCharacter (ULift.{u} (PadicAlgCl l)))
  let f : (PadicAlgCl l)ˣ → Module.End (PadicAlgCl l) (ULift.{u} (PadicAlgCl l)) :=
    fun a ↦ (a : PadicAlgCl l) • LinearMap.id
  have hf : Function.Injective f := fun a b h ↦ Units.ext <| by
    simpa [f] using congrArg ULift.down (LinearMap.congr_fun h (ULift.up 1))
  refine Set.Finite.of_finite_image ?_ hf.injOn
  rw [← Set.range_comp]
  exact hfin

omit [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] in
/-- A nonzero Weil representation has at most one determinant weight, as soon as the curve
has a closed point. -/
theorem HasDetWeight.eq [Nontrivial V] {γ γ' : ℝ} (h : W.HasDetWeight l ρ ι γ)
    (h' : W.HasDetWeight l ρ ι γ') (x : C.finitePoints) : γ = γ' :=
  mul_left_cancel₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') ((h x).symm.trans (h' x))

omit [FiniteDimensional (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V']
  [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] in
/-- Determinant weights are invariant under equivalence of representations. -/
theorem HasDetWeight.of_equiv {σ : Representation (PadicAlgCl l) W.carrier V'} (e : ρ.Equiv σ)
    {γ : ℝ} (h : W.HasDetWeight l ρ ι γ) : W.HasDetWeight l σ ι γ := fun x ↦ by
  rw [e.det_apply, e.finrank_eq]
  exact h x

end DetWeight

section RankinSelberg

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V V' : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V] [AddCommGroup V']
  [Module (PadicAlgCl l) V'] [FiniteDimensional (PadicAlgCl l) V']
  {ρ : Representation (PadicAlgCl l) W.carrier V} {σ : Representation (PadicAlgCl l) W.carrier V'}
  (ι : PadicAlgCl l →+* ℂ)

/-- An irreducible representation is nonzero. -/
private theorem nontrivial_of_isIrreducible {V'' : Type*} [AddCommGroup V'']
    [Module (PadicAlgCl l) V''] {τ : Representation (PadicAlgCl l) W.carrier V''}
    (hτ : τ.IsIrreducible) : Nontrivial V'' := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

variable [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]

/-- Blueprint `sk-p-tensor`: the determinant weights of the constituents of a tensor product
`ℱ ⊗ 𝒢` of lisse Weil sheaves are bounded by `d₁ + d₂` if those of `ℱ` are bounded by `d₁` and
those of `𝒢` by `d₂`: by the tensor rule a constituent of `ℱ ⊗ 𝒢` has determinant weight
`dw (ℱ_i) + dw (𝒢_j)` for constituents `ℱ_i` of `ℱ` and `𝒢_j` of `𝒢`, and by
`sk-p-real-rankone` every lisse Weil sheaf has its determinant weight in the sense of
`AlgebraicGeometry.WeilGroup.HasDetWeight`, which is unique as soon as the curve has a closed
point `x₀`. -/
theorem le_add_of_isConstituent_tprod_of_hasDetWeight (x₀ : C.finitePoints)
    (hρ : W.IsLisse l ρ) (hσ : W.IsLisse l σ) {d₁ d₂ : ℝ}
    (hd₁ : ∀ {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
      [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
      (γ : ℝ), τ.IsConstituent ρ → W.HasDetWeight l τ ι γ → γ ≤ d₁)
    (hd₂ : ∀ {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
      [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
      (γ : ℝ), τ.IsConstituent σ → W.HasDetWeight l τ ι γ → γ ≤ d₂)
    {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
    [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
    (γ : ℝ) (hτ : τ.IsConstituent (ρ.tprod σ)) (hγ : W.HasDetWeight l τ ι γ) :
    γ ≤ d₁ + d₂ := by
  obtain ⟨N, M, hcov, ⟨e⟩⟩ := hτ.exists_covBy
  have hQirr := (Subrepresentation.isIrreducible_subquotient_iff hcov.le).2 hcov
  have hQlisse := (hρ.tprod hσ).subquotient M N
  obtain ⟨UV, SV, UE, SE, hV, hE, hVirr, hEirr, -, -, hsum⟩ :=
    Representation.exists_detWeight_eq_add_of_subquotient_tprod
      (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift ρ σ hcov.lt hQirr
      hQlisse.hasFiniteGeometricDet
  have h₁ := hd₁ _ _ ⟨hVirr, UV, SV, hV.le, ⟨SV.subquotientAsModuleLinearEquiv UV⟩⟩
    ((hρ.subquotient SV UV).hasDetWeight ι)
  have h₂ := hd₂ _ _ ⟨hEirr, UE, SE, hE.le, ⟨SE.subquotientAsModuleLinearEquiv UE⟩⟩
    ((hσ.subquotient SE UE).hasDetWeight ι)
  have := nontrivial_of_isIrreducible hQirr
  rw [detWeight_weightCharacter, detWeight_weightCharacter, detWeight_weightCharacter] at hsum
  rw [HasDetWeight.eq ι (hγ.of_equiv ι e) (hQlisse.hasDetWeight ι) x₀, hsum]
  exact add_le_add h₁ h₂

/-- The `ι`-weight of a square is twice the `ι`-weight. -/
private theorem frobeniusWeight_sq (qx : ℕ) (α : PadicAlgCl l) :
    frobeniusWeight ι qx (α ^ 2) = 2 * frobeniusWeight ι qx α := by
  simp only [frobeniusWeight, map_pow, norm_pow, Real.log_pow]
  push_cast
  ring

/-- The Rankin–Selberg step of `lem-rp-upper-bound`.

Let `ℋ` be a lisse Weil sheaf on a smooth geometrically connected affine curve whose inverse
local factors have nonnegative coefficients and whose constituents have determinant weight at
most `D`. Then every local eigenvalue of `ℋ` has `ι`-weight at most `D + 2`.

The eigenvalues `λ` of the geometric Frobenius on `H_c² (U, ℋ)` satisfy
`|ι λ| ≤ q ^ (D / 2 + 1)` (`lem-rp-hc2-eigenvalue-determinant-weight`), so by the Euler product
(`cor-rp-euler-product`) the Euler series of `ℋ` converges on the disc of radius
`R = q ^ (-(D / 2 + 1))`. By positivity every local factor converges there as well
(`lem-rp-positive-product-radius`), so its denominator `ι P_x (ℋ, T ^ e)` has no zero in that
disc; a local eigenvalue `β` produces the zero `T` with `T ^ e = (ι β)⁻¹`, whence
`|ι β| ^ (-1 / e) ≥ R`. -/
theorem frobeniusWeight_le_add_two_of_hasNonnegCoeffs [IsAffine C] (hρ : W.IsLisse l ρ)
    (hpos : ∀ x, (W.eulerFactor l ρ ι x).HasNonnegCoeffs) {D : ℝ}
    (hD : ∀ {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
      [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
      (γ : ℝ), τ.IsConstituent ρ → W.HasDetWeight l τ ι γ → γ ≤ D)
    (x : C.finitePoints) {β : PadicAlgCl l} (hβ : β ∈ W.localEigenvalues l ρ x) :
    frobeniusWeight ι (C.pointNorm x.1) β ≤ D + 2 := by
  classical
  open PowerSeries in
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq : 1 < q := by
    have := (Finite.one_lt_card_iff_nontrivial (α := K)).2 inferInstance
    rw [hqdef]
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  set e := p.degreeOver x.1
  have he : e ≠ 0 := p.degreeOver_ne_zero x.2
  -- the eigenvalues of the geometric Frobenius on `H_c²`
  set Tq := (Nat.card K : PadicAlgCl l) • ρ.toCoinvariants W.geometric W.frobeniusLift
  set S := Tq.charpoly.roots.map ι
  have hS : ∀ c ∈ S, ‖c‖ ≤ q ^ (D / 2 + 1) := by
    intro c hc
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hc
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp only [map_zero, norm_zero]
      positivity
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hμ
    obtain ⟨N, M, hNM, hc, hdet⟩ := exists_isConstituent_hasDetWeight_of_hasEigenvalue ρ ι hμ
    have hle := hD _ _ hc hdet
    have hpos : 0 < ‖ι (μ / Nat.card K)‖ := by
      simp [hμ0]
    rw [frobeniusWeight, div_le_iff₀ hlogq] at hle
    have h1 : ‖ι (μ / Nat.card K)‖ ≤ q ^ (D / 2) := by
      rw [← Real.exp_log hpos, Real.rpow_def_of_pos hq0]
      exact Real.exp_le_exp.2 (by nlinarith)
    have h2 : ‖ι μ‖ = q * ‖ι (μ / Nat.card K)‖ := by
      rw [map_div₀, norm_div, map_natCast, Complex.norm_natCast, ← hqdef]
      field_simp
    rw [h2, Real.rpow_add hq0, Real.rpow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 hq0.le
  -- the Euler series converges on the disc of radius `R`
  set R : ℝ := q ^ (-(D / 2 + 1))
  have hR : 0 < R := Real.rpow_pos_of_pos hq0 _
  have hRS : ∀ c ∈ S, ‖c‖ * R ≤ 1 := fun c hc ↦ by
    calc ‖c‖ * R ≤ q ^ (D / 2 + 1) * R := mul_le_mul_of_nonneg_right (hS c hc) hR.le
      _ = 1 := by rw [← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  set Dser : PowerSeries ℂ := ((Tq.charpolyRev.map ι : Polynomial ℂ) : PowerSeries ℂ)
    with hDdef
  have hDser : Dser = (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod := by
    rw [hDdef, LinearMap.charpolyRev_eq_prod_roots, Polynomial.map_multiset_prod_one_sub_C_mul_X,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun c _ ↦ by simp)
  have hDser0 : PowerSeries.constantCoeff Dser ≠ 0 := by
    rw [hDser, map_multiset_prod, Multiset.map_map, Multiset.prod_eq_one fun a ha ↦ by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
      simp]
    exact one_ne_zero
  obtain ⟨P₁, hP₁⟩ := exists_eulerSeries_mul_eq_coe ρ ι hρ
  have hL : W.eulerSeries l ρ ι = (P₁ : PowerSeries ℂ) * Dser⁻¹ := by
    rw [← hP₁, mul_assoc, PowerSeries.mul_inv_cancel _ hDser0, mul_one]
  -- the local polynomial at `x` and a zero of it
  set Qx : Polynomial ℂ := ((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ e)
  have hβ0 : ι β ≠ 0 :=
    (map_ne_zero ι).2 fun h ↦ zero_notMem_localEigenvalues (ρ := ρ) x (h ▸ hβ)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι β)⁻¹ (Nat.pos_of_ne_zero he)
  have hQz : Qx.eval z = 0 := by
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, hz, map_localPolynomial,
      Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨1 - Polynomial.C (ι β) * Polynomial.X,
      Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem ι hβ), ?_⟩)
    simp [hβ0]
  have hQ0 : Qx.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_pow,
      Polynomial.eval_X, zero_pow he, eval_zero_map_localPolynomial]
    exact one_ne_zero
  -- the zero lies outside the disc of radius `R`
  have hzR : R ≤ ‖z‖ := by
    by_contra! hlt
    set r : NNReal := ⟨(‖z‖ + R) / 2, by positivity⟩
    have hzr : ‖z‖ < r := by change ‖z‖ < (‖z‖ + R) / 2; linarith
    have hrR : (r : ℝ) < R := by change (‖z‖ + R) / 2 < R; linarith
    have hr : ∀ c ∈ S, ‖c‖ * r < 1 := fun c hc ↦ by
      rcases eq_or_ne c 0 with rfl | hc0
      · simp
      · calc ‖c‖ * r < ‖c‖ * R := mul_lt_mul_of_pos_left hrR (norm_pos_iff.2 hc0)
          _ ≤ 1 := hRS c hc
    have h1 : (r : ENNReal) ≤ (W.eulerSeries l ρ ι).radius := by
      rw [hL, hDser]
      exact PowerSeries.le_radius_coe_mul_inv_prod P₁ S hr
    have h2 := PowerSeries.radius_tprod_le_radius hpos (constantCoeff_eulerFactor ι)
      (multipliable_eulerFactors W l ρ ι) x
    have h3 : (‖z‖₊ : ENNReal) < ((Qx : PowerSeries ℂ)⁻¹).radius :=
      lt_of_lt_of_le (by exact_mod_cast hzr) (h1.trans h2)
    exact PowerSeries.eval_ne_zero_of_lt_radius_inv hQ0 h3 hQz
  -- hence `|ι β| ≤ q ^ (e (D / 2 + 1))`
  have hnorm : ‖ι β‖ ≤ q ^ ((e : ℝ) * (D / 2 + 1)) := by
    have hze : ‖z‖ ^ e = ‖ι β‖⁻¹ := by rw [← norm_pow, hz, norm_inv]
    have hRe : R ^ e ≤ ‖ι β‖⁻¹ := hze ▸ pow_le_pow_left₀ hR.le hzR e
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le] at hRe
    have := (le_inv_comm₀ (by positivity) (norm_pos_iff.2 hβ0)).1 hRe
    rwa [← Real.rpow_neg hq0.le, neg_mul, neg_neg, mul_comm] at this
  rw [frobeniusWeight, Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2, Nat.cast_pow,
    Real.log_pow, div_le_iff₀ (by positivity)]
  have := Real.log_le_log (norm_pos_iff.2 hβ0) hnorm
  rw [Real.log_rpow hq0] at this
  change 2 * Real.log ‖ι β‖ ≤ (D + 2) * (e * Real.log q)
  nlinarith

/-- The iterated Rankin–Selberg bound: if `ℱ` is lisse and `ι`-real on a smooth geometrically
connected affine curve and its constituents have determinant weight at most `d`, then every
local eigenvalue of `ℱ` has `ι`-weight at most `d + 2 ^ (-j)`, for every `j`.

For `j = 0` apply `AlgebraicGeometry.WeilGroup.frobeniusWeight_le_add_two_of_hasNonnegCoeffs`
to the tensor square `ℱ ⊗ ℱ`, whose inverse local factors are nonnegative
(`lem-rp-even-tensor-positivity`) and whose constituents have determinant weight at most `2 d`
(`sk-p-tensor`), and to the local eigenvalue `α ^ 2`; for `j + 1` apply the case `j` to
`ℱ ⊗ ℱ`, which is again lisse and `ι`-real. -/
theorem frobeniusWeight_le_add_inv_two_pow_of_isReal [IsAffine C] (j : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
      [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V),
      W.IsLisse l ρ → W.IsReal l ρ ι → ∀ {d : ℝ},
      (∀ {V'' : Type u} [AddCommGroup V''] [Module (PadicAlgCl l) V'']
        [FiniteDimensional (PadicAlgCl l) V''] (τ : Representation (PadicAlgCl l) W.carrier V'')
        (γ : ℝ), τ.IsConstituent ρ → W.HasDetWeight l τ ι γ → γ ≤ d) →
      ∀ (x : C.finitePoints), ∀ α ∈ W.localEigenvalues l ρ x,
        frobeniusWeight ι (C.pointNorm x.1) α ≤ d + 1 / 2 ^ j := by
  induction j with
  | zero =>
    intro V _ _ _ ρ hρ hreal d hd x α hα
    have h := frobeniusWeight_le_add_two_of_hasNonnegCoeffs ι (hρ.tprod hρ)
      (hreal.hasNonnegCoeffs_eulerFactor_tprod_self ι)
      (le_add_of_isConstituent_tprod_of_hasDetWeight ι x hρ hρ hd hd) x
      (sq_mem_localEigenvalues_tprod_self hα)
    rw [frobeniusWeight_sq] at h
    norm_num
    linarith
  | succ j ih =>
    intro V _ _ _ ρ hρ hreal d hd x α hα
    have h := ih (ρ.tprod ρ) (hρ.tprod hρ) (hreal.tprod ι hreal)
      (le_add_of_isConstituent_tprod_of_hasDetWeight ι x hρ hρ hd hd) x _
      (sq_mem_localEigenvalues_tprod_self hα)
    rw [frobeniusWeight_sq] at h
    have h2 : (1 : ℝ) / 2 ^ (j + 1) = 1 / 2 ^ j / 2 := by rw [pow_succ]; ring
    rw [h2]
    linarith

end RankinSelberg

end WeilGroup

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `sk-p-real-rankin`: Rankin–Selberg upper bound.

Let `U₀` be an affine smooth geometrically connected curve over `𝔽_q` and let `ℱ ≠ 0` be an
`ι`-real lisse Weil sheaf on it all of whose irreducible constituents have determinant weight
at most `d`. Then every local Frobenius eigenvalue of `ℱ` has `ι`-weight at most `d`.

The proof runs the Rankin–Selberg trick on the even tensor powers `ℋ_m = ℱ ^ ⊗ (2 m)`. Their
constituents have determinant weight at most `2 m d`, so the top compactly supported
cohomology `H_c² (U, ℋ_m)`, a coinvariant Tate twist, has eigenvalues of modulus at most
`q ^ (m d + 1)`; the Grothendieck trace formula therefore bounds the radius of convergence of
`L_ι (U₀, ℋ_m, T)` below by `q ^ (-(m d + 1))`. Reality of `ℱ` makes every coefficient of
every inverse local factor nonnegative, so each individual factor inherits that radius bound
from the product, and a zero of the local denominator at `|ι α| ^ (-2 m / e)` gives
`wt (α) ≤ d + 1 / m` for every `m`. -/
theorem hasWeightsAtMost_of_isReal [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Nontrivial V] (hρ : W.IsLisse l ρ)
    (hreal : W.IsReal l ρ ι) {d : ℝ}
    (hd : ∀ {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
      [FiniteDimensional (PadicAlgCl l) V'] (σ : Representation (PadicAlgCl l) W.carrier V')
      (γ : ℝ), σ.IsConstituent ρ → W.HasDetWeight l σ ι γ → γ ≤ d) :
    W.HasWeightsAtMost l ρ ι d := by
  intro x α hα
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε one_half_lt_one
  have h := frobeniusWeight_le_add_inv_two_pow_of_isReal ι j ρ hρ hreal hd x α hα
  rw [one_div_pow] at hj
  linarith

/-- Blueprint `lem-rp-upper-bound`: Upper bound via the largest determinant weight.

Let `U₀` be a smooth geometrically connected affine curve, `ℱ` an `ι`-real lisse Weil sheaf on
it and `d` an upper bound for the determinant weights of its constituents. Then every local
eigenvalue `α` of `ℱ` at a closed point `x` satisfies `|ι α| ^ 2 ≤ q_x ^ d`.

This is `AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_isReal` with the weight unfolded: the
Rankin–Selberg bound for the iterated tensor squares
(`AlgebraicGeometry.WeilGroup.frobeniusWeight_le_add_inv_two_pow_of_isReal`) gives
`|ι α| ^ 2 ≤ q_x ^ (d + 2 ^ (-j))` for every `j`. -/
theorem sq_norm_le_rpow_of_isReal [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Nontrivial V] (hρ : W.IsLisse l ρ)
    (hreal : W.IsReal l ρ ι) {d : ℝ}
    (hd : ∀ {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
      [FiniteDimensional (PadicAlgCl l) V'] (σ : Representation (PadicAlgCl l) W.carrier V')
      (γ : ℝ), σ.IsConstituent ρ → W.HasDetWeight l σ ι γ → γ ≤ d)
    (x : C.finitePoints) {α : PadicAlgCl l} (hα : α ∈ W.localEigenvalues l ρ x) :
    ‖ι α‖ ^ 2 ≤ (C.pointNorm x.1 : ℝ) ^ d := by
  have h := hasWeightsAtMost_of_isReal W l ρ ι hρ hreal hd x α hα
  have hα0 : 0 < ‖ι α‖ := norm_pos_iff.2 <|
    (map_ne_zero ι).2 fun h ↦ zero_notMem_localEigenvalues (ρ := ρ) x (h ▸ hα)
  have hq : (1 : ℝ) < C.pointNorm x.1 := by exact_mod_cast C.one_lt_pointNorm x.2
  rw [frobeniusWeight, div_le_iff₀ (Real.log_pos hq)] at h
  rw [← Real.exp_log (pow_pos hα0 2), Real.rpow_def_of_pos (zero_lt_one.trans hq),
    Real.log_pow]
  exact Real.exp_le_exp.2 (by push_cast; linarith)

end WeilGroup

namespace BoundaryDatum

variable {U : Scheme.{u}} {pU : U ⟶ Spec (.of K)} [IsCurve pU] {j : U ⟶ C}
  [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} {WC : WeilGroup p}
  (D : BoundaryDatum j WU WC) (l : ℕ) [Fact l.Prime] {V : Type u}
  [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `sk-p-real-semi`: Semi-continuity of weights.

For a boundary datum `D`, if the lisse Weil sheaf `ℱ` on `U₀` has weights at most `w`, then
`j_* ℱ` has weights at most `w` on `C₀`. Concretely: at a boundary point `s`, the residue
Frobenius acts on the boundary stalk `V ^ (I_s)`, and every one of its eigenvalues `α`,
witnessed by a nonzero invariant eigenvector `v`, has `ι`-weight at most `w` relative to the
residue cardinality `q_s`.

Shrinking to an affine neighbourhood, the counting bound `N_e ≤ A q ^ e` for closed points of
degree `e` shows that `L_ι (U₀, ℱ, T)⁻¹` has radius at least `q ^ (-(w + 2) / 2)`, while the
open–closed sequence identifies `H_c² (C, j_* ℱ)` with a coinvariant Tate twist whose
eigenvalues are bounded by `q ^ ((w + 2) / 2)`. The trace formula then confines the zeros of
the boundary factor, giving the preliminary bound `|ι α| ≤ q_s ^ ((w + 2) / 2)`; applying it
to the tensor powers `ℱ ^ ⊗ n`, whose boundary stalks receive `(V ^ (I_s)) ^ ⊗ n`, improves it
to `|ι α| ≤ q_s ^ (w / 2 + 1 / n)` for every `n`, and `n → ∞` finishes. -/
theorem frobeniusWeight_le_of_hasWeightsAtMost
    (ρ : Representation (PadicAlgCl l) WU.carrier V) {w : ℝ}
    (hw : WU.HasWeightsAtMost l ρ ι w) (s : ↥((Set.range j.base)ᶜ)) {α : PadicAlgCl l} {v : V}
    (hv : v ∈ D.boundaryStalk l ρ s) (hv0 : v ≠ 0) (hα : ρ (D.residueFrobenius s) v = α • v) :
    WeilGroup.frobeniusWeight ι (C.pointNorm s.1) α ≤ w := by
  sorry

/-- Blueprint `sk-p-real-semi`: Semi-continuity of weights.

The consequence of the weight bound for `j_* ℱ`: a lisse Weil sheaf `𝒢` on `C₀` whose
restriction to the open `U₀` is punctually `ι`-pure of weight `w` is punctually `ι`-pure of
weight `w` on all of `C₀`.

Indeed `𝒢` is the direct image of its restriction, so the previous bound applies to `𝒢` and
to its dual `𝒢 ᵛ`; the eigenvalues of the dual are the inverses of the eigenvalues of `𝒢`, so
the upper bound `w` for `𝒢` and the upper bound `-w` for `𝒢 ᵛ` combine into an equality at
every closed point of the boundary. The dual `𝒢 ᵛ` is not defined in this block; the proof
will need `Representation.dual` on top of the statements recorded here. -/
theorem isPunctuallyPure_of_isPunctuallyPure_restrict
    (ρ : Representation (PadicAlgCl l) WC.carrier V) {w : ℝ} (hρ : WC.IsLisse l ρ)
    (hpure : WU.IsPunctuallyPure l (ρ.comp D.restrict) ι w) :
    WC.IsPunctuallyPure l ρ ι w := by
  sorry

end BoundaryDatum

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `sk-p-real-purity`: Purity of real lisse sheaves on curves.

The main theorem of the block. Let `C₀ / 𝔽_q` be a smooth geometrically connected curve and
`ℱ` an `ι`-real lisse Weil sheaf on it. Then every irreducible constituent `V` of `ℱ` is
punctually `ι`-pure of weight `dw_ι (V)`, its own determinant weight.

Replacing `ℱ` by its semisimplification, which has the same local polynomials and is again
real, and restricting to a nonempty affine open `U₀`, fix a nonzero weight block `𝒮 (γ)` and
let `N = N_γ` and `B = B_γ` be the rank and the weight sum of the blocks strictly above `γ`.
The exterior power `⋀ ^ (N + 1) 𝒮` is nonzero, real, and its constituents have determinant
weight at most `B + γ`. At a point of degree `e`, multiplying one eigenvalue `α` of the
`γ`-block by all eigenvalues of all higher blocks produces an eigenvalue of that exterior
power, so the Rankin–Selberg bound gives `|ι α| q ^ (e B / 2) ≤ q ^ (e (B + γ) / 2)`, that is
`|ι α| ≤ q ^ (e γ / 2)`. Since the determinant of the block is pure of weight `r γ`, the
product of the `r` ratios `|ι α_i| / q ^ (e γ / 2)` is `1` while each is at most `1`, so each
is `1`. That is purity on `U₀`, and semi-continuity of weights extends it over the finitely
many missing points of `C₀`. -/
theorem isPunctuallyPure_of_isConstituent_of_isReal [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] (hρ : W.IsLisse l ρ) (hreal : W.IsReal l ρ ι)
    {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
    [FiniteDimensional (PadicAlgCl l) V']
    (σ : Representation (PadicAlgCl l) W.carrier V') (hσ : σ.IsConstituent ρ)
    {γ : ℝ} (hγ : W.HasDetWeight l σ ι γ) :
    W.IsPunctuallyPure l σ ι γ := by
  sorry

end WeilGroup

end AlgebraicGeometry
