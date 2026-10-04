/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.OpenSubcurve
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations
public import WeilConjectures.Mathlib.Algebra.Order.BigOperators.Group.Multiset
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
- `AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_isReal`
- `AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_of_hasWeightsAtMost`
- `AlgebraicGeometry.BoundaryDatum.isPunctuallyPure_of_isPunctuallyPure_restrict`
- `AlgebraicGeometry.WeilGroup.IsLisse.hasDetWeight`: every lisse Weil sheaf has a determinant
  weight, read off from the rank-one determinant line.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_subquotient_of_isReal`: the composition factors
  of a real lisse Weil sheaf on an affine curve are pure of their determinant weights.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine`
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
  sorry

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

section DetWeight

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V V' : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V] [AddCommGroup V']
  [Module (PadicAlgCl l) V'] [FiniteDimensional (PadicAlgCl l) V']
  {ρ : Representation (PadicAlgCl l) W.carrier V} (ι : PadicAlgCl l →+* ℂ)

omit [Finite K] [IsCurve p] in
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

omit [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] in
/-- Local eigenvalues are invariant under equivalence of representations. -/
theorem localEigenvalues_of_equiv {σ : Representation (PadicAlgCl l) W.carrier V'}
    (e : ρ.Equiv σ) (x : C.finitePoints) :
    W.localEigenvalues l σ x = W.localEigenvalues l ρ x := by
  rw [localEigenvalues, localEigenvalues, e.charpoly_apply]

end DetWeight

end WeilGroup

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

-- The constituent bound elaborates exterior powers of direct sums of subquotients.
set_option maxHeartbeats 1000000 in
/-- Blueprint `thm-rp-real-lisse-purity-affine`, Steps 1–3, for the composition factors.

Let `ρ` be an `ι`-real lisse Weil representation on a smooth geometrically connected affine
curve, and `0 = F 0 ⋖ F 1 ⋖ ⋯ ⋖ F n = ρ` a composition series. Then every composition factor
`Q j = F (j + 1) ⧸ F j` is punctually `ι`-pure of its determinant weight
`γ = wt_{ι, q}(det Q j (γ)) / rank Q j`.

The semisimplification `S = ⨁ i, Q i` has the local polynomials of `ρ`, so its exterior power
`E = ⋀^(N + 1) S`, where `N` is the total rank of the factors of determinant weight `> γ`, is
real (`sk-r-real-linear`); by the exterior-power rule (`sk-p-exterior`) its constituents have
determinant weight at most `B + γ`, where `B` is the sum of the determinant weights of those
factors counted with rank. The Rankin–Selberg bound (`sk-p-real-rankin`) then bounds every
local eigenvalue of `E` by `B + γ`. At a closed point `x`, the product of an eigenvalue `β` of
`Q j` with all eigenvalues of the factors of weight `> γ` is such an eigenvalue
(`sk-p-linear-spectra`), of weight `wt β + B`; so `wt β ≤ γ`. The weights of the eigenvalues
of `Q j` sum to the weight `rank (Q j) * γ` of its determinant, so all of them equal `γ`. -/
theorem isPunctuallyPure_subquotient_of_isReal [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] (hρ : W.IsLisse l ρ) (hreal : W.IsReal l ρ ι) {n : ℕ}
    {F : ℕ → Subrepresentation ρ} (h0 : F 0 = ⊥) (hn : F n = ⊤)
    (hF : ∀ i < n, F i ⋖ F (i + 1)) {j : ℕ} (hj : j < n) :
    W.IsPunctuallyPure l ((F (j + 1)).subquotient (F j)) ι
      (frobeniusWeight ι (Nat.card K)
          (LinearMap.det ((F (j + 1)).subquotient (F j) W.frobeniusLift)) /
        Module.finrank (PadicAlgCl l)
          ((F (j + 1)).toSubmodule ⧸ (F j).toSubmodule.comap (F (j + 1)).toSubmodule.subtype)) := by
  classical
  intro x α hα
  let Qt : Fin n → Type u := fun i ↦
    (F (i + 1)).toSubmodule ⧸ (F i).toSubmodule.comap (F (i + 1)).toSubmodule.subtype
  let Q : ∀ i, Representation (PadicAlgCl l) W.carrier (Qt i) := fun i ↦
    (F (i + 1)).subquotient (F i)
  let d : Fin n → ℕ := fun i ↦ Module.finrank (PadicAlgCl l) (Qt i)
  let w : Fin n → ℝ := fun i ↦
    frobeniusWeight ι (Nat.card K) (LinearMap.det (Q i W.frobeniusLift)) / d i
  let j' : Fin n := ⟨j, hj⟩
  change α ∈ W.localEigenvalues l (Q j') x at hα
  change frobeniusWeight ι (C.pointNorm x.1) α = w j'
  set γ := w j' with hγ
  set qx := C.pointNorm x.1
  let eig : Fin n → Multiset (PadicAlgCl l) := fun i ↦ W.localEigenvalues l (Q i) x
  -- the composition factors
  have hQlisse (i : Fin n) : W.IsLisse l (Q i) := hρ.subquotient _ _
  have hQirr (i : Fin n) : (Q i).IsIrreducible :=
    (Subrepresentation.isIrreducible_subquotient_iff (hF i i.2).le).2 (hF i i.2)
  have hQnontriv (i : Fin n) : Nontrivial (Qt i) := by
    have := hQirr i
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (bot_ne_top : (⊥ : Subrepresentation (Q i)) ≠ ⊤)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hQdet (i : Fin n) : W.HasDetWeight l (Q i) ι (w i) := (hQlisse i).hasDetWeight ι
  have hcardeig (i : Fin n) : Multiset.card (eig i) = d i := by
    rw [show d i = (Q i (W.frobenius x)).charpoly.natDegree from
      (LinearMap.charpoly_natDegree _).symm]
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hweig (i : Fin n) : frobeniusWeight ι qx (eig i).prod = d i * w i := by
    change frobeniusWeight ι qx (Q i (W.frobenius x)).charpoly.roots.prod = _
    rw [← Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    exact hQdet i x
  have h0eig (i : Fin n) : (0 : PadicAlgCl l) ∉ eig i := zero_notMem_localEigenvalues x
  -- the semisimplification
  let S := Representation.directSum Q
  have hcharpoly (g : W.carrier) : (S g).charpoly = (ρ g).charpoly := by
    rw [Representation.charpoly_directSum, LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le (ρ g)
      (fun i ↦ (F i).toSubmodule) n (by rw [h0]; rfl) (by rw [hn]; rfl) (fun i hi ↦ (hF i hi).le)
      (fun i ↦ (F i).apply_mem_toSubmodule g)]
    exact Fin.prod_univ_eq_prod_range (fun i ↦ ((F (i + 1)).subquotient (F i) g).charpoly) n
  have heigS : W.localEigenvalues l S x = ∑ i, eig i := by
    change (S (W.frobenius x)).charpoly.roots = _
    rw [Representation.charpoly_directSum, Polynomial.roots_prod _ _
      (Finset.prod_ne_zero_iff.2 fun i _ ↦ (LinearMap.charpoly_monic _).ne_zero)]
    rfl
  -- the factors of determinant weight above `γ`
  let A : Finset (Fin n) := Finset.univ.filter fun i ↦ γ < w i
  let N := ∑ i ∈ A, d i
  let B := ∑ i ∈ A, (d i : ℝ) * w i
  have hj'A : j' ∉ A := by simp [A, γ]
  have hSlisse : W.IsLisse l S := IsLisse.directSum hQlisse
  have hSnontriv : Nontrivial (DirectSum (Fin n) Qt) :=
    (DirectSum.of_injective (β := Qt) j').nontrivial
  -- the bound on the determinant weights of the constituents of `⋀^(N + 1) S`
  have hbound : ∀ {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
      [FiniteDimensional (PadicAlgCl l) V'] (τ : Representation (PadicAlgCl l) W.carrier V')
      (γ' : ℝ), τ.IsConstituent (S.exteriorPower (N + 1)) → W.HasDetWeight l τ ι γ' →
      γ' ≤ B + γ := by
    intro V' _ _ _ τ γ' hτ hγ'
    obtain ⟨N₁, M₁, hcov, ⟨eτ⟩⟩ := hτ.exists_covBy
    have hRirr : (M₁.subquotient N₁).IsIrreducible :=
      (Representation.isIrreducible_iff_of_equiv eτ).1 hτ.1
    have hRlisse : W.IsLisse l (M₁.subquotient N₁) := (hSlisse.exteriorPower _).subquotient _ _
    obtain ⟨T, hT, hTc, hTs⟩ :=
      Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower
      (weightCharacter ι (Nat.card K)) W.deg W.frobeniusLift S (N + 1)
      (Representation.directSumSummand Q)
      (fun i ↦ (Representation.isIrreducible_iff_of_equiv
        (Representation.directSumSummandEquiv Q i)).1 (hQirr i))
      (fun i ↦ ((hQlisse i).of_equiv
        (Representation.directSumSummandEquiv Q i)).hasFiniteGeometricDet)
      (Representation.isInternal_directSumSummand Q) hcov.lt hRirr hRlisse.hasFiniteGeometricDet
    have hτnontriv : Nontrivial V' := by
      have := hτ.1
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    have hγ'eq : γ' = (M₁.subquotient N₁).detWeight (weightCharacter ι (Nat.card K))
        W.frobeniusLift := by
      rw [detWeight_weightCharacter, eτ.det_apply, eτ.finrank_eq]
      have hτlisse : W.IsLisse l τ := hRlisse.of_equiv eτ.symm
      exact HasDetWeight.eq (ρ := τ) ι hγ' (hτlisse.hasDetWeight ι) x
    have hWM : Representation.weightMultiset (weightCharacter ι (Nat.card K)) W.frobeniusLift
        (Representation.directSumSummand Q) = ∑ i, Multiset.replicate (d i) (w i) := by
      simp only [Representation.weightMultiset]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have e := Representation.directSumSummandEquiv Q i
      rw [detWeight_weightCharacter, e.det_apply, e.finrank_eq]
    have hfilter : (∑ i, Multiset.replicate (d i) (w i)).filter (γ < ·) =
        ∑ i ∈ A, Multiset.replicate (d i) (w i) := by
      have key (s : Finset (Fin n)) : (∑ i ∈ s, Multiset.replicate (d i) (w i)).filter (γ < ·) =
          ∑ i ∈ s.filter (fun i ↦ γ < w i), Multiset.replicate (d i) (w i) := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Multiset.filter_add, ih, Finset.filter_insert]
          split_ifs with h
          · rw [Finset.sum_insert (by simp [ha]),
              Multiset.filter_eq_self.2 fun b hb ↦ (Multiset.eq_of_mem_replicate hb) ▸ h]
          · rw [Multiset.filter_eq_nil.2 fun b hb ↦ (Multiset.eq_of_mem_replicate hb) ▸ h,
              zero_add]
      exact key Finset.univ
    rw [hWM] at hT
    have hle := Multiset.sum_le_sum_filter_add_of_le γ hT (by
      rw [hTc, hfilter, Multiset.card_sum]
      simp [N])
    rw [hfilter, Multiset.sum_sum] at hle
    simp only [Multiset.sum_replicate, nsmul_eq_mul] at hle
    rw [hγ'eq, hTs]
    exact hle
  -- the upper bound for the eigenvalues of the block `Q j`
  have key (β : PadicAlgCl l) (hβ : β ∈ eig j') : frobeniusWeight ι qx β ≤ γ := by
    let t := β ::ₘ ∑ i ∈ A, eig i
    have ht : t.prod ∈ W.localEigenvalues l (S.exteriorPower (N + 1)) x := by
      change t.prod ∈ (_root_.exteriorPower.map (N + 1) (S (W.frobenius x))).charpoly.roots
      rw [LinearMap.charpoly_roots_exteriorPower]
      change t.prod ∈ ((W.localEigenvalues l S x).powersetCard (N + 1)).map Multiset.prod
      rw [heigS]
      refine Multiset.mem_map_of_mem _ (Multiset.mem_powersetCard.2 ⟨?_, ?_⟩)
      · change β ::ₘ (∑ i ∈ A, eig i) ≤ _
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j'), ← Multiset.singleton_add]
        exact add_le_add (Multiset.singleton_le.2 hβ) (Finset.sum_le_sum_of_subset fun i hi ↦
          Finset.mem_erase.2 ⟨fun h ↦ hj'A (h ▸ hi), Finset.mem_univ _⟩)
      · simp [t, Multiset.card_sum, hcardeig, N, add_comm]
    have hEnontriv : Nontrivial (⋀[PadicAlgCl l]^(N + 1) (DirectSum (Fin n) Qt)) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have h' : W.localEigenvalues l (S.exteriorPower (N + 1)) x = 0 := by
        rw [localEigenvalues, LinearMap.charpoly_eq_one_of_subsingleton, Polynomial.roots_one,
          Multiset.empty_eq_zero]
      rw [h'] at ht
      exact Multiset.notMem_zero _ ht
    have hE := hasWeightsAtMost_of_isReal W l (S.exteriorPower (N + 1)) ι
      (hSlisse.exteriorPower _) (hreal.exteriorPower_of_charpoly_eq ι (fun _ ↦ hcharpoly _) _)
      hbound x _ ht
    have hne : ∀ i ∈ A, (eig i).prod ≠ 0 := fun i _ ↦ Multiset.prod_ne_zero (h0eig i)
    have hw : frobeniusWeight ι qx t.prod = frobeniusWeight ι qx β + B := by
      rw [Multiset.prod_cons, Multiset.prod_sum,
        frobeniusWeight_mul ι qx (fun h ↦ h0eig j' (h ▸ hβ)) (Finset.prod_ne_zero_iff.2 hne),
        frobeniusWeight_prod ι qx A hne]
      simp only [hweig, B]
    linarith
  -- the product of the eigenvalues of `Q j` has weight `rank (Q j) * γ`
  have hsum : ((eig j').map (frobeniusWeight ι qx)).sum =
      Multiset.card ((eig j').map (frobeniusWeight ι qx)) • γ := by
    rw [← frobeniusWeight_multiset_prod ι qx (h0eig j'), hweig, Multiset.card_map, hcardeig,
      nsmul_eq_mul]
  exact Multiset.eq_of_le_of_sum_eq (fun a ha ↦ by
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
      exact key b hb) hsum _ (Multiset.mem_map_of_mem _ hα)

/-- Blueprint `thm-rp-real-lisse-purity-affine`: Purity of real lisse sheaves on curves, for an
affine curve.

Let `C₀ / 𝔽_q` be a smooth geometrically connected affine curve and `ρ` an `ι`-real lisse Weil
representation. Every irreducible constituent `σ` of `ρ` is punctually `ι`-pure of its
determinant weight `γ`. Indeed `σ` is a composition factor `F (i₀ + 1) ⧸ F i₀` of a
composition series of `ρ`, and the composition factors are pure of their determinant weights
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_subquotient_of_isReal`); the determinant weight
of a nonzero representation is unique. -/
theorem isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine [IsAffine C]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] (hρ : W.IsLisse l ρ)
    (hreal : W.IsReal l ρ ι) {V' : Type u} [AddCommGroup V'] [Module (PadicAlgCl l) V']
    [FiniteDimensional (PadicAlgCl l) V']
    (σ : Representation (PadicAlgCl l) W.carrier V') (hσ : σ.IsConstituent ρ)
    {γ : ℝ} (hγ : W.HasDetWeight l σ ι γ) :
    W.IsPunctuallyPure l σ ι γ := by
  obtain ⟨N, M, hNM, hE⟩ := hσ.exists_covBy
  obtain ⟨n, F, i₀, h0, hn, hF, hi₀, hFi₀, hFi₀'⟩ := Subrepresentation.exists_covBy_chain hNM
  rw [← hFi₀, ← hFi₀'] at hE
  obtain ⟨e⟩ := hE
  intro x α hα
  rw [← localEigenvalues_of_equiv e] at hα
  rw [isPunctuallyPure_subquotient_of_isReal W l ρ ι hρ hreal h0 hn hF hi₀ x α hα]
  have hirr := (Subrepresentation.isIrreducible_subquotient_iff (hF i₀ hi₀).le).2 (hF i₀ hi₀)
  have : Nontrivial ((F (i₀ + 1)).toSubmodule ⧸
      (F i₀).toSubmodule.comap (F (i₀ + 1)).toSubmodule.subtype) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (bot_ne_top : (⊥ : Subrepresentation ((F (i₀ + 1)).subquotient (F i₀))) ≠ ⊤)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  exact ((hρ.subquotient _ _).hasDetWeight ι).eq ι (hγ.of_equiv ι e) x

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
  intro x α hα
  obtain ⟨U, hU, hxU, -⟩ : ∃ U : C.Opens, IsAffineOpen U ∧ x.1 ∈ U ∧ U ≤ ⊤ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp C.isBasis_affineOpens
      (show x.1 ∈ (⊤ : C.Opens) from trivial)
  have : IsAffine U := hU
  have : Nonempty U := ⟨⟨x.1, hxU⟩⟩
  have : IsCurve (U.ι ≫ p) := IsCurve.comp_of_isOpenImmersion p U.ι
  have : SmoothOfRelativeDimension 1 (U.ι ≫ p) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ p))
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : GeometricallyConnected (U.ι ≫ p) := GeometricallyConnected.comp_of_isOpenImmersion p U.ι
  have hy : (⟨x.1, hxU⟩ : U) ∈ U.toScheme.finitePoints :=
    (Scheme.mem_finitePoints_iff_of_isOpenImmersion U.ι _).1 x.2
  have h := isPunctuallyPure_of_isConstituent_of_isReal_of_isAffine (W.ofIsOpenImmersion U.ι) l ρ
    ι (hρ.ofIsOpenImmersion U.ι) (hreal.ofIsOpenImmersion U.ι ι) σ hσ
    (hγ.ofIsOpenImmersion U.ι ι)
  exact h.of_ofIsOpenImmersion U.ι ι ⟨_, hy⟩ α hα

end WeilGroup

end AlgebraicGeometry
