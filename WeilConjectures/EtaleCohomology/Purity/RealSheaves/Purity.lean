/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
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
