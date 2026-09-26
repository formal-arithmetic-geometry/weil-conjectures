/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Analysis.Complex.Basic
public import WeilConjectures.FourierTransform.AffineSpace

/-!

# The trace function and the Fourier trace formula

A complex `K` on a scheme `X₀` separated of finite type over a finite field `k₀` has a
*trace function*: at a `k₁`-point `x` of `X₀`, for `k₁/k₀` finite, the alternating sum

`t_K(x) = Tr(F_x | K_x̄) = ∑ⱼ (-1)ʲ Tr(F_x | Hʲ(K)_x̄)`

of the traces of the local Frobenius on the stalks of the cohomology sheaves. It is a
numerical invariant of `K`, and the Fourier–Deligne transform acts on it by the classical
finite Fourier transform of the additive group of `k₁`, up to the sign coming from the
shift `[1]`. Two numerical identities follow: the Plancherel formula and the trace-level
form of Fourier inversion.

## Main definitions

- `AlgebraicGeometry.Etale.traceFunction`: the trace function `t_K`.
- `AlgebraicGeometry.AffineSpace.linePoint`: the `k₁`-point of the affine line over `k₀`
  with a given coordinate.

## Main statements

- `AlgebraicGeometry.Etale.traceFunction_affineFourierTransform`: the Fourier trace
  formula.
- `AlgebraicGeometry.Etale.sum_normSq_traceFunction_affineFourierTransform`: Plancherel.
- `AlgebraicGeometry.Etale.traceFunction_affineFourierTransform_comp`: trace-level Fourier
  inversion.

## Implementation notes

The local Frobenius and the notion of a Weil complex belong to another block of the
blueprint; `traceFunction` is therefore stated with a `sorry` body, its `k₀`-structure
recorded by the structure morphism `a : X ⟶ Spec k₀` and the compatibility of the point
with it.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace AffineSpace

variable (k₀ : Type u) [Field k₀] (k₁ : Type u) [Field k₁] [Algebra k₀ k₁]

/-- The `k₁`-point of the affine line over `k₀` with coordinate `x ∈ k₁`. -/
noncomputable def linePoint (x : k₁) :
    Spec (CommRingCat.of k₁) ⟶ line (Spec (CommRingCat.of k₀)) :=
  homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)))
    fun _ ↦ (Scheme.ΓSpecIso (CommRingCat.of k₁)).inv x

@[simp]
lemma linePoint_over (x : k₁) :
    linePoint k₀ k₁ x ≫ line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) :=
  homOfVector_over _ _

end AffineSpace

namespace Etale

open AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime]

/-- Blueprint `sk-def-trace`: The trace function, and the classical Fourier transform.

For a Weil complex `K` on a scheme `X` separated of finite type over a finite field `k₀`
and a `k₁`-point `x` of `X` over `k₀`, with `k₁/k₀` finite, the *trace function* of `K` at
`x` is

`t_K(x) = Tr(F_x | K_x̄) = ∑ⱼ (-1)ʲ Tr(F_x | Hʲ(K)_x̄)`,

the alternating sum of the traces of the local Frobenius at `x` on the stalks of the
cohomology sheaves of `K`. The classical Fourier transform of a function `f` on `k₁`,
`f̂(y) = ∑ₓ f(x) ψ(xy)`, is the model for the Fourier trace formula below. -/
noncomputable def traceFunction {k₀ : Type u} [Field k₀] [Finite k₀] {X : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of k₀))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {k₁ : Type u} [Field k₁] [Finite k₁] [Algebra k₀ k₁] (x : Spec (CommRingCat.of k₁) ⟶ X)
    (hx : x ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) : Λ :=
  sorry

section AffineLine

variable {k₀ : Type u} [Field k₀] [Finite k₀] {k₁ : Type u} [Field k₁] [Fintype k₁]
  [Algebra k₀ k₁] [Algebra (ZMod p) k₁]
variable [CharP Γ(pullback (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
    (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)), ⊤) p]
  [HasCompactification (pullback.snd
    (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
    (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)))]

/-- Blueprint `sk-thm-fourier-trace-formula`: P8: the Fourier trace formula.

The trace function of the Fourier–Deligne transform of `K` is, up to the sign coming from
the shift `[1]`, the classical Fourier transform of the trace function of `K`:

`t_{FT_ψ(K)}(y) = -∑_{x ∈ k₁} t_K(x) ψ(Tr_{k₁/k₀}(xy))`,

the character of `k₁` being `Ψ ∘ Tr_{k₁/𝔽_p}`. -/
theorem traceFunction_affineFourierTransform (Ψ : AddChar (ZMod p) Λ)
    (K : DerivedCategory
      (Sheaf (line (Spec (CommRingCat.of k₀))).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (y : k₁) :
    traceFunction Λ (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
        ((affineFourierTransform Λ PUnit.{u + 1} (Spec (CommRingCat.of k₀)) Ψ).obj K)
        (linePoint k₀ k₁ y) (by simp) =
      -∑ x : k₁, traceFunction Λ
          (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)) K
          (linePoint k₀ k₁ x) (by simp) *
        (Ψ.compAddMonoidHom (Algebra.trace (ZMod p) k₁).toAddMonoidHom) (x * y) :=
  sorry

/-- Blueprint `sk-cor-plancherel`: P9: Plancherel.

Under a ring homomorphism `ι` of the coefficients into `ℂ`, the Fourier–Deligne transform
multiplies the squared `L²`-norm of the trace function by `#k₁`:

`∑_{y ∈ k₁} |t_{FT_ψ(K)}(y)|² = #k₁ ∑_{x ∈ k₁} |t_K(x)|²`.

This is the classical Plancherel theorem for the finite group `(k₁, +)`, transported to
trace functions; no weight enters. -/
theorem sum_normSq_traceFunction_affineFourierTransform (Ψ : AddChar (ZMod p) Λ)
    (ι : Λ →+* ℂ)
    (K : DerivedCategory
      (Sheaf (line (Spec (CommRingCat.of k₀))).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∑ y : k₁, ‖ι (traceFunction Λ
        (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
        ((affineFourierTransform Λ PUnit.{u + 1} (Spec (CommRingCat.of k₀)) Ψ).obj K)
        (linePoint k₀ k₁ y) (by simp))‖ ^ 2 =
      Fintype.card k₁ * ∑ x : k₁, ‖ι (traceFunction Λ
        (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)) K
        (linePoint k₀ k₁ x) (by simp))‖ ^ 2 :=
  sorry

/-- Blueprint `sk-prop-double-trace`: P10: trace-level Fourier inversion.

Applying the Fourier–Deligne transform for `ψ` and then for `ψ⁻¹` multiplies the trace
function by `#k₁`, which is the trace function of the Tate twist `K(-1)` at points of
degree `n`:

`t_{FT_{ψ⁻¹} FT_ψ(K)}(y) = #k₁ · t_K(y)`.

This is the rank-one trace-level consequence of the functorial inversion isomorphism
`AlgebraicGeometry.Etale.fourierTransformInversionIso`. -/
theorem traceFunction_affineFourierTransform_comp (Ψ Ψ' : AddChar (ZMod p) Λ)
    (hΨ : Ψ * Ψ' = 1)
    (K : DerivedCategory
      (Sheaf (line (Spec (CommRingCat.of k₀))).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (y : k₁) :
    traceFunction Λ (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
        ((affineFourierTransform Λ PUnit.{u + 1} (Spec (CommRingCat.of k₀)) Ψ').obj
          ((affineFourierTransform Λ PUnit.{u + 1} (Spec (CommRingCat.of k₀)) Ψ).obj K))
        (linePoint k₀ k₁ y) (by simp) =
      Fintype.card k₁ * traceFunction Λ
        (line (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)) K
        (linePoint k₀ k₁ y) (by simp) :=
  sorry

end AffineLine

end Etale

end AlgebraicGeometry
