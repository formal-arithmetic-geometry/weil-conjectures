module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The matrix-unit corner embedding

Source: the coefficient auxiliary extracted from paragraph (3) of the direct-image proof
in blueprint unit `sk-thm-sf-ctf-stability`, reconstruction steps 2–4.
(blueprint: lem-sfb-matrix-unit-corner-embedding)

The corner subspace, tensor map and image are specified by their carriers and pure-tensor
formula; no extra choices of a basis, action or tensor map are hypotheses.
-/

@[expose] public section

universe u v w x

open scoped TensorProduct

namespace Module.Basis

/-- The corner tensor map for a subalgebra containing all coordinate matrix units is
injective, intertwines the first-factor action, and has quotient killed by every diagonal
matrix unit. Source: the coefficient auxiliary extracted from paragraph (3) of the
blueprint direct-image proof, unit `sk-thm-sf-ctf-stability`, reconstruction steps 2–4.
(blueprint: lem-sfb-matrix-unit-corner-embedding)

Proof plan:
1. Evaluating on a vector gives `Eᵢⱼ Eₖₗ = δⱼₖ Eᵢₗ`, hence `e² = e`. Scalar operators
commute with all endomorphisms, so the restricted scalar action makes the D-action K-linear.
2. The image `eH` is closed under sums and K-scalars, and e acts identically there.
Expand v in the algebraic basis; its finite expansion gives `θᵥ = ∑ aᵢ Eᵢⱼ₀ ∈ D`.
3. The formula `(v,h) ↦ θᵥ • h` is bilinear. The tensor universal property
(def-weil-pbc-module-tensor-product) extends it to the specified linear map Φ.
4. Evaluation gives `T θᵥ = θ_(Tv)`, so Φ intertwines the action on pure tensors.
Tensor-Hom uniqueness (lem-weil-pbc-module-tensor-hom-currying) gives this on all tensors.
5. Expand a tensor as a finite sum `∑ bⱼ ⊗ kⱼ`, with each kⱼ in eH, using finite basis
expansions and bilinearity (def-weil-pbc-module-tensor-product).
6. If its image is zero, apply Eⱼ₀ₖ to isolate the coefficient kₖ, since e kₖ = kₖ.
All coefficients vanish, proving injectivity.
7. Equivariance makes the image a D-submodule. For any h, the image of
`bⱼ₀ ⊗ eh` is eh, so e kills the quotient. The identity
`Eⱼⱼ = Eⱼⱼ₀ e Eⱼ₀ⱼ` shows that every diagonal matrix unit kills it too.
All expansions are finite, without a cardinality or topology assumption. -/
theorem matrixUnit_corner_embedding
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    {J : Type w} (b : Module.Basis J K V) (j₀ : J)
    (D : Subalgebra K (Module.End K V))
    (hE : ∀ i j : J, (b.coord j).smulRight (b i) ∈ D)
    (H : Type x) [AddCommGroup H] [Module D H] [Module K H]
    [IsScalarTower K D H] :
    ∃ C : Submodule K H,
      (C : Set H) = Set.range (fun h : H ↦
        (⟨(b.coord j₀).smulRight (b j₀), hE j₀ j₀⟩ : D) • h) ∧
      ∃ hθ : ∀ v : V, (b.coord j₀).smulRight v ∈ D,
      ∃ Φ : V ⊗[K] C →ₗ[K] H,
        (∀ (v : V) (h : C), Φ (v ⊗ₜ[K] h) =
          (⟨(b.coord j₀).smulRight v, hθ v⟩ : D) • (h : H)) ∧
        Function.Injective Φ ∧
        (∀ (T : D) (z : V ⊗[K] C),
          Φ (LinearMap.rTensor C (T : Module.End K V) z) = T • Φ z) ∧
        ∃ N : Submodule D H,
          (N : Set H) = Set.range Φ ∧
          (∀ q : H ⧸ N,
            (⟨(b.coord j₀).smulRight (b j₀), hE j₀ j₀⟩ : D) • q = 0) ∧
          (∀ (j : J) (q : H ⧸ N),
            (⟨(b.coord j).smulRight (b j), hE j j⟩ : D) • q = 0) := by
  sorry

end Module.Basis
