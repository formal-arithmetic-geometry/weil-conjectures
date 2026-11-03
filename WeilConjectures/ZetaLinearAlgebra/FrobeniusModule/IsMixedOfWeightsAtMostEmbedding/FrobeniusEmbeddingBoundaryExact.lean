/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Exact.Basic
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusEmbeddingSpectralBounds
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.IsMixedOfWeightsAtMostEmbedding.FrobeniusEmbeddingExtensionBounds
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-!
# The weight estimate from a boundary exact sequence

Source: latest blueprint, sk-thm-wft-affine-curve-upper.proof.md, final paragraph.
(blueprint: lem-a1-embedding-boundary-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v

namespace FrobeniusModule

/-- An exact boundary sequence with bounded outer terms bounds its middle term.
The first map need not be injective.

Source: latest blueprint, sk-thm-wft-affine-curve-upper.proof.md, final paragraph:
pass the bound to the boundary image and then apply the extension bound.
(blueprint: lem-a1-embedding-boundary-exact).

Proof: the image of the first map is stable under the middle Frobenius, in both
directions, by equivariance and invertibility on the source. Restrict the middle
Frobenius to this image. The first map surjects onto its image, so the spectral
bound, and hence mixedness, passes to the image. Its inclusion and the second map
form a short exact sequence. Splice the two bounded pure filtrations using the
extension theorem. This includes zero boundary and zero cohomology. -/
theorem IsMixedOfWeightsAtMostEmbedding.of_boundaryExact
    {K : Type v} [Field K] [IsAlgClosed K]
    (iota : K →+* ℂ) (q : ℕ) (hq : 1 < q)
    (B M N : FrobeniusModule.{u, v} K)
    (δ : B.carrier →ₗ[K] M.carrier) (b : M.carrier →ₗ[K] N.carrier)
    (hδ : ∀ x, δ (B.frobenius x) = M.frobenius (δ x))
    (hb : ∀ x, b (M.frobenius x) = N.frobenius (b x))
    (hex : Function.Exact δ b) (hsurj : Function.Surjective b)
    (w : ℝ) (hB : IsMixedOfWeightsAtMostEmbedding iota q B w)
    (hN : IsMixedOfWeightsAtMostEmbedding iota q N w) :
    IsMixedOfWeightsAtMostEmbedding iota q M w := by
  classical
  let R := LinearMap.range δ
  have hR : R.map M.frobenius.toLinearMap = R := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨B.frobenius x, hδ x⟩
    · rintro ⟨x, rfl⟩
      refine ⟨δ (B.frobenius.symm x), ⟨B.frobenius.symm x, rfl⟩, ?_⟩
      change M.frobenius (δ (B.frobenius.symm x)) = δ x
      rw [← hδ, B.frobenius.apply_symm_apply]
  let I : FrobeniusModule K :=
    { carrier := R
      frobenius := M.frobenius.ofSubmodules R R hR }
  have hδI : ∀ x, δ.rangeRestrict (B.frobenius x) =
      I.frobenius (δ.rangeRestrict x) := fun x ↦ Subtype.ext (hδ x)
  have hI : IsMixedOfWeightsAtMostEmbedding iota q I w := by
    apply (isMixedOfWeightsAtMostEmbedding_iff_hasWeightsAtMost iota q hq I w).mpr
    have hBb := (isMixedOfWeightsAtMostEmbedding_iff_hasWeightsAtMost
      iota q hq B w).mp hB
    exact HasWeightsAtMost.of_surjective δ.rangeRestrict hδI δ.surjective_rangeRestrict hBb
  have hex' : Function.Exact R.subtype b := by
    apply LinearMap.exact_iff.mpr
    rw [Submodule.range_subtype]
    exact (LinearMap.exact_iff.mp hex)
  exact IsMixedOfWeightsAtMostEmbedding.of_shortExact iota q I M N R.subtype b
    (fun _ ↦ rfl) hb Subtype.val_injective hex' hsurj w hI hN

end FrobeniusModule
