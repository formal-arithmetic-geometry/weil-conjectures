/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.WeilFourierKernelData

/-!
# The unshifted, middle-factor Fourier convolution operator

Data for the convolution kernel of the Fourier transform on affine space: the phase on the
triple product and the complement of the diagonal.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

noncomputable section

/-- The phase `r₁₂* b - r₂₃* b` on the triple product, equivalently `⟨x-z,y⟩`. -/
abbrev affineFourierInversePhase (k₀ : Type u) [Field k₀] (n : Type u) [Fintype n] :
    Γ(affineFourierTriple k₀ n, ⊤) :=
  (affineFourierR₁₂ k₀ n).appTop (AffineSpace.stdPairing n (affineFourierBase k₀)) -
    (affineFourierR₂₃ k₀ n).appTop (AffineSpace.stdPairing n (affineFourierBase k₀))

/-- The open complement of the closed diagonal. In rank zero it is empty. -/
def affineFourierDiagonalComplement (k₀ : Type u) [Field k₀] (n : Type u) :
    (affineFourierPlane k₀ n).Opens :=
  ⟨(Set.range (affineFourierDiagonal k₀ n))ᶜ,
    (affineFourierDiagonal k₀ n).isClosedEmbedding.isClosed_range.isOpen_compl⟩

end

end AlgebraicGeometry.WeilComplex
