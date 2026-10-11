module

public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Ampleness lifts along a square-zero thickening

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, square-zero case
(blueprint: lem-sc-ample-square-zero-thickening).

The invertibility of the pullback `j^*L` is the first clause of the landed
`Scheme.Modules.invertible_pullback_tensor` (lem-weil-pbc-invertible-pullback-tensor);
it is not restated here.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Ampleness lifts along a square-zero closed immersion of Noetherian schemes.
Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, square-zero case
(blueprint: lem-sc-ample-square-zero-thickening).

Proof: the ideal sheaf `I` is quasi-coherent with `I^2 = 0`, so the sequence
`0 → I ⊗ L^n → L^n → j_*j^*L^n → 0` is exact. For a point `x`, choose
`s ∈ Γ(Z, j^*L^n)` with `x ∈ Z_s` affine. The boundary of `s` is a derivation-like
class `ξ` in `H^1(X, I ⊗ L^n)`, and `∂(s^{e+1}) = (e+1) s^e ξ`. Since `Z_s` is affine
and `I ⊗ L^n` is annihilated by `I`, the class `s^e ξ` vanishes for `e` large (Lemma 01XR),
so a power of `s` lifts to `s' ∈ Γ(X, L^{(e+1)n})`. Then `j⁻¹ X_{s'} = Z_s` and
`Z_s → X_{s'}` is a finite surjective morphism from an affine scheme to a Noetherian
scheme, so `X_{s'}` is affine (Lemma 01YQ); with `X` quasi-compact, `L` is ample.
-/
theorem isAmple_of_isAmple_tensorPullback_of_square_zero
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian Z] [CompactSpace Z]
    (L : X.Modules) [L.IsInvertible]
    (hI : j.ker ^ 2 = ⊥) :
    letI : ((Scheme.Modules.tensorPullback j).obj L).IsInvertible :=
      ((Scheme.Modules.invertible_pullback_tensor j).1 L).2
    AlgebraicGeometry.Scheme.Modules.IsAmple Z ((Scheme.Modules.tensorPullback j).obj L) →
      AlgebraicGeometry.Scheme.Modules.IsAmple X L := by
  sorry

end AlgebraicGeometry.Scheme.Modules
