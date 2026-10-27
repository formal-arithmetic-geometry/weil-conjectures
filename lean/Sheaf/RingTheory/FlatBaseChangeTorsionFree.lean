module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flat extension of domains preserves torsion-free modules

Source: Stacks Project, More on Algebra, Tag 0AXM, lemma-flat-pullback-torsion
(blueprint: lem-per-flat-base-change-torsion-free).

Multiplication by `b : S` on `N ⊗[R] S` is written as
`(LinearMap.mul R S b).lTensor N`, which sends `n ⊗ s` to `n ⊗ (b * s)`.
This expresses the second-factor action without requiring an `S`-action on `N`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Module

/-- Flat base change between domains preserves torsion freeness for arbitrary modules.
The conclusion uses the second-factor action, explicitly as `id_N ⊗ (s ↦ b * s)`.

Source: Stacks Project, Tag 0AXM, lemma-flat-pullback-torsion
(blueprint: lem-per-flat-base-change-torsion-free).

Proof plan:
1. Put `K = Frac(R)` and `V = (R ∖ {0})⁻¹N`. The kernel criterion in
   `def-weil-pbc-module-localization` and torsion freeness give an injection `i : N → V`.
   Since `R` is a domain, `K` is a field and `V` is a `K`-vector space.
2. By `lem-weil-pbc-localization-flat`, `K` is flat over `R`. By
   `lem-weil-pbc-module-over-field-flat`, `V` is flat over `K`. Then
   `lem-pc-module-flat-transitive` makes `V` flat over `R`.
3. Flatness of `R → S` (`def-weil-pbc-flat-ring-map`) and
   `lem-trf-flat-tensor-preserves-injection` give an injection
   `J : S ⊗[R] N → S ⊗[R] V`. It is `S`-linear, as checked on pure tensors
   using `def-weil-pbc-module-tensor-product`.
4. By `lem-weil-pbc-flat-module-base-change`, `S ⊗[R] V` is flat over `S`.
   By `lem-trf-flat-module-torsionfree-domain`, every nonzero scalar of `S`
   acts injectively on this target, including scalars outside the image of `R`.
5. Tensor symmetry gives `τ : N ⊗[R] S → S ⊗[R] N`, intertwining the
   second-factor action with the first-factor action. If `b * z = 0` in the
   second-factor sense, then `b • J(τ(z)) = 0`. Step 4 and injectivity of
   `J` and `τ` imply `z = 0`. No finiteness or Noetherian condition is used. -/
theorem torsionFree_baseChange_right
    (R : Type u) (S : Type v) (N : Type w)
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
    [AddCommGroup N] [Module R N]
    (hflat : (algebraMap R S).Flat)
    (hN : ∀ (a : R), a ≠ 0 → ∀ (n : N), a • n = 0 → n = 0) :
    ∀ (b : S), b ≠ 0 → ∀ (z : N ⊗[R] S),
      (LinearMap.mul R S b).lTensor N z = 0 → z = 0 := by
  sorry

end Module
