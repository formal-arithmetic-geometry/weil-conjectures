import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Equivariant isomorphism from a perfect pairing against a line

Source: literature/blueprint/master/blueprint/sec-zeta-weil/sk-cor-hasse/prop-endpoints.md,
  proof sentence giving the top-degree line isomorphism (blueprint:
  lem-weil-perfect-pairing-line-equivariance)

## Main statements

* `LinearMap.perfectPairingLineEquivariance`: a perfect bilinear pairing against a
  one-dimensional factor identifies the other factor with that line, compatibly with
  scalar endomorphisms.
-/

universe uL uV uW uM

namespace LinearMap

/-- A perfect pairing against a one-dimensional factor identifies the other factor with that
line, compatibly with scalar endomorphisms.

Source: literature/blueprint/master/blueprint/sec-zeta-weil/sk-cor-hasse/prop-endpoints.md,
  proof sentence giving the top-degree line isomorphism
  (blueprint: lem-weil-perfect-pairing-line-equivariance).

The proof follows the node's six steps: choose a nonzero vector in the one-dimensional first
factor; use bijectivity of the flipped pairing for injectivity of evaluation and bijectivity of
the pairing for surjectivity; obtain the dimension of the second factor from a singleton basis;
then substitute the chosen vector in the compatibility equation and cancel the evaluation map.
-/
theorem perfectPairingLineEquivariance
    (L : Type uL) [Field L]
    (V : Type uV) [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (W : Type uW) [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    (M : Type uM) [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    (β : V →ₗ[L] W →ₗ[L] M)
    (hβ : Function.Bijective β)
    (hβ_flip : Function.Bijective β.flip)
    (F_V : V →ₗ[L] V) (F_W : W →ₗ[L] W) (F_M : M →ₗ[L] M)
    (c : L)
    (hcompat : ∀ (x : V) (y : W), β (F_V x) (F_W y) = F_M (β x y))
    (hV : F_V = LinearMap.id)
    (hM : F_M = c • LinearMap.id)
    (hVdim : Module.finrank L V = 1)
    (hMdim : Module.finrank L M = 1) :
    Module.finrank L W = 1 ∧
      (∀ (e : V), e ≠ 0 →
          Function.Bijective (β e) ∧
            (∀ y : W, β e (F_W y) = F_M (β e y))) ∧
      F_W = c • LinearMap.id := by
  sorry

end LinearMap
