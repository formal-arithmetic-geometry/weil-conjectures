module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.Mathlib.Algebra.Module.Torsion
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Finite-presentation approximation and exceptional torsion quotients

Source: Stacks Project, Tag 0810, `lemma-helper-blowup-affine-space`, first proof paragraph.
(blueprint: lem-trf-affine-fp-approximation-strict-transform)
-/

@[expose] public section

universe u v w

open TensorProduct

namespace Module

/-- A finite module whose localization at `h` is finitely presented has a finite-presentation
approximation with the same localization and the same exceptional torsion quotients.

Source: Stacks Project, Tag 0810, `lemma-helper-blowup-affine-space`, first proof paragraph.
(blueprint: lem-trf-affine-fp-approximation-strict-transform)

Proof plan:
1. Choose finite generators of `N`, defining a surjection `v : (Fin n → B) →ₗ[B] N`.
   Localization preserves surjectivity, and the localized source is finite free.
2. By localization exactness (lem-weil-pbc-localization-module-exact), the localized
   kernel is the kernel of the localized map. By
   lem-trf-finite-presentation-surjective-module-kernel it is finitely generated.
3. Lift finitely many localized kernel generators to numerators in `ker v`; their span
   is a finitely generated submodule `K ≤ ker v` with the required localization.
4. The quotient by `K` has a finite presentation. The factor `u` of `v` is surjective;
   localization exactness and the equality of localized kernels make `u_h` bijective.
5. Every element of `ker u` is killed by a power of `h`. Tensor right exactness
   (lem-weil-pbc-tensor-right-exact) shows that the kernel after extension to `D` is
   the image of `D ⊗[B] ker u`. Each element is a finite sum of tensors, so a common
   power of the image of `h` kills it. Since `a = (algebraMap B D h) * c`, a power of
   `a` kills it as well. No flatness assumption on `D` is needed.
6. Linearity induces the map on power-torsion quotients. It is surjective. If the image
   of `x` is killed by `a^r`, then `a^r • x` is in the kernel and killed by `a^s` for
   some `s`. Thus `x` is killed by `a^(r+s)`, giving injectivity on the quotients.

The equation `u.comp K.mkQ = v` specifies the induced quotient map uniquely.
The tensor factors use the scalar-extension convention `D ⊗[B] M`, canonically
identified with `M ⊗[B] D` by `TensorProduct.comm`. The algebra `D` lives in an
independent universe `w`, so every commutative `B`-algebra is allowed.
-/
theorem exists_affine_fp_approximation_strict_transform
    (B : Type u) [CommRing B] (h : B)
    (N : Type v) [AddCommGroup N] [Module B N] [Module.Finite B N]
    [Module.FinitePresentation (Localization (Submonoid.powers h))
      (LocalizedModule (Submonoid.powers h) N)] :
    ∃ (n : ℕ) (v : (Fin n → B) →ₗ[B] N) (K : Submodule B (Fin n → B)),
      Function.Surjective v ∧ K.FG ∧ K ≤ LinearMap.ker v ∧
      (K.localized (Submonoid.powers h)).restrictScalars B =
        LinearMap.ker (IsLocalizedModule.map (Submonoid.powers h)
          (LocalizedModule.mkLinearMap (Submonoid.powers h) (Fin n → B))
          (LocalizedModule.mkLinearMap (Submonoid.powers h) N) v) ∧
      Module.FinitePresentation B ((Fin n → B) ⧸ K) ∧
      ∃ u : ((Fin n → B) ⧸ K) →ₗ[B] N,
        u.comp K.mkQ = v ∧ Function.Surjective u ∧
        Function.Bijective (IsLocalizedModule.map (Submonoid.powers h)
          (LocalizedModule.mkLinearMap (Submonoid.powers h) ((Fin n → B) ⧸ K))
          (LocalizedModule.mkLinearMap (Submonoid.powers h) N) u) ∧
        ∀ (D : Type w) [CommRing D] [Algebra B D] (a c : D),
          a = algebraMap B D h * c →
          Function.Bijective (Submodule.torsion'QuotientMap (Submonoid.powers a)
            (LinearMap.baseChange D u)) := by
  sorry

end Module
