module

public import Mathlib.LinearAlgebra.Contraction

/-! # Finite-free maps and least coefficient support

Source: Stacks Project, algebra.tex, Tags 059G (remark-flat-ML) and 059S
(lemma-flat-ML-criterion), the paragraph beginning "Since M_i is free and finite"
(blueprint: lem-trf-finite-free-map-coefficient-support).

The canonical map and its inverse are Mathlib's `dualTensorHom` and
`dualTensorHomEquiv`. The coefficient submodule of a map `u` is the range of
Mathlib's `LinearMap.dualMap`; no new notion of tensor product or support is introduced.
-/

@[expose] public section

open scoped TensorProduct BigOperators

universe uR uP uN uN' uE uι uκ

namespace LinearMap

/-- Finite-free duality, its basis formulas and naturality, and the least coefficient
support of a map to a finite-free module.

Source: Stacks Project, algebra.tex, Tags 059G (remark-flat-ML) and 059S
(lemma-flat-ML-criterion), the paragraph beginning "Since M_i is free and finite"
(blueprint: lem-trf-finite-free-map-coefficient-support).

Proof:
1. Choose a finite basis `e` of `P`. Its coordinate maps form a basis of the dual:
   expand a functional using its values on `e`, and evaluate at each basis vector
   to prove independence. Thus the dual is finite free, including in rank zero.
2. The bilinear map `(h, n) ↦ (p ↦ h p • n)` induces `dualTensorHom` by the tensor
   universal property of def-weil-pbc-module-tensor-product. The finite sum
   `g ↦ ∑ a, e.dualBasis a ⊗ₜ g (e a)` is linear.
3. Applying the two maps successively gives the identity: use the basis expansion
   of `p` in one direction, and that of `h` in the other on pure tensors. Pure
   tensors generate the tensor product. This proves bijectivity and the inverse
   formula for every finite basis.
4. For `v : N →ₗ[R] N'`, both sides of naturality agree on a pure tensor by
   `v`'s compatibility with scalar multiplication. Extend by tensor generation.
5. Choose any finite basis `b` of `E` and set `c t = (b.dualBasis t).comp u`.
   The basis expansion of `u p` shows that `∑ t, c t ⊗ₜ b t` represents `u`.
   Each `c t` is in the range of `u.dualMap`; expanding an arbitrary functional
   on `E` in the dual basis proves that this range is the span of the `c t`.
6. For `M = G` or `M = Module.Dual R P`, the bilinear coordinate maps
   `(m, e) ↦ b.dualBasis t e • m` induce maps `q t : M ⊗[R] E →ₗ[R] M`.
   The basis identity gives `w = ∑ t, q t w ⊗ₜ b t`, first on pure tensors
   and then on every tensor by generation.
7. These coordinate maps commute with the inclusion-induced map from `G ⊗[R] E`.
   If a tensor maps to zero, all its coordinates vanish by injectivity of `G.subtype`;
   the reconstruction formula in step 6 makes the tensor zero.
8. If the coefficient range lies in `G`, the sum in step 5 lifts to `G ⊗[R] E`.
   Conversely, a lift has every coordinate `c t` in `G` by steps 5--7, so the
   span calculation gives containment of the coefficient range in `G`.
   Taking `G` to be that range proves it supports the tensor and is least.
   Empty bases give empty sums, covering both rank-zero cases.
-/
theorem finite_free_map_coefficient_support
    (R : Type uR) [CommRing R] (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] :
    Module.Free R (Module.Dual R P) ∧ Module.Finite R (Module.Dual R P) ∧
    (∀ (N : Type uN) [AddCommGroup N] [Module R N],
      Function.Bijective (dualTensorHom R P N) ∧
      (∀ (h : Module.Dual R P) (n : N) (p : P),
        dualTensorHom R P N (h ⊗ₜ[R] n) p = h p • n) ∧
      (∀ (ι : Type uι) [Fintype ι] [DecidableEq ι]
          (e : Module.Basis ι R P) (g : P →ₗ[R] N),
        (dualTensorHomEquiv R P N).symm g = ∑ a, e.dualBasis a ⊗ₜ[R] g (e a))) ∧
    (∀ (N : Type uN) [AddCommGroup N] [Module R N]
        (N' : Type uN') [AddCommGroup N'] [Module R N']
        (v : N →ₗ[R] N') (z : Module.Dual R P ⊗[R] N),
      dualTensorHom R P N' (v.lTensor (Module.Dual R P) z) =
        v.comp (dualTensorHom R P N z)) ∧
    (∀ (E : Type uE) [AddCommGroup E] [Module R E]
        [Module.Free R E] [Module.Finite R E] (u : P →ₗ[R] E),
      (∀ G : Submodule R (Module.Dual R P),
        Function.Injective (G.subtype.rTensor E) ∧
        ((dualTensorHomEquiv R P E).symm u ∈ LinearMap.range (G.subtype.rTensor E) ↔
          LinearMap.range u.dualMap ≤ G)) ∧
      IsLeast {G : Submodule R (Module.Dual R P) |
        (dualTensorHomEquiv R P E).symm u ∈ LinearMap.range (G.subtype.rTensor E)}
        (LinearMap.range u.dualMap) ∧
      (∀ (κ : Type uκ) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ R E),
        (dualTensorHomEquiv R P E).symm u =
          ∑ t, ((b.dualBasis t).comp u) ⊗ₜ[R] b t ∧
        LinearMap.range u.dualMap =
          Submodule.span R (Set.range (fun t ↦ (b.dualBasis t).comp u)))) := by
  sorry

end LinearMap
