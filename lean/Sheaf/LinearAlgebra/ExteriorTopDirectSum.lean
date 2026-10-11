/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Top exterior power of a direct sum

Source: Weil conjectures blueprint, `sec-picard-framework/sk-thm-picard-rr/lem-sc-riemann-roch`,
proof of (*), determinant paragraph (blueprint: lem-sc-exterior-top-direct-sum).

## Main statements

* `exteriorPower.existsUnique_topDirectSum`: the canonical isomorphism characterized on wedges.
* `exteriorPower.topDirectSum_natural`: its compatibility with isomorphisms of the two modules.
-/

universe u v w v' w'

open scoped TensorProduct

namespace exteriorPower

/-- Source: Weil conjectures blueprint, `lem-sc-riemann-roch`, proof of (*), determinant
paragraph (blueprint: lem-sc-exterior-top-direct-sum).

Choose bases of `M` and `N`. The top exterior-power basis lemma
`lem-weil-pbc-exterior-power-free-basis` gives one-element wedge bases of their top powers
and of the top power of the concatenated basis of `M × N`.
The product-basis lemma `lem-sc-tensor-product-free-basis` gives the tensor of the two
one-element bases as a basis of the tensor product. Sending this tensor basis vector to
the concatenated wedge basis vector defines an isomorphism with coefficient +1.
Expand arbitrary vectors in the chosen bases by multilinearity, remove repeated factors
by alternation, and reorder using anticommutation: the same coefficients occur before
and after the two inclusions, giving the displayed formula on all pure wedges.
Pure wedges span exterior powers and pure tensors span the tensor product, so this
formula determines the isomorphism uniquely and makes it independent of the bases. -/
theorem existsUnique_topDirectSum
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (r s : ℕ) (_bM : Module.Basis (Fin r) R M) (_bN : Module.Basis (Fin s) R N) :
    ∃! e : (⋀[R]^(r + s) (M × N)) ≃ₗ[R] ((⋀[R]^r M) ⊗[R] (⋀[R]^s N)),
      ∀ (m : Fin r → M) (n : Fin s → N),
        e.symm ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n)) =
          ιMulti R (r + s) (Fin.append (fun i ↦ (m i, 0)) (fun j ↦ (0, n j))) := by
  sorry

/-- Source: Weil conjectures blueprint, `lem-sc-riemann-roch`, proof of (*), determinant
paragraph (blueprint: lem-sc-exterior-top-direct-sum).

Apply isomorphisms `f` and `g` to the pure-wedge characterization of the two isomorphisms.
Exterior-power maps send each wedge to the wedge of the images, tensor-product maps send
pure tensors to the tensors of their images, and the inclusions into the direct sum
commute with `f` and `g`. Thus the naturality square commutes on pure tensors of wedges.
These span by the exterior-power and tensor-product universal properties, so the square
commutes everywhere. Taking inverses gives the displayed naturality in the orientation
from the top exterior power of the direct sum to the tensor product. -/
theorem topDirectSum_natural
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {M' : Type v'} [AddCommGroup M'] [Module R M']
    {N' : Type w'} [AddCommGroup N'] [Module R N']
    (r s : ℕ) (f : M ≃ₗ[R] M') (g : N ≃ₗ[R] N')
    (e : (⋀[R]^(r + s) (M × N)) ≃ₗ[R] ((⋀[R]^r M) ⊗[R] (⋀[R]^s N)))
    (e' : (⋀[R]^(r + s) (M' × N')) ≃ₗ[R] ((⋀[R]^r M') ⊗[R] (⋀[R]^s N')))
    (he : ∀ (m : Fin r → M) (n : Fin s → N),
      e.symm ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n)) =
        ιMulti R (r + s) (Fin.append (fun i ↦ (m i, 0)) (fun j ↦ (0, n j))))
    (he' : ∀ (m : Fin r → M') (n : Fin s → N'),
      e'.symm ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n)) =
        ιMulti R (r + s) (Fin.append (fun i ↦ (m i, 0)) (fun j ↦ (0, n j))))
    (x : ⋀[R]^(r + s) (M × N)) :
    e' (map (r + s) (f.toLinearMap.prodMap g.toLinearMap) x) =
      TensorProduct.map (map r f.toLinearMap) (map s g.toLinearMap) (e x) := by
  sorry

end exteriorPower
