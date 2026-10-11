/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker J1
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.Galois.Basic

/-!
# Fibre product of a finite Galois field extension

Source: Stacks Project, `pione.tex`, Tag 03SF (blueprint:
lem-exc-finite-galois-algebra-tensor-decomposition).
-/

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

/-- (blueprint: lem-exc-finite-galois-algebra-tensor-decomposition) For a finite Galois
extension `E/L`, a supplied algebra isomorphism sending `a ⊗ b` to `(a * q b)₍q₎`
identifies the affine fibre product with the finite coproduct of copies of `Spec E`.
Under the affine pullback isomorphism (lem-weil-pbc-fibre-product-affine-spectra),
the component maps are induced by the coordinate projections of the product ring
(lem-weil-pbc-spec-finite-product-fields). On the `q`-th component the first pullback
projection is the identity and the second is `Spec q`: the tensor inclusions
`a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` become `a ↦ a` and `b ↦ q b` after evaluation at `q`.
The argument includes `E = L`, when the automorphism group has one element.
Source: Stacks Project, `pione.tex`, Tags 03SF, 01I4, and 00ED. -/
theorem finiteGaloisTensorCoproduct
    (L E : Type u) [Field L] [Field E] [Algebra L E]
    [FiniteDimensional L E] [IsGalois L E]
    (φ : (E ⊗[L] E) ≃ₐ[L] ((E ≃ₐ[L] E) → E))
    (hφ : ∀ (a b : E) (q : E ≃ₐ[L] E), φ (a ⊗ₜ[L] b) q = a * q b) :
    ∃ e : (∐ fun _ : E ≃ₐ[L] E => Spec (.of E)) ≅
        pullback (Spec.map (CommRingCat.ofHom (algebraMap L E)))
          (Spec.map (CommRingCat.ofHom (algebraMap L E))),
      (∀ q : E ≃ₐ[L] E,
        Sigma.ι (fun _ : E ≃ₐ[L] E => Spec (.of E)) q ≫ e.hom ≫
          pullback.fst _ _ = 𝟙 (Spec (.of E))) ∧
      (∀ q : E ≃ₐ[L] E,
        Sigma.ι (fun _ : E ≃ₐ[L] E => Spec (.of E)) q ≫ e.hom ≫
          pullback.snd _ _ = Spec.map (CommRingCat.ofHom q.toRingEquiv.toRingHom)) := by
  sorry

end AlgebraicGeometry
