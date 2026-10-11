/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor decomposition of a finite Galois field extension

Source: Stacks Project, Fundamental Groups, Tag 03SF
(blueprint: lem-exc-finite-galois-tensor-decomposition).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

/-- For a finite Galois extension `E/L`, the map from `E ⊗[L] E` to the product indexed
by `Gal(E/L)`, taking `a ⊗ b` to `(a * q b)`, is an isomorphism. Its affine spectrum
identifies the self-fibre-product of `Spec E` over `Spec L` with a finite disjoint union.
For every sheaf on the small etale site, the corresponding bijection of sections takes
restriction along the first projection to the constant family and restriction along the
second projection to the family of Galois translates.

For the algebraic part, choose a primitive element by the finite separable primitive-element
lemma and identify `E` with its minimal-polynomial quotient (the primitive-element and
quotient-field nodes). Base-change that quotient to `E` by the tensor universal property;
the monomial bases on both sides show the resulting map is an isomorphism. Normality and
separability identify the distinct roots with the `L`-automorphisms of `E` (the conjugate-root
and finite-Galois fixed-field nodes). The distinct-linear-factor Chinese remainder theorem
then gives the displayed tensor isomorphism and its formula on pure tensors. The affine
tensor/pullback consequence identifies the components and both projection maps. Finally,
the finite-separable-spectrum etale lemma supplies the site objects, and the finite-coproduct
sheaf-sections theorem gives the bijection and both restriction formulas (Stacks, Tag 03SF).
(blueprint: lem-exc-finite-galois-tensor-decomposition) -/
theorem finiteGaloisTensorDecomposition
    (L E : Type u) [Field L] [Field E] [Algebra L E]
    [FiniteDimensional L E] [IsGalois L E]
    (F : Sheaf ((Spec (CommRingCat.of L)).smallEtaleTopology) (Type v)) :
    (∃ φ : (E ⊗[L] E) ≃ₐ[L] ((E ≃ₐ[L] E) → E),
      ∀ (a b : E) (q : E ≃ₐ[L] E), φ (a ⊗ₜ[L] b) q = a * q b) ∧
    (let π : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L) :=
        Spec.map (CommRingCat.ofHom (algebraMap L E))
      ∃ (hπ : Etale π) (hW : Etale (pullback.fst π π ≫ π)),
        letI : Etale π := hπ
        letI : Etale (pullback.fst π π ≫ π) := hW
        let U : (Spec (CommRingCat.of L)).Etale := .mk π
        let V : (Spec (CommRingCat.of L)).Etale := .mk (pullback.fst π π ≫ π)
        ∃ (p₁ p₂ : V ⟶ U) (σ : (E ≃ₐ[L] E) → (U ⟶ U)),
          p₁.left = pullback.fst π π ∧
          p₂.left = pullback.snd π π ∧
          (∀ q : E ≃ₐ[L] E, (σ q).left =
            Spec.map (CommRingCat.ofHom q.toRingEquiv.toRingHom)) ∧
          ∃ β : F.obj.obj (Opposite.op V) ≃
              ((E ≃ₐ[L] E) → F.obj.obj (Opposite.op U)),
            (∀ s q, β (F.obj.map p₁.op s) q = s) ∧
            (∀ s q, β (F.obj.map p₂.op s) q = F.obj.map (σ q).op s)) := by
  sorry

end AlgebraicGeometry
