/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Continuous functions into a finite sum of lattices

Source: main-20261015 blueprint, sk-lem-stratified-lattice.proof.md,
"Pushing down by the trace" (blueprint: lem-sfb-continuous-lattice-sum).

The sheaf assertions are stated by their sections and restriction maps: the
submodule sum is equal sectionwise, the rank-r trivialization commutes with
restriction, and the scalar-extension comparison is specified on pure tensors.
Thus the tensor comparison is the one induced by the actual lattice inclusion.
-/

@[expose] public section

universe u v w z

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

set_option autoImplicit false

/-- The actual inclusion of continuous lattice-valued functions into vector-valued functions.
Source: main-20261015 blueprint, sk-lem-stratified-lattice.proof.md,
"Pushing down by the trace" (blueprint: lem-sfb-continuous-lattice-sum). -/
def continuousLatticeInclusion {E : Type v} [NormedField E] (A : Subring E)
    {r : ℕ} (L : Submodule A (Fin r → E)) (Z : Type z) [TopologicalSpace Z] :
    C(Z, L) →ₗ[C(Z, A)] C(Z, Fin r → E) where
  toFun f := ⟨fun x ↦ (f x : Fin r → E), continuous_subtype_val.comp f.continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A finite sum of full lattices has a continuous linear section; continuous
functions preserve this sum, and on every small pro-etale site the resulting
module sheaf is free of rank r and its actual inclusion rationalizes to an isomorphism.

Source: main-20261015 blueprint, sk-lem-stratified-lattice.proof.md,
"Pushing down by the trace" (blueprint: lem-sfb-continuous-lattice-sum).

Proof plan:
1. Apply lem-sfb-finite-sum-lattice to obtain an integral basis of the sum,
   also a field basis, whose coordinate map is a homeomorphism.
2. Lift each basis vector to the finite product of the input lattices. Extend
   these lifts A-linearly using the coordinate homeomorphism. Coordinatewise
   finite sums and scalar multiplication show continuity and q composed with s is identity.
3. Postcompose any continuous function with the components of s. The resulting
   continuous functions sum to the given function, for every space Z.
4. Continuous functions into each lattice and the sum satisfy the sheaf condition:
   use lem-cbc-continuous-functions-fpqc-sheaf and restrict to the pro-etale site.
   Postcomposition with the basis homeomorphism gives the displayed rank-r
   trivializations. They commute with restriction, which is precomposition.
5. Step 3 identifies the sectionwise submodule sum with the sum-lattice sheaf.
   Since this is already a sheaf, it is also the sum as submodule sheaves.
6. Under the trivialization, the actual inclusion is the constant matrix whose
   columns are the basis vectors. After tensoring with continuous E-valued
   functions it is invertible with inverse the inverse matrix. The pure-tensor
   formula specifies this actual comparison. It commutes with restriction and
   identifies the presheaf tensor with an existing sheaf, so sheafification gives
   the same isomorphism for the sheaf tensor of def-pur-sheaf-tensor-product.
   All formulas also hold for r = 0.
-/
theorem continuous_lattice_sum
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (r : ℕ) (J : Type w) [Fintype J] [Nonempty J]
    (L : J → Submodule (Padic.coefficientExtensionIntegers ℓ E) (Fin r → E))
    (hL : ∀ j, ∃ b : Module.Basis (Fin r) (Padic.coefficientExtensionIntegers ℓ E) (L j),
      ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) :
    (∃ s : ↥(⨆ j, L j) →L[Padic.coefficientExtensionIntegers ℓ E] (∀ j, L j),
      ∀ x, (∑ j, ((s x j : L j) : Fin r → E)) = (x : Fin r → E)) ∧
    (∀ (Z : Type z) [TopologicalSpace Z] (f : C(Z, ↥(⨆ j, L j))),
      ∃ g : ∀ j, C(Z, L j), ∀ x,
        (∑ j, ((g j x : L j) : Fin r → E)) = (f x : Fin r → E)) ∧
    (∀ S : Scheme.{u},
      (∀ j, Presheaf.IsSheaf (Scheme.ProEt.topology S)
        ((Scheme.ProEt.forget S ⋙ Over.forget S).op ⋙ continuousMapPresheafAb (L j))) ∧
      Presheaf.IsSheaf (Scheme.ProEt.topology S)
        ((Scheme.ProEt.forget S ⋙ Over.forget S).op ⋙
          continuousMapPresheafAb ↥(⨆ j, L j)) ∧
      (∀ U : S.ProEt,
        (⨆ j, (continuousLatticeInclusion (Padic.coefficientExtensionIntegers ℓ E)
          (L j) U.left).range) =
        (continuousLatticeInclusion (Padic.coefficientExtensionIntegers ℓ E)
          (⨆ j, L j) U.left).range) ∧
      (∃ e : ∀ U : S.ProEt,
          (Fin r → C(U.left, Padic.coefficientExtensionIntegers ℓ E)) ≃ₗ[
            C(U.left, Padic.coefficientExtensionIntegers ℓ E)] C(U.left, ↥(⨆ j, L j)),
        ∀ (U V : S.ProEt) (a : V ⟶ U)
          (x : Fin r → C(U.left, Padic.coefficientExtensionIntegers ℓ E)),
          e V (fun i ↦ (x i).comp a.left.base.hom) = (e U x).comp a.left.base.hom) ∧
      (∀ U : S.ProEt,
        ∃ e : (C(U.left, E) ⊗[C(U.left, Padic.coefficientExtensionIntegers ℓ E)]
            C(U.left, ↥(⨆ j, L j))) ≃+ C(U.left, Fin r → E),
          ∀ (a : C(U.left, E)) (f : C(U.left, ↥(⨆ j, L j))) (x : U.left),
            e (a ⊗ₜ f) x = a x • (f x : Fin r → E))) := by
  sorry

end AlgebraicGeometry.ProEtale
