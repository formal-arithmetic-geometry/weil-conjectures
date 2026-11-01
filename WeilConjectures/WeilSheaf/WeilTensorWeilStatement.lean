/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.SmoothPurity.WeilSheafComplex

/-! # Tensor product of strict Weil complexes

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-r-real-linear/
lem-wf-tensor-weil.md, order 3982, and its companion proof, steps 1–6
(blueprint: lem-wf-tensor-weil).

The strict-pair category is the landed category over the geometric fibre and the
specified geometric Frobenius. Exactness is asserted on the underlying derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- The tensor bifunctor on strict bounded constructible Weil complexes, with its
specified underlying objects, arrows and Frobenius, and exactness in each variable: for every
`K ∈ D^b_c(X, Λ)`, tensoring with `K` on either side is a triangulated functor of the
ambient derived category (so it restricts to `D^b_c(X, Λ)` by the tensor closure).
Source: latest blueprint, sec-purity-real-sheaves/sk-r-real-linear/lem-wf-tensor-weil.md,
order 3982, displayed tensor formula and final sentence (blueprint: lem-wf-tensor-weil). -/
structure WfTensorWeilData
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (c : WeilCoefficient ell) where
  tensor : strictWeilComplexCategory D ell hell X₀ c ×
    strictWeilComplexCategory D ell hell X₀ c ⥤ strictWeilComplexCategory D ell hell X₀ c
  carrier : ∀ K L : strictWeilComplexCategory D ell hell X₀ c,
    (tensor.obj (K, L)).obj.carrier =
      (wfCondensedTensor (WeilCoefficient.ab c) (D.geometricFiber X₀).left).obj
        (K.obj.carrier, L.obj.carrier)
  frobenius : ∀ K L : strictWeilComplexCategory D ell hell X₀ c,
    HEq (tensor.obj (K, L)).obj.str
      (wfCondensedGeometricTensorFrobenius (WeilCoefficient.ab c) D X₀ K.obj L.obj)
  map : ∀ (K K' L L' : strictWeilComplexCategory D ell hell X₀ c)
      (f : K ⟶ K') (g : L ⟶ L'),
    HEq (tensor.map (Prod.mkHom f g)).hom.hom.f
      ((wfCondensedTensor (WeilCoefficient.ab c) (D.geometricFiber X₀).left).map
        (Prod.mkHom f.hom.hom.f g.hom.hom.f))
  exact_left : ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left) Ab.{u + 1})
        (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left)),
    boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left)
      K →
    ∃ s : ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
      (D.geometricFiber X₀).left).obj K).CommShift ℤ,
      (fun [_sInst : ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
        (D.geometricFiber X₀).left).obj K).CommShift ℤ] ↦
          ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
            (D.geometricFiber X₀).left).obj K).IsTriangulated) (_sInst := s)
  exact_right : ∀ L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left) Ab.{u + 1})
        (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left)),
    boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left)
      L →
    ∃ s : ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
      (D.geometricFiber X₀).left).flip.obj L).CommShift ℤ,
      (fun [_sInst : ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
        (D.geometricFiber X₀).left).flip.obj L).CommShift ℤ] ↦
          ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
            (D.geometricFiber X₀).left).flip.obj L).IsTriangulated) (_sInst := s)

/-- The specified derived tensor defines a bifunctor on strict Weil complexes over
`E̲` or `ℚ̲̄_ℓ`, lying over the exact derived tensor on bounded constructible complexes.
Source: latest blueprint, sec-purity-real-sheaves/sk-r-real-linear/lem-wf-tensor-weil.md,
order 3982, entire statement, and companion proof (blueprint: lem-wf-tensor-weil).

Proof (the node's six steps):
1. Work with the recorded condensed coefficients on `X = X₀ × k`, strict pairs for
   geometric Frobenius, and the Layer B relative derived tensor computed by K-flat models.
2. Finite type survives base change, so X is Noetherian and quasi-separated. Choose a
   finite affine finite-type cover; each chart is separated over k, even when X is not.
3. Exact restriction commutes with cohomology and derived tensor. Rational tensor closure
   on each chart gives bounded constructibility locally. A common finite interval bounds
   all charts, the sheaf axiom detects vanishing, and Zariski locality glues constructibility.
   On empty X every module sheaf is zero, so no nonempty cover or interval is needed.
4. A K-flat representative gives a shift-compatible triangulated tensor functor in one
   variable; reversal gives the other variable. The bounded constructible full triangulated
   subcategory inherits these comparisons and distinguished triangles.
5. Compose the natural pullback/tensor isomorphism with the tensor of the two supplied
   Weil isomorphisms. Its inverse is the tensor of their inverses followed by the inverse
   comparison. This is exactly `wfCondensedGeometricTensorFrobenius`, with no cocycle datum.
6. Naturality of the comparison and the two intertwining equations show that T(f,g)
   intertwines these structures. Identity and composition are inherited from T, since
   equality of strict-pair arrows is equality of their underlying arrows. Thus objects,
   Frobenius and maps have precisely the specified formulas. -/
theorem wf_tensor_weil_strict
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (c : WeilCoefficient ell) :
    Nonempty (WfTensorWeilData D ell hell X₀ c) := by
  sorry

end WeilConjectures
