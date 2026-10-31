/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData

/-! # Finite scalar free shifts act by tensor equivalences

Source: the scalar-generator proof of the finite proper projection formula.
(blueprint: lem-coef-finite-scalar-shift-tensor-equivalences).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

/-- The finite sections left adjoint sends each shift of the free integral scalar
module to a tensor-invertible object, both before and after proper pullback.
Source: Stacks 07A4, 06YU; the scalar-generator step of
lem-amb-proper-coproducts-projection.
(blueprint: lem-coef-finite-scalar-shift-tensor-equivalences).

Proof: quotient-scalar restriction followed by point sections is the recorded
right adjoint. Its left adjoint is derived extension from R to A_(q+1), followed
by the constant-sheaf functor. Compare it to F.sstar by adjoint uniqueness.
The free rank-one module maps to the constant coefficient unit. The analogous
adjoint comparison for F.pstar takes this unit to the coefficient unit on the
compactification. Exact inverse image and derived extension commute with shifts.
Use the natural K-flat tensor models to identify left tensor by either shifted
unit with translation by n: on a flat-term K-flat representative it is the
single-term total tensor and its signed shift identification. Localize that
natural identification and invert it by translation by -n. This works for zero
coefficient rings and empty schemes as well. -/
theorem finiteScalarShift_tensor_equivalences
    {Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E c S) (q : ℕ)
    (F : CoefPairingFiniteFrame l E c S G q) (n : ℤ) :
    let U := ((DerivedCategory.singleFunctor
      (ModuleCat.{u + 1} (coefTraceRing l E)) 0).obj
        (ModuleCat.of (coefTraceRing l E) (ULift.{0} (coefTraceRing l E))))⟦n⟧
    (Prod.sectR (F.sstar.obj U) _ ⋙ (G.baseTensors.finiteClosed q).tensor).IsEquivalence ∧
      (Prod.sectR (F.pstar.obj (F.sstar.obj U)) _ ⋙
        (G.compactTensors.finiteClosed q).tensor).IsEquivalence := by sorry

end WeilConjectures
