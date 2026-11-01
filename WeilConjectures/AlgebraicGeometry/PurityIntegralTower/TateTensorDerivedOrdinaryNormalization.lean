/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorOrdinaryTransition
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint

/-! The ordinary single model of the normalized ordered derived root transition.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- Regrouping the ordered shifted root comparison is the shifted adjunction
insertion of its ordinary semilinear tensor map. This statement is entirely on
the small etale site, before comparison inverse image or coefficient realization.

Source: smooth-purity transport, normalized Tate tower, Step 4, tensor induction.
(blueprint: lem-pur-tate-tensor-derived-ordinary-normalization).

Proof: at zero, the scalar unit comparison is scalar/single insertion of the
restriction unit; cancel the single/unit and zero-shift comparisons. For one
root, use derived_eq_scalarInsertion and naturality of the left and right
unitors. For the successor, expand tensorPowerStep and baseTateStep. Compute on
flat single complexes: the derived scalar tensorator is ordinary scalar
balancing, and singleFunctorObjTensorIso is the localization of the tensor of
the two ordinary singles. The tensor product of adjunction insertions is the
insertion of the restriction tensorator followed by the two ordinary maps.
Naturality moves the inductive comparison through this tensorator. The
root-normalized product in baseTateStep is the canonical ordered ordinary
product, so its generator formula identifies it with the next ordinary tensor.
The derivedTensorShiftIso and scalarShiftIso are the localized termwise shift
comparisons. Their additivity identifies the successive shifts 2d and 2 with
2(d+1). Every interchange sign is +1 because these shifts are even. The
single/single and scalar adjunction triangle identities give precisely the
stated map. No permutation or choice of root trivialization is involved. -/
theorem finiteTateEtaleTransition_derived
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {phi : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {T : Scheme.{u}} (r : CoefficientLineComparison phi N M hA hB T)
    (hN : 0 < N) (hM : 0 < M)
    (hNT : IsUnit (N : Γ(T, ⊤))) (hMT : IsUnit (M : Γ(T, ⊤))) (d : ℕ) :
    (r.tensorPower d).hom ≫
        (Etale.CoordinateCounitArrows.baseTateIso B M hM hB T hMT d).hom =
      (ordinaryScalar phi T).map
          (Etale.CoordinateCounitArrows.baseTateIso A N hN hA T hNT d).hom ≫
        (scalarShiftIso phi T (2 * (d : ℤ))).hom.app _ ≫
        (shiftFunctor _ (2 * (d : ℤ))).map
          (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
            (finiteTateEtaleTransition r d)) := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
