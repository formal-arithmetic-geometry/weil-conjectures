/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreLinearCurrent.CondensedFibreLinearOperationsStatement
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Tensor injection on native middle-image stalks

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
last paragraph, the injection of invariant tensors.
(blueprint: lem-wf-native-middle-tensor-eigenvalue).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2
open NativeCondensedModule
open scoped TensorProduct

/-- The middle-image fibres have an injective tensor map compatible with local Frobenius.
Source: latest blueprint, sk-p-real-semi.proof.md, final paragraph, the injection of
inertia invariant tensors into the invariants of the tensor product
(blueprint: lem-wf-native-middle-tensor-eigenvalue).

Proof: ordinary restriction identifies a missing-point middle-image fibre with
inertia invariants in the generic fibre. Tensor the two inclusions into their generic
fibres, use injectivity of tensor products over a field, and observe that each pure
tensor of invariant vectors is invariant. Restriction is monoidal and the inertia
comparison commutes with the canonical Weil return, so the map commutes with the
specified local operators. At a point in the open use the direct-image counit and
canonical monoidal fibre comparison. Extend the local residue closure to the chosen
geometric point; scalar extension is faithfully flat and preserves the injection.
If either source fibre is zero the tensor source is zero, and the map is injective. -/
theorem middleWeilImage_tensor_injection
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {U₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (N : WeilModule D l U₀)
    (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    ∃ t : (fibre l D (middleWeilImage D l j₀ M).carrier (localClosedPoint D X₀ x i hi))
        ⊗[ULift.{u + 1} (PadicAlgCl l)]
          (fibre l D (middleWeilImage D l j₀ N).carrier (localClosedPoint D X₀ x i hi)) →ₗ[
            ULift.{u + 1} (PadicAlgCl l)]
        (fibre l D (middleWeilImage D l j₀
          (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius U₀) M N)).carrier
            (localClosedPoint D X₀ x i hi)),
      Function.Injective t ∧ ∀ v,
        (closedOperator D l X₀ (middleWeilImage D l j₀
          (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius U₀) M N))
            x i hi).hom (t v) =
          t (TensorProduct.map
            (closedOperator D l X₀ (middleWeilImage D l j₀ M) x i hi).hom
            (closedOperator D l X₀ (middleWeilImage D l j₀ N) x i hi).hom v) := by sorry

end WeilConjectures.NativeL2
