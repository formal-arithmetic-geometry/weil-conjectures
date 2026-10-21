/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.PurityFiniteKummerDefinitions

/-! # Finite root tensors under base change

Source: finite Kummer-level blueprint, proof steps 9--11; Stacks Tag 03PK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The scalar-extended finite-root base-change isomorphism.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, steps 9--11;
Stacks Tags 03PK, 040M and 03EL.
(blueprint: lem-pur-kummer-root-tensor-base-change)

Proof: the positive coefficient quotient is finite by
Padic.finite_coefficientExtensionRing, so the existing finite-coefficient
comparison applies. Use the root-square and tensor-unit statements of
lem-amb-finite-root-site-comparison, transported from fixed-module sheaves to
modules over the constant ring sheaf by lem-cbc-constant-ring-module-sheaves.
These equivalences preserve underlying sections, additive maps, and constant
scalar actions. General local coefficients are checked after the locally
surjective constant-sheaf unit, so equality on constants implies the displayed
formula for every section z. The root maps pull units back along the
fibre-product projections.
They commute with restriction. For each positive exponent m=ell^(N+1),
the root sheaf is represented
on the etale site by the finite etale scheme defined by z^m=1: on affine charts this
is the polynomial quotient universal property, and the descriptions glue. Since
ell is invertible, the derivative m*z^(m-1) is a unit at every root. Base change
preserves that scheme and its universal root. Inverse-image adjunction and Yoneda
identify the canonical root map with the representable base-change isomorphism.
The pro-etale comparison functor preserves it. Extend scalars by the constant
coefficient map a. The canonical constant-ring pullback comparison and the tensor
universal property give delta. On local pure tensors its formula is exactly the
one displayed. Its inverse is induced by the inverse root comparison and the
inverse constant-ring comparison. The two composites are identities on pure
tensors and hence after sheafification. Empty schemes give zero sheaves and the
same formulas; no infinite-limit preservation by inverse image is used. -/
theorem kummer_root_tensor_base_change (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n)
    (T T' : Scheme.{u}) (f : T' ⟶ T)
    (hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x))
    (hT' : ∀ x : T', IsUnit (P.coefficients.l : T'.presheaf.stalk x)) :
    ∃ δ : (Scheme.tatePullback f (P.kummerCoefficient n)).obj
          (P.kummerRootsTensor n N a T) ≅ P.kummerRootsTensor n N a T',
      ∀ (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
          (y : (Scheme.proEtaleRootsOfUnitySheaf T (P.coefficients.l ^ (N + 1))).obj.obj
            (op U)),
          δ.hom.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
              (Scheme.tateUnit f (P.kummerCoefficient n) (P.kummerRootsTensor n N a T) U
                (P.kummerTargetTensor n N a T U z y)) =
            P.kummerTargetTensor n N a T' ((Scheme.proEtaleBaseChange f).obj U)
              (Scheme.tateRingUnit f (P.kummerCoefficient n) U z)
              ((Scheme.proEtaleRootsOfUnityDirectImageMap f
                (P.coefficients.l ^ (N + 1))).hom.app (op U) y) := by
  sorry

end WeilConjectures.PurityFiniteSetting
