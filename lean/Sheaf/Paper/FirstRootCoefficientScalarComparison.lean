/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.PurTwistSheaves
public import Sheaf.Paper.IntegralScalarExtension
public import Sheaf.Paper.ScalarExtensionDualTowerCore

/-! # Root-normalized scalar extension in exponent one

Source: coefficient Tate twists, scalar extension of the integral first line;
Stacks Project, Modules on Sites, Tags 03EK and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Extension of the first integral root line is the first target root line.
The root-tensor formula also determines its semilinear adjunct among all maps.
Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-def-sp-tate-twist/def-coefficient-twists-detailed.md, the integral first line;
Stacks Project, Modules on Sites, Tags 03EK and 03EL.
(blueprint: lem-pur-first-root-coefficient-scalar-comparison).
Proof: present each integral line as the sheafification of the constant integer
ring tensored with the common root-limit module. The integer inclusion sends
b tensor x to its image b tensor x. The finite-residue descriptions of the
completed actions show that this additive map is semilinear for the actual
completed coefficient inclusion. Its extension by balancing is the displayed
linear map. Trivialize the common root line on a primitive-root pro-etale cover.
There this map is multiplication R_L tensor over R_E R_E to R_L, whose inverse
sends z to z tensor one. These local inverses agree because the forward map
is fixed, so they glue to an inverse. For uniqueness forget the completed action:
the root-tensor formula determines the map before sheafification, and hence
on the sheafification by its universal property. This proves uniqueness also
for competing maps whose scalar extensions are not assumed invertible. The
same universal properties apply to the empty scheme and the identity inclusion. -/
theorem firstRootCoefficientScalarComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :
    let α := integralCompletedScalarMap l E L ι S
    let β : purTwistIntegralConstant S l E ⟶ purTwistIntegralConstant S l L :=
      (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)))
    let res := SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)
    ∃ b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        α (purTwistIntegralModule S l E) ≅ purTwistIntegralModule S l L,
      (∀ (U : S.ProEtᵒᵖ) (a : (purTwistIntegralConstant S l E).obj.obj U)
        (x : (purTwistZlModule S l).val.obj U),
        b.hom.val.app U (SheafOfModules.scalarExtensionSection α
          (purTwistIntegralModule S l E) U 1 (purTwistIntegralTensor S l E U a x)) =
            purTwistIntegralTensor S l L U (β.hom.app U a) x) ∧
      ∀ c : purTwistIntegralModule S l E ⟶ res.obj (purTwistIntegralModule S l L),
        (∀ (U : S.ProEtᵒᵖ) (a : (purTwistIntegralConstant S l E).obj.obj U)
          (x : (purTwistZlModule S l).val.obj U),
          c.val.app U (purTwistIntegralTensor S l E U a x) =
            purTwistIntegralTensor S l L U (β.hom.app U a) x) →
        c = SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α
            (purTwistIntegralModule S l E) ≫
          res.map b.hom := by sorry

end WeilConjectures
