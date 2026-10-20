/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.Paper.PurityAffineLineOrientation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-! # Supported geometric restriction and the étale stalk

Source: blueprint main-20261015, affine-line orientation uniqueness, Step 4
(blueprint: lem-pur-affine-line-support-stalk).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- Evaluate an étale morphism at the constant unit in a geometric stalk.
Source: blueprint affine-line orientation uniqueness, Step 4
(blueprint: lem-pur-affine-line-support-stalk). -/
def orientationEtaleUnitGerm (P : PurityFiniteSetting.{u}) {Y : Scheme.{u}}
    {H : EtSheaves P Y} (f : P.constantEtale Y ⟶ H)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (CommRingCat.of Ω) ⟶ Y) :
    (((Scheme.pointSmallEtale y).ulift.{u + 1}).sheafFiber (A := Modules P)).obj H :=
  (((Scheme.pointSmallEtale y).ulift.{u + 1}).sheafFiber (A := Modules P)).map f
    ((((Scheme.pointSmallEtale y).ulift.{u + 1}).sheafFiberConstantSheafIso
      (ModuleCat.of P.Coefficient P.Coefficient)).inv 1)

/-- The supported pullback of a section of the Gysin sheaf is its geometric stalk.
The model and all fibre identifications are independent of the section being tested.

Source: blueprint main-20261015, affine-line orientation uniqueness, Step 4
(blueprint: lem-pur-affine-line-support-stalk).

Proof: Represent the exceptional object using its degree-zero étale model. The
supported-Hom description represents its sections by the exceptional counit. Its
cocycle normalization identifies the Gysin chart with this description. Pull back the
closed pair using the unit-normalized supported kernel map. Naturality of supported
Hom and the comparison-pullback square identify the resulting class with inverse
image of the section. Relative Kummer and its geometric base change identify the
fibre Gysin line with the inverse image of the model; the coordinate generator gives
an isomorphism, including when the geometric point is not of finite type. On the
algebraically closed fibre, global sections of an étale sheaf are its geometric stalk.
These identifications give v, and evaluating on 1 gives the displayed formula for
every f. No conservativity or conclusion about equality of global morphisms is used.
For an empty base there are no geometric points; for a disconnected base the
construction is performed on each component.
-/
theorem affineLine_support_stalk (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (chart : OrientationSupportData P h Y) :
    ∃ (H : EtSheaves P Y)
      (e : (comparisonUpperStar (Modules P) Y).obj H ≅
        (DerivedCategory.homologyFunctor (ProSheaves P Y) 0).obj (P.gysinValue h Y)),
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
      (y : Spec (CommRingCat.of Ω) ⟶ Y)
      (_hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
    ∃ p : proEtaleSupportHomTransport P (zeroSection Y)
        (zeroSection (Spec (CommRingCat.of Ω))) (AffineSpace.map (ULift.{u} (Fin 1)) y),
    ∃ v : (((Scheme.pointSmallEtale y).ulift.{u + 1}).sheafFiber (A := Modules P)).obj H ≅
      P.gysinSupport h (Spec (CommRingCat.of Ω)),
    ∀ f : P.constantEtale Y ⟶ H,
      P.orientationSupportRestriction h y p
        (chart.support.hom (P.gysinEvaluate Y
          ((comparisonUpperStar (Modules P) Y).map f ≫ e.hom))) =
        v.hom (P.orientationEtaleUnitGerm f y) := by
  sorry

end WeilConjectures.PurityFiniteSetting
