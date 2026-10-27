/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.Paper.OpenWeilCoefficientFibres

/-! # Open Weil extension comparison

Source: blueprint lem-zl-quasi-finite, proof (1) and (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
  {U₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [hUsep : IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hXsep : IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]

include hUsep hXsep

variable (J : sfCommonStageWeilSheaf D l hl U₀ Qbar ⥤
  sfCommonStageWeilSheaf D l hl X₀ Qbar)
  (a : J ⊣ zlWeilPull D l hl Qbar j₀)

include a

/-- Natural adic fibre formulas for any left adjoint to open Weil restriction.

Source: latest blueprint lem-zl-quasi-finite.proof.md, proof (1), stalk formula;
Bhatt--Scholze 6.8.14 and 6.8.15.
(blueprint: lem-zl-open-weil-geometric-fibres).

Proof: use the normalized integral open compact-support adjunction and its
rational/common-stage descent to identify J with the Weil lift of extension by
zero by uniqueness of left adjoints. Choose the intrinsic normalized adic fibre
functors from sfAdicCommonFiber_exists at all geometric points. On the open the
invertible open unit gives a natural identification of restriction of extension
with the original sheaf. Compose with pullback-composition and point-section
comparisons; these give the displayed natural iso, including both arrows in any
diagram. Outside the open choose its closed subscheme complement. Every such
field-valued point factors through that complement. restrictionIdentities gives
zero after the complementary pullback at every integral, rational and common
stage. The adic point comparison sends this zero object to zero. This proves
vanishing for arbitrary algebraically closed geometric fields, including
nonclosed image points. The scalar unit and tower identities ensure that the
same normalized fibres work simultaneously. Empty schemes give vacuous point
clauses; zero sheaves and the identity immersion satisfy the same formulas. -/
theorem openWeilGeometricFibres :
    (∃
      (FU : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        (Spec (.of Ω) ⟶ (D.geometricFiber U₀).left) →
          (generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber U₀).left ⥤
            ModuleCat.{max (u + 1) v} Qbar))
      (FX : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        (Spec (.of Ω) ⟶ (D.geometricFiber X₀).left) →
          (generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber X₀).left ⥤
            ModuleCat.{max (u + 1) v} Qbar)),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left),
        SfAdicCommonFiberSpec l (D.geometricFiber U₀).left x Qbar (FU Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left),
        SfAdicCommonFiberSpec l (D.geometricFiber X₀).left x Qbar (FX Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left),
        Nonempty (J ⋙ zlWeilHeartCarrier D l hl Qbar X₀ ⋙
          FX Ω (x ≫ zlFiberMap D j₀) ≅ zlWeilHeartCarrier D l hl Qbar U₀ ⋙ FU Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left),
        Set.range x.base ⊆ (Set.range (zlFiberMap D j₀).base)ᶜ →
        ∀ F : sfCommonStageWeilSheaf D l hl U₀ Qbar,
          IsZero ((FX Ω x).obj ((J.obj F).obj.carrier)))) := by sorry

end WeilConjectures
