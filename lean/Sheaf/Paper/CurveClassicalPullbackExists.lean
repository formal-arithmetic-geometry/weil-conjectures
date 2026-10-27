/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.CurveRestrictionFiltrationData

/-! # CurveClassicalPullbackExists

Source: blueprint latest, real-mixed-by-curves, paragraph 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor (IsoAlgebra)
open Opposite
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

variable (m : ℕ) (hm : 1 ≤ m)
  (C₀ : Over (Spec (.of (D.extensionSubfield m hm))))
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
  (h₀ : C₀ ⟶ constantExtensionModel D m hm X₀) [IsClosedImmersion h₀.left]


variable [IsSeparated C₀.hom]
  [Fact (∀ x : (D.geometricFiber X₀).left,
    IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))]
  [Fact (∀ x : ((constantExtensionDatum D m hm).geometricFiber C₀).left,
    IsUnit (l : ((constantExtensionDatum D m hm).geometricFiber C₀).left.presheaf.stalk x))]

/-- A normalized classical curve inverse image, with lisse realized carriers.
Source: BS 6.8.4(1),(4), 6.8.14 and 6.8.15; blueprint real-mixed-by-curves, paragraph 2
(blueprint: lem-zl-curve-classical-pullback-exists).

Proof:
Pull finite locally free systems back level by level along the geometric composite.
Their pulled-back trivializations and reduction maps define the ordinary classical
inverse image. Apply completed_system_comparison to compare completion and
rationalization with this inverse image. The normalized rational realization
identifies the resulting geometric functor with commonStageDerivedPullback.
Use hR's normalized constant comparison followed by the immersion pullback
compositor for underlying. Its composition equation is underlying_normalization.
The composition equations for the completed systems and realization, applied to
geometric Frobenius and the ordered m-fold Weil map, define classical on Weil
objects and give realization and realization_underlying, naturally on all arrows.
Use the supplied RX and RC normalizations, rather than choosing new realizations.
The same finite locally free models show the realized restricted carriers are
common-stage lisse. At every algebraically closed geometric point, the pullback
composition comparison gives a natural isomorphism of the classical fibre functors;
its maps are the same finite-level pullback maps through completion and rationalization.
Empty schemes and zero ranks use the zero systems. -/
theorem zl_curve_classical_pullback_exists
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hR : ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω R)
    (RX : ZlClassicalRealization D l hl Ω X₀)
    (RC : ZlClassicalRealization (constantExtensionDatum D m hm) l hl Ω C₀)
    : ∃ c : ZlCurveClassicalPullback D l hl Ω X₀ m hm C₀ h₀ RX RC R,
      (∀ H : ZlClassicalWeil D l Ω X₀,
        @IsCommonStageLisse l _ Ω _ _ _
        ((constantExtensionDatum D m hm).geometricFiber C₀).left
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl C₀)
        ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj
          ((RX.weil D l hl Ω X₀).obj H)).obj.carrier) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
        (x : Spec (.of κ) ⟶ ((constantExtensionDatum D m hm).geometricFiber C₀).left),
      Nonempty (c.classical ⋙
          IsoAlgebra.forget (lisseAlgebraicAutomorphismPullback
            ((constantExtensionDatum D m hm).geometricFrobenius C₀) l Ω) ⋙
          lisseAlgebraicFiberFunctor l
            ((constantExtensionDatum D m hm).geometricFiber C₀).left x Ω ≅
        IsoAlgebra.forget (lisseAlgebraicAutomorphismPullback
            (D.geometricFrobenius X₀) l Ω) ⋙
          lisseAlgebraicFiberFunctor l (D.geometricFiber X₀).left
            (x ≫ zlCurveGeometricMap D X₀ m hm C₀ h₀) Ω) := by sorry

end WeilConjectures
