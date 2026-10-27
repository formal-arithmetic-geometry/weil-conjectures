/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.Paper.LineKummerFieldRealization
public import Sheaf.Paper.SectionCompactSourceExchange
public import Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization

/-! # Supported Cartier Kummer pullback in the fixed D+ presentation

Source: blueprint latest, rank-one Thom proof, Step 3; Cartier Kummer base change.
(blueprint: lem-pur-supported-cartier-derived-pullback)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.SupportedCartierDerivedPullback
open Scheme LineKummerField

/-- The supported degree-two Kummer class commutes with Cartesian pullback in D+.
The source comparison is the specified supported-constant exchange, fixed by its
constant restriction equation. No compact-support functor is present in this lemma.

Source: blueprint latest, rank-one Thom proof, Step 3, and Cartier Kummer base change
(blueprint: lem-pur-supported-cartier-derived-pullback).

Proof: Extract the pro-etale base-change clause of the uniquely normalized Cartier
Kummer family. It supplies a supported-source isomorphism b, a projection-normalized
Tate pullback p, preservation of the constant restriction, and the Ext equation
mk0(b).comp(kappa') = mapExactFunctor(kappa).comp(mk0(p)). The stipulated uniqueness
hypothesis identifies b.hom with the canonical supported-constant exchange: the
constant upper-star comparison is the adjoint of the constant direct-image unit,
so its restriction equation is precisely the one in Kummer base change.
Apply Ext.hom to its equation and the formulas for Ext.comp_hom, mk0_hom and
mapExactFunctor_hom. This gives the equality of ambient derived arrows, with the
single-functor comparisons and shift comparison displayed in the conclusion.
Use the fully faithful inclusion of D+ into D to reflect that equality. The
singleFunctor inclusion isomorphisms identify extPlusMap with Ext.hom, and the
inclusion commutes with exact pullback and shifts. Cancel these isomorphisms and
substitute b.hom. This proves exactly the displayed equality. The empty divisor
and empty schemes require no exceptions: the normalized constant and Ext equations
still hold, and no section, dimension, finiteness or flatness property is used. -/
theorem supported_cartier_derived_pullback
    (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
    [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)
    {B X B' X' : Scheme.{u}} {g : B' ⟶ B} {v : X' ⟶ X}
    (z : B ⟶ X) (z' : B' ⟶ X') [IsClosedImmersion z] [IsClosedImmersion z']
    (sqZ : ChosenCartesianSquare g z' z v)
    (hI : z.ker.IsInvertible) (hI' : z'.ker.IsInvertible)
    (hX : IsUnit (l : Γ(X, ⊤)))
    (hX' : IsUnit (l : Γ(X', ⊤)))
    (hnorm : ∀ d : (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
          (SupportedConstantNormalization.supported (finiteTateCoefficient l F n) true z) ⟶
            SupportedConstantNormalization.supported (finiteTateCoefficient l F n) true z',
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).map
        (SupportedConstantNormalization.restriction (finiteTateCoefficient l F n) true z) ≫ d =
        (SupportedConstantNormalization.unitIso (finiteTateCoefficient l F n) true v).hom ≫
          SupportedConstantNormalization.restriction (finiteTateCoefficient l F n) true z' →
      d = SupportedConstantNormalization.exchange (finiteTateCoefficient l F n) true sqZ) :
    ∃ p : (ProEtale.upperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
        (finiteTateProSheaf l F n X 1) ≅
          finiteTateProSheaf l F n X' 1,
      IsFiniteTateProPullback l F n X v 1 p ∧
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
          v).mapDerivedCategoryPlus.map (proClass l F n z hI hX) ≫
        (((ProEtale.upperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
            v).mapDerivedCategoryPlus.commShiftIso (2 : ℤ)).app _ ≪≫
          (shiftFunctor _ (2 : ℤ)).mapIso
            ((Functor.mapDerivedCategoryPlusSingleFunctor
              (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v)
                0).app _ ≪≫
              (DerivedCategory.Plus.singleFunctor _ 0).mapIso p)).hom =
      SectionCompactSource.proBeta (finiteTateCoefficient l F n) sqZ ≫
        proClass l F n z' hI' hX' := by sorry

end AlgebraicGeometry.SupportedCartierDerivedPullback
