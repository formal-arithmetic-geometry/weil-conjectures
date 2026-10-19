/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Paper.DiagonalTowerLimit

/-! # The normalized completed diagonal arrow
Source: blueprint main-20261015, diagonal-limit clause 3 and trace proof step 11
(blueprint: def-sfb-diagonal-trace-limit-characterization).

## Main definitions
- `DiagonalTrace.rootLimitComparison` is the canonical preserved-limit comparison.
- `DiagonalTrace.IsDiagonalLimit` records the complete normalized limit characterization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w v a b c va vb vc wa wb wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The canonical comparison of a preserved limit with an isomorphic target diagram.
Source: blueprint trace proof step 5 and diagonal-limit clause 3
(blueprint: def-sfb-diagonal-trace-limit-characterization). -/
def rootLimitComparison
    {C : Type a} {D : Type b} {J : Type c}
    [Category.{va} C] [Category.{vb} D] [Category.{vc} J]
    (V : C ⥤ D) (H : J ⥤ C) (K : J ⥤ D)
    [HasLimit H] [HasLimit K] [PreservesLimit H V] (e : H ⋙ V ≅ K) :
    V.obj (limit H) ≅ limit K :=
  preservesLimitIso V H ≪≫ HasLimit.isoOfNatIso e

/-- A completed diagonal arrow with the full normalized presentation of the recorded
limit theorem: its finite Cartier system, coefficient cones, limit equation, completeness,
uniqueness and reduction comparisons. This specifies the whole-system map.
Source: blueprint trace clause 2 and diagonal-limit clause 3
(blueprint: def-sfb-diagonal-trace-limit-characterization). -/
def IsDiagonalLimit (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y) : Prop :=
  ∃ (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y) ∧
    c.hom = a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom ∧
    (∀ n : ℕ,
      ∃ (s : (D.ordinary.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
          (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
            ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
              (diagonalImmersion Y)).obj
                (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
        (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
          (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
            (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y))),
        DiagonalSourceNormalization ℓ Y D.ordinary n s ∧
        HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
          (roots.hom.app (op n) ≫
            cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
              (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
              (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)) ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
            (op n))).comp (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) =
          (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1) (diagonalImmersion Y)
            (diagonalImmersion_cartier Y) (diagonalSurface_power_unit ℓ Y hY n)).mapExactFunctor
               (diagonalFiniteToPadic ℓ n (diagonalSurface Y))) ∧
    ∃ (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (M : DiagonalCompletedReduction ℓ (diagonalSurface Y))
      (s₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (diagonalCompletedSource ℓ Y) ≅
        limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H),
      (∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y))) ∧
      HEq ((diagonalForget ℓ (diagonalSurface Y)).map t₀.hom)
        (rootLimitComparison (diagonalForget ℓ (diagonalSurface Y)) H
          (Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ
            (Fact.out : ℓ.Prime)) roots).inv ∧
      IsIso (diagonalSourceLimitMap ℓ Y D a L s₀) ∧
      IsIso (diagonalTargetLimitMap ℓ Y D H b L t₀) ∧
      (∀ P : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ diagonalCompletedDomain ℓ Y)) ∧
      (∀ P : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ diagonalCompletedCodomain ℓ Y)) ∧
      (((diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)) ∧
        (∀ δ' : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y,
          ((diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ' ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)) → δ' = δ)) ∧
      ∀ (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y),
        (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom) →
        ∀ n : ℕ,
          ∃ (s : (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
              ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).obj
                  (diagonalCompletedDomain ℓ Y)) ≅
              (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).obj
                (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))))
            (t : (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
              ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).obj
                  (diagonalCompletedCodomain ℓ Y)) ≅
              (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).obj
                (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
                  (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧))),
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.unit n).app (diagonalCompletedDomain ℓ Y)) ≫ s.hom =
              diagonalSourceLimitMap ℓ Y D a L s₀ ≫ (L.projection n).app
                (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))) ∧
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.unit n).app (diagonalCompletedCodomain ℓ Y)) ≫ t.hom =
              diagonalTargetLimitMap ℓ Y D H b L t₀ ≫ (L.projection n).app
                (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
                  (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) ∧
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                  (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).map
                    δ) =
              s.hom ≫ (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).map (D.T.map (diagonalIntegralBoundary Y).hom) ≫
                  t.inv


end AlgebraicGeometry.ProEtale.DiagonalTrace
