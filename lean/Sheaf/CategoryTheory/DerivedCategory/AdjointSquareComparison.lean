/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Comparison of derived adjoint squares

Source: Stacks Project, Derived Categories, Tags 09T5, 0DVC and 0FND; the compatible-square
calculation from their canonical Hom formula
(blueprint: lem-kun-derived-adjoint-square-comparison).
-/

@[expose] public section

universe uA uB uA0 uB0 vA vB vA0 vB0 wA wB wA0 wB0

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- A compatible square of additive adjunctions with exact left and vertical functors
induces a compatible square of canonical derived adjunctions. Source: Stacks Project,
Derived Categories, Tags 09T5, 0DVC and 0FND, and the square calculation from their Hom formula
(blueprint: lem-kun-derived-adjoint-square-comparison).

The hypotheses `hcan` and `hcan0` specify the canonical derived adjunctions through the
localized Hom formula of `exists_derived_adjunction_of_essentially_constant`, written on
complexes. The hypotheses `haD` and `hb` spell out the exact-functor localization
identifications in the termwise comparison and the right-derived comparison. The
postcomposition hypothesis is the right-derived universal property with its localized unit.

Proof:
1. Apply the identity-fraction Hom formula of `preDerivedAdjunctionGeneral` to the termwise
underived unit and identity denominators. The triangle identity identifies its adjunct
with the identity; hence the derived unit is the localized underived unit followed by
`γ`. Exactness identifies the left derived comparison with `mapDerivedCategoryFactors`,
by `exactFunctor_derivedFunctor`. Repeat for the second adjunction.
2. Specialize `hc` to the identity of `L.obj M`. It identifies the underived units through
`a.inv` and `c.hom`. Apply this degreewise, localize, and use `hb` and naturality of `γ0`
for the complex isomorphism induced by `a.inv`. Step 1 gives the derived-unit equation
on every localized complex, with precisely the identifications in `haD`.
3. Both sides are natural transformations. `Localization.natTrans_ext` extends the
unit equality from localized complexes to all objects of the derived category.
4. Express each adjunct as the unit followed by the right adjoint applied to the map.
The unit equation and naturality of `b` give the asserted equality for every `t`.
5. Specialize to the counit. Its adjunct is the identity by the triangle identity;
transpose back through the second adjunction to obtain the counit equation. Conversely,
specializing the adjunct identity to an identity recovers the unit equation. -/
theorem derived_adjoint_square_comparison
    {A : Type uA} {B : Type uB} {A0 : Type uA0} {B0 : Type uB0}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA0} A0] [Category.{vB0} B0]
    [Abelian A] [Abelian B] [Abelian A0] [Abelian B0]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wA0} A0] [HasDerivedCategory.{wB0} B0]
    (L : B ⥤ A) (R : A ⥤ B) (L0 : B0 ⥤ A0) (R0 : A0 ⥤ B0)
    [L.Additive] [R.Additive] [L0.Additive] [R0.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L0] [PreservesFiniteColimits L0]
    (adj : L ⊣ R) (adj0 : L0 ⊣ R0)
    (V : A ⥤ A0) (W : B ⥤ B0) [V.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (a : L ⋙ V ≅ W ⋙ L0) (c : R ⋙ W ≅ V ⋙ R0)
    (hc : ∀ (M : B) (N : A) (t : L.obj M ⟶ N),
      adj0.homEquiv (W.obj M) (V.obj N) (a.inv.app M ≫ V.map t) =
        W.map (adj.homEquiv M N t) ≫ c.hom.app N)
    (RR : DerivedCategory A ⥤ DerivedCategory B)
    (RR0 : DerivedCategory A0 ⥤ DerivedCategory B0)
    (γ : R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RR)
    (γ0 : R0.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RR0)
    [RR.IsRightDerivedFunctor γ (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    [RR0.IsRightDerivedFunctor γ0 (HomologicalComplex.quasiIso A0 (ComplexShape.up ℤ))]
    (hR : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ X : DerivedCategory B,
        IsEssentiallyConstantIndDiagram
          (MorphismProperty.Under.forget
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ K ⋙ Under.forget K ⋙
            R.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) X)
    (hR0 : ∀ K : HomotopyCategory A0 (ComplexShape.up ℤ),
      ∃ X : DerivedCategory B0,
        IsEssentiallyConstantIndDiagram
          (MorphismProperty.Under.forget
            (HomotopyCategory.quasiIso A0 (ComplexShape.up ℤ)) ⊤ K ⋙ Under.forget K ⋙
            R0.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) X)
    (d : L.mapDerivedCategory ⊣ RR) (d0 : L0.mapDerivedCategory ⊣ RR0)
    (hcan : ∀ (M : CochainComplex B ℤ) (P : CochainComplex A ℤ)
      (f : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ P),
      d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj P)
          (L.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv M P f)
          ≫ γ.app P)
    (hcan0 : ∀ (M : CochainComplex B0 ℤ) (P : CochainComplex A0 ℤ)
      (f : (L0.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ P),
      d0.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj P)
          (L0.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj0.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv M P f)
          ≫ γ0.app P)
    [(RR ⋙ W.mapDerivedCategory).IsRightDerivedFunctor
      ((Functor.isoWhiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          W.mapDerivedCategoryFactors.symm).hom ≫
        Functor.whiskerRight γ W.mapDerivedCategory ≫
        (Functor.associator DerivedCategory.Q RR W.mapDerivedCategory).hom)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (b : RR ⋙ W.mapDerivedCategory ⟶ V.mapDerivedCategory ⋙ RR0)
    (hb : ∀ P : CochainComplex A ℤ,
      W.mapDerivedCategoryFactors.inv.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        W.mapDerivedCategory.map (γ.app P) ≫ b.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((c.hom.mapHomologicalComplex (ComplexShape.up ℤ)).app P) ≫
        γ0.app ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        RR0.map (V.mapDerivedCategoryFactors.inv.app P))
    (aD : L.mapDerivedCategory ⋙ V.mapDerivedCategory ≅
      W.mapDerivedCategory ⋙ L0.mapDerivedCategory)
    (haD : ∀ X : CochainComplex B ℤ,
      aD.hom.app (DerivedCategory.Q.obj X) ≫
        L0.mapDerivedCategory.map (W.mapDerivedCategoryFactors.hom.app X) ≫
        L0.mapDerivedCategoryFactors.hom.app
          ((W.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) =
      V.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app X) ≫
        V.mapDerivedCategoryFactors.hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((a.hom.mapHomologicalComplex (ComplexShape.up ℤ)).app X)) :
    (∀ (M : DerivedCategory B) (N : DerivedCategory A)
      (t : L.mapDerivedCategory.obj M ⟶ N),
      d0.homEquiv (W.mapDerivedCategory.obj M) (V.mapDerivedCategory.obj N)
          (aD.inv.app M ≫ V.mapDerivedCategory.map t) =
        W.mapDerivedCategory.map (d.homEquiv M N t) ≫ b.app N) ∧
    (∀ M : DerivedCategory B,
      W.mapDerivedCategory.map (d.unit.app M) ≫ b.app (L.mapDerivedCategory.obj M) =
        d0.unit.app (W.mapDerivedCategory.obj M) ≫ RR0.map (aD.inv.app M)) ∧
    (∀ N : DerivedCategory A,
      V.mapDerivedCategory.map (d.counit.app N) =
        aD.hom.app (RR.obj N) ≫ L0.mapDerivedCategory.map (b.app N) ≫
          d0.counit.app (V.mapDerivedCategory.obj N)) := by
  sorry

end CategoryTheory.Adjunction
