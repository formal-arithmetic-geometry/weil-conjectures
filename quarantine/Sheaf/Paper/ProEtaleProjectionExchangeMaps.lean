/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.RationalLocalizingProjectionFormula
public import Sheaf.Paper.TraceBaseChangeFirst
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.CategoryTheory.Adjunction.Mates


/-!
# Canonical projection and exchange maps on internal pro-etale modules

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-line.proof.md`, (1), second triangle
(blueprint: def-sfb-proetale-projection-exchange-maps).

The tensor comparison is the existing representative-normalized comparison on internal
module objects. Projection and base change are its actual adjunction mates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u uA vA wA uB u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open scoped CategoryTheory.Functor

namespace CategoryTheory

/-- The actual Koszul braiding, as a generic derived-category shortcut.
Source: Stacks 07A4 (blueprint: def-sfb-proetale-projection-exchange-maps). -/
def traceDerivedBraiding {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{wA} A] [HasDerivedCategory.{wA} A]
    [MonoidalCategory A] [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
    [HasColimitsOfSize.{0, 0} A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory A) : K ⊗ L ≅ L ⊗ K :=
  DerivedMonoidal.braiding' (DerivedCategory.Qh (C := A))
    (HomotopyCategory.quasiIso A (.up ℤ)) K L

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual internal module category. Source: blueprint (1), second triangle
(blueprint: def-sfb-proetale-projection-exchange-maps). -/
abbrev TraceModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The actual unbounded derived category. Source: blueprint (1), second triangle
(blueprint: def-sfb-proetale-projection-exchange-maps). -/
abbrev TraceDerived (X : Scheme.{u}) := DerivedCategory (TraceModules Λ X)

/-- The recorded relative derived tensor, in uncurried notation.
Source: blueprint (1) (blueprint: def-sfb-proetale-projection-exchange-maps). -/
abbrev traceTensor (X : Scheme.{u}) : TraceDerived Λ X × TraceDerived Λ X ⥤ TraceDerived Λ X :=
  Functor.uncurry.obj (derivedTensor Λ X)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The signed braiding descended from the actual tensor on complexes.
Source: Stacks 07A4 (blueprint: def-sfb-proetale-projection-exchange-maps). -/
def traceBraiding (Z : Scheme.{u}) (K L : TraceDerived Λ Z) : K ⊗ L ≅ L ⊗ K :=
  traceDerivedBraiding K L

/-- The existing comparison in its original curried interface; its total-complex
formula fixes every component. Source: Stacks 07A4, 0B56
(blueprint: def-sfb-proetale-projection-exchange-maps). -/
def traceTensorComparison :
    (Functor.postcompose₂.obj (tracePull Λ f)).obj (derivedTensor Λ Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (tracePull Λ f)).obj (tracePull Λ f)).obj
        (derivedTensor Λ X) :=
  letI : IsIso (moduleObjectDerivedTensorComparison Λ f) :=
    (existsUnique_moduleObjectDerivedTensorComparison Λ f).exists.choose_spec.2
  asIso (moduleObjectDerivedTensorComparison Λ f)

/-- Left-factor projection from the recorded counit mate and the two signed symmetries.
Source: Stacks 0B56 (blueprint: def-sfb-proetale-projection-exchange-maps). -/
def traceProjection (K : TraceDerived Λ Y) (N : TraceDerived Λ X) :
    K ⊗ (tracePush Λ f).obj N ⟶
      (tracePush Λ f).obj
        ((tracePull Λ f).obj K ⊗ N) :=
  (traceBraiding Λ Y _ _).hom ≫
    moduleObjectProjectionMate Λ f N K ≫
    (tracePush Λ f).map (traceBraiding Λ X _ _).hom

variable {W : Scheme.{u}} (p₁ p₂ : W ⟶ X) (sq : CommSq p₁ p₂ f f)

/-- The comparison for fp1=fp2, built from the existing derived pullback composition maps.
Source: Stacks 0D6D (blueprint: def-sfb-proetale-projection-exchange-maps). -/
def traceSquarePullback :
    (tracePull Λ f) ⋙ (tracePull Λ p₂) ≅
      (tracePull Λ f) ⋙ (tracePull Λ p₁) :=
  (leftDerivedUpperStarComp Λ p₂ f).symm ≪≫
    eqToIso (congrArg (fun h ↦ tracePull Λ h) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ p₁ f

/-- Canonical base-change mate b2; interchanging p1,p2 gives b1.
Source: Stacks 07A7 and the recorded mate correspondence
(blueprint: def-sfb-proetale-projection-exchange-maps). -/
def traceBaseChange :
    (tracePush Λ f) ⋙ (tracePull Λ f) ⟶
      (tracePull Λ p₁) ⋙ (tracePush Λ p₂) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ p₂)
    (TwoSquare.mk _ _ _ _ (traceSquarePullback Λ f p₁ p₂ sq).hom)).natTrans


end AlgebraicGeometry.ProEtale.CondensedRing
