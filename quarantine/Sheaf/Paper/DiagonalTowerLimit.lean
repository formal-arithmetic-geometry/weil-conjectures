/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.DiagonalTowerSystem
public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.FormalClosedSupportIILimits
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.AdicCompletionReduction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# The completed diagonal class

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-limit.md, clauses 1--3; Stacks Tags 099L and 099I
(blueprint: det-prop-diagonal-tower-limit).

Strict towers have constant discrete Z_l coefficients. Only the final arrow has
coefficients in the completed ring sheaf. Positive exponent n+1 is indexed by n.

## Main statements

- `diagonalTower_limit`: completed endpoints and the unique completed diagonal arrow.
- `diagonalTower_directImage`: levelwise direct image and its canonical limit comparison.
- `diagonalCompletedTwist_limits`: exactness, products and inverse limits for both twists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v w a b
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The existing commutative-ring sheafification at the fixed coefficient universe.
Naming this specialization avoids an unresolved maximum in instance synthesis.
Source: blueprint completed coefficient convention, clause 3
(blueprint: det-prop-diagonal-tower-limit). -/
instance (priority := 2200) diagonalCompletedRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u} X

/-- Additivity of this specific limit functor, from its binary-product preservation.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-limit). -/
instance diagonalLimitAdditive (A : Type a) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- A total right derived functor with its universal unit and K-injective computation.
Source: blueprint clause 1, total derived functors on strict towers
(blueprint: det-prop-diagonal-tower-limit). -/
structure DiagonalRightDerived
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] where
  R : DerivedCategory A ⥤ DerivedCategory B
  η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R
  universal : R.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))
  computation : ∀ P : CochainComplex A ℤ, P.IsKInjective → IsIso (η.app P)
  [shift : R.CommShift ℤ]
  triangulated : R.IsTriangulated

attribute [instance] DiagonalRightDerived.shift

/-- The total derived limit, including its canonical projections to the derived levels.
The normalization is an equation on complexes and fixes the maps, not just their types.
Source: blueprint clauses 1 and 3, Stacks 0940
(blueprint: det-prop-diagonal-tower-limit). -/
structure DiagonalRlim
    (A : Type a) [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] extends
    DiagonalRightDerived (lim : (ℕᵒᵖ ⥤ A) ⥤ A) where
  projection : ∀ n : ℕ,
    R ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
  normalization : ∀ (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    η.app P ≫ (projection n).app (DerivedCategory.Q.obj P) ≫
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app P =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app P)

/-- Scalar forgetting preserves tower limits by the existing scalar adjunction.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-limit). -/
instance diagonalForgetTowerLimits (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (diagonalForget ℓ X) :=
  (diagonalScalarAdjunction ℓ X).rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- Modules over the existing completed coefficient sheaf.
Source: blueprint completed coefficient convention, clause 3
(blueprint: det-prop-diagonal-tower-limit). -/
abbrev DiagonalCompleted (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :=
  SheafOfModules.{u + 1} (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X ℓ))

/-- The existing abelian structure on completed coefficient modules, named once so
all derived expressions share its sheafification witnesses.
Source: blueprint completed coefficient convention, clause 3
(blueprint: det-prop-diagonal-tower-limit). -/
instance (priority := 2000) diagonalCompletedAbelian
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : Abelian (DiagonalCompleted ℓ X) :=
  inferInstance

/-- The n-th component of the canonical completed coefficient pullback map.
Source: blueprint clause 1, completed source coefficients
(blueprint: det-prop-diagonal-tower-limit). -/
def diagonalCompletedCoefficientComponent (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (Scheme.purTwistZlCompletion Y ℓ) ⟶ Scheme.purTwistFiniteRing X ℓ n :=
  (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (Scheme.purTwistZlProjection Y ℓ n) ≫
    Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))

/-- The finite components respect the prescribed quotient transitions.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-limit).
Proof: the limit projections commute with every tower arrow. The constant-sheaf
inverse-image comparison is natural in a ring homomorphism, because it is adjoint
to the constant-section map. Apply this naturality to each quotient transition;
functoriality of inverse image then gives the displayed cone equation. -/
theorem diagonalCompletedCoefficient_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) {b a : ℕᵒᵖ} (g : b ⟶ a) :
    diagonalCompletedCoefficientComponent ℓ f b.unop ≫
      (Scheme.purTwistZlTower X ℓ).map g =
        diagonalCompletedCoefficientComponent ℓ f a.unop := by
  sorry

/-- The canonical map from inverse-image to completed coefficients on the source.
Its actual data is the limit lift of the finite constant-section comparisons.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-limit). -/
def diagonalCompletedCoefficientMap (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion Y ℓ) ⟶ Scheme.purTwistZlCompletion X ℓ :=
  limit.lift (Scheme.purTwistZlTower X ℓ)
    { pt := (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (Scheme.purTwistZlCompletion Y ℓ)
      π := { app n := diagonalCompletedCoefficientComponent ℓ f n.unop
             naturality _ _ g := (Category.id_comp _).trans
               (diagonalCompletedCoefficient_naturality ℓ f g).symm } }

/-- The supported completed constant with its canonical completed-coefficient action.
Use the completed coefficient sheaf on the diagonal, restricted along the actual
coefficient structure map before ringed direct image.
Source: blueprint Delta_* Z_l in clauses 1 and 3
(blueprint: det-prop-diagonal-tower-limit). -/
def diagonalCompletedSource (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :
    DiagonalCompleted ℓ (diagonalSurface Y) :=
  (Scheme.proEtaleRingedDirectImage (diagonalImmersion Y)
    (Scheme.purTwistZlCompletion (diagonalSurface Y) ℓ)).obj
      ((SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (diagonalCompletedCoefficientMap ℓ (diagonalImmersion Y)))).obj
              (SheafOfModules.unit
                (Scheme.purTwistRing (ProjectiveLine Y)
                  (Scheme.purTwistZlCompletion (ProjectiveLine Y) ℓ))))

/-- Restrict the completed action to constant scalars, then to constant sections.
The two constant-ring presentations are identified by constantCommuteCompose.
Source: blueprint clause 3 and Stacks 099I
(blueprint: det-prop-diagonal-tower-limit). -/
def diagonalCompletedRestriction (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    DiagonalCompleted ℓ X ⥤ DiagonalMod ℓ X :=
  letI := Scheme.purTwistForgetPreservesSheafification X
  SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (Scheme.purTwistZlCompletionMap X ℓ)) ⋙
  SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).inv ⋙
  constantRingModuleRestriction.{u + 1, u} (Scheme.ProEt.topology X) (ULift.{u + 1} ℤ_[ℓ])

/-- Constant-scalar restriction is additive and exact.
Source: blueprint clause 3, coefficient comparison (blueprint: det-prop-diagonal-tower-limit).
Proof: all three factors retain the underlying additive sheaf. Kernels are sectionwise
and cokernels are additive sheafifications, so finite limits, finite colimits and sums
of morphisms are unchanged. The constant-ring equivalence extends the scalar action
uniquely by local gluing (lem-cbc-constant-ring-module-sheaves). -/
theorem diagonalCompletedRestriction_exact (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    (diagonalCompletedRestriction ℓ X).Additive ∧
    PreservesFiniteLimits (diagonalCompletedRestriction ℓ X) ∧
    PreservesFiniteColimits (diagonalCompletedRestriction ℓ X) := by
  sorry

/-- The additive part of coefficient restriction. Source: blueprint clause 3
(blueprint: det-prop-diagonal-tower-limit). -/
instance diagonalCompletedRestrictionAdditive (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    (diagonalCompletedRestriction ℓ X).Additive :=
  (diagonalCompletedRestriction_exact ℓ X).1

/-- The left exact part of coefficient restriction. Source: blueprint clause 3
(blueprint: det-prop-diagonal-tower-limit). -/
instance diagonalCompletedRestrictionLimits (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    PreservesFiniteLimits (diagonalCompletedRestriction ℓ X) :=
  (diagonalCompletedRestriction_exact ℓ X).2.1

/-- The right exact part of coefficient restriction. Source: blueprint clause 3
(blueprint: det-prop-diagonal-tower-limit). -/
instance diagonalCompletedRestrictionColimits (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    PreservesFiniteColimits (diagonalCompletedRestriction ℓ X) :=
  (diagonalCompletedRestriction_exact ℓ X).2.2

/-- Ordinary tensor with the signed completed Tate line.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-limit). -/
def diagonalCompletedSheafTwist (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (d : ℤ) :
    DiagonalCompleted ℓ X ⥤ DiagonalCompleted ℓ X :=
  SheafOfModules.siteSheafTensorRight
    (A := Scheme.purTwistZlCompletion X ℓ)
    (WeilConjectures.coefficientTwistLine X
      (R := Scheme.purTwistZlCompletion X ℓ) (Scheme.purTwistZlModule X ℓ) d)

/-- Tensor with the published signed Tate line, on objects and morphisms.
Source: blueprint clause 2; sk-def-sp-tate-twist, final formula
(blueprint: det-prop-diagonal-tower-limit). -/
def diagonalCompletedTwist (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ X)] (d : ℤ) :
    DerivedCategory (DiagonalCompleted ℓ X) ⥤ DerivedCategory (DiagonalCompleted ℓ X) :=
  (𝟭 _).prod' ((Functor.const _).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (WeilConjectures.coefficientTwistLine X
        (R := Scheme.purTwistZlCompletion X ℓ) (Scheme.purTwistZlModule X ℓ) d))) ⋙
  SheafOfModules.siteDerivedTensorIndependentCoefficients
    (Scheme.ProEt.topology X) (Scheme.purTwistZlCompletion X ℓ)

/-- Simultaneous derived quotient with its canonical quotient units on arbitrary inputs.
The normalization with the left-derived counit specifies the actual quotient map.
Source: blueprint clause 3, derived finite reductions; Stacks 099M
(blueprint: det-prop-diagonal-tower-limit). -/
structure DiagonalCompletedReduction (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ X)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ X)] where
  derived : DiagonalDerivedReduction ℓ (𝟭 (DiagonalCompleted ℓ X))
  unit : ∀ n : ℕ, 𝟭 (DerivedCategory (DiagonalCompleted ℓ X)) ⟶
    derived.T ⋙ ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ X)).obj (op n)).mapDerivedCategory
  normalization : ∀ (P : CochainComplex (DiagonalCompleted ℓ X) ℤ) (n : ℕ),
    (unit n).app (DerivedCategory.Q.obj P) ≫
      ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ X)).obj (op n)).mapDerivedCategory.map
        (derived.ε.app P) ≫
      ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ X)).obj (op n)).mapDerivedCategoryFactors.hom.app
        ((derived.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (derived.ordinary.π n) (.up ℤ)).app P)

/-- The degree-zero supported completed coefficient object.
Source: blueprint clauses 1 and 3 (blueprint: det-prop-diagonal-tower-limit). -/
abbrev diagonalCompletedDomain (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ (diagonalSurface Y))] :
    DerivedCategory.{w} (DiagonalCompleted ℓ (diagonalSurface Y)) :=
  (DerivedCategory.singleFunctor _ 0).obj (diagonalCompletedSource ℓ Y)

/-- The published completed Tate line shifted by two.
Source: blueprint clause 3 (blueprint: det-prop-diagonal-tower-limit). -/
abbrev diagonalCompletedCodomain (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ (diagonalSurface Y))] :
    DerivedCategory.{w} (DiagonalCompleted ℓ (diagonalSurface Y)) :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (Scheme.purTwistZlModule (diagonalSurface Y) ℓ))⟦(2 : ℤ)⟧

/-- Exact derived restriction from completed to constant coefficients.
Source: blueprint clause 3 (blueprint: det-prop-diagonal-tower-limit). -/
abbrev diagonalCompletedUnderlying (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ X)]
    [HasDerivedCategory.{w} (DiagonalMod ℓ X)] :=
  (diagonalCompletedRestriction ℓ X).mapDerivedCategory

/-- The ordinary limit cone maps to its total derived limit through the derived unit.
This is the canonical comparison with zero nullhomotopy on the Roos model.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-limit). -/
def diagonalOrdinaryRlim
    {A : Type a} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) (H : ℕᵒᵖ ⥤ A) :
    (DerivedCategory.singleFunctor A 0).obj (limit H) ⟶
      L.R.obj ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H) :=
  (DerivedCategory.singleFunctorIsoCompQ A 0).hom.app (limit H) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A) (.up ℤ) 0).inv.app H) ≫
    L.η.app ((HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0).obj H) ≫
    L.R.map ((DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ A) 0).inv.app H)

/-- The supported integral constant has a unique coefficient-unit map into the
supported completed constant. On every constant integer section it is n times one.
Source: blueprint clauses 1 and 3, completed source convention
(blueprint: det-prop-diagonal-tower-limit).
Proof: on the diagonal site send an integer n to n times one in the diagonal
completed ring. Ring restrictions preserve one and integer multiples, so these maps
form a presheaf morphism. The sheafification adjunction extends it uniquely from
the constant presheaf. Apply direct image along the diagonal. Every section of the
constant sheaf is locally a constant integer, so the displayed equations determine
the resulting additive sheaf map uniquely. -/
theorem diagonalCompletedGenerator_existsUnique (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :
    ∃! γ : diagonalIntegralSource Y ⟶
        (diagonalForget ℓ (diagonalSurface Y)).obj
          ((diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
            (diagonalCompletedSource ℓ Y)),
      ∀ (U : (diagonalSurface Y).ProEtᵒᵖ) (n : ℤ),
        HEq (γ.hom.app U
          ((toSheafify (Scheme.ProEt.topology (ProjectiveLine Y))
            ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                (op ((Scheme.proEtaleBaseChange (diagonalImmersion Y)).obj U.unop))
                  (ULift.up n)))
          (n • (1 : (Scheme.purTwistZlCompletion (ProjectiveLine Y) ℓ).obj.obj
            (op ((Scheme.proEtaleBaseChange (diagonalImmersion Y)).obj U.unop)))) := by
  sorry

/-- The unique coefficient-unit map, determined on locally constant integers.
Source: blueprint completed source convention
(blueprint: det-prop-diagonal-tower-limit). -/
def diagonalCompletedGenerator (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :=
  (diagonalCompletedGenerator_existsUnique ℓ Y).exists.choose

/-- The source endpoint identification induced by the ordinary limit comparison
and the already normalized derived source counit.
Source: blueprint clauses 1 and 3 (blueprint: det-prop-diagonal-tower-limit). -/
def diagonalSourceLimitMap (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y))) :
    (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj (diagonalCompletedDomain ℓ Y) ⟶
      L.R.obj (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))) :=
  ((diagonalCompletedRestriction ℓ (diagonalSurface Y)).mapDerivedCategorySingleFunctor 0).hom.app
      (diagonalCompletedSource ℓ Y) ≫
    (DerivedCategory.singleFunctor _ 0).map s.hom ≫
    diagonalOrdinaryRlim L (D.ordinary.E.obj (diagonalIntegralSource Y)) ≫
    L.R.map a.inv

/-- The target endpoint identification induced by the ordinary root limit,
the canonical shift comparison, and the existing signed Kummer identification.
Source: blueprint clauses 1 and 3 (blueprint: det-prop-diagonal-tower-limit). -/
def diagonalTargetLimitMap (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H) :
    (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj (diagonalCompletedCodomain ℓ Y) ⟶
      L.R.obj (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
        (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) :=
  ((diagonalCompletedUnderlying ℓ (diagonalSurface Y)).commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj (Scheme.purTwistZlModule (diagonalSurface Y) ℓ)) ≫
    (shiftFunctor _ (2 : ℤ)).map
      (((diagonalCompletedRestriction ℓ (diagonalSurface Y)).mapDerivedCategorySingleFunctor
          0).hom.app (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≫
        (DerivedCategory.singleFunctor _ 0).map t.hom ≫ diagonalOrdinaryRlim L H) ≫
    (L.R.commShiftIso (2 : ℤ)).inv.app ((DerivedCategory.singleFunctor _ 0).obj H) ≫
    L.R.map b.inv

/-- Both signed Tate twists are exact, preserve all products, and carry every
homotopy-limit triangle and its canonical comparison to a homotopy-limit triangle.
This expresses commutation with the total derived inverse limit, not just with limits
of degree-zero sheaves.

Source: blueprint clause 2, Stacks 099L
(blueprint: det-prop-diagonal-tower-limit).
Proof: the root limit is locally free of rank one over the completed ring by
lem-pur-twist-sheaf-locally-free; its dual has the dual trivializations. Tensor by
either line is locally the identity, so is exact on sheaves and preserves products.
The signed-line tensor is the functor of sk-def-sp-tate-twist. Derived tensor is
triangulated. Apply the tensor clause of det-formal-closed-support-ii-limits with
X=Z=S, identity immersions and empty complement. Products and fibers give the Roos
triangle of the tensor tower; the normalized comparison is an isomorphism. -/
theorem diagonalCompletedTwist_limits (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ X)]
    (d : ℤ) (hd : d = 1 ∨ d = -1) :
    (diagonalCompletedSheafTwist ℓ X d).Additive ∧
    PreservesFiniteLimits (diagonalCompletedSheafTwist ℓ X d) ∧
    PreservesFiniteColimits (diagonalCompletedSheafTwist ℓ X d) ∧
    (∃ (_ : (diagonalCompletedTwist ℓ X d).CommShift ℤ),
      CondensedRing.ClosedSupportLimitFunctorProperties (diagonalCompletedTwist ℓ X d)) := by
  sorry

/-- Derived direct image on the constant-coefficient tower category is levelwise and
commutes with the total derived limit, for morphisms of the pro-etale sites
in the standing finite-type, separated field setting.
The final equation retains the canonical projections of the comparison.

Source: blueprint clause 1, Stacks 0A07 and 0940
(blueprint: det-prop-diagonal-tower-limit).
Proof: the direct image is restriction along base change and commutes with ordinary
limits. Resolve strict towers by K-injective towers; evaluation preserves K-injectives,
so the evaluated derived direct image is Rf_* of the evaluated level. The constant
tower functor is exact and left adjoint to limit. The two composites are therefore
the same derived direct image on the tower site, by
lem-weil-ringed-tower-pushforward-limit-comparison and
lem-weil-pbc-ringed-strict-tower-homotopy-limit. Their common derived unit fixes the
comparison and naturality of the tower projections gives the displayed equation. -/
theorem diagonalTower_directImage (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ Y)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ Y)] :
    ∃ (LX : DiagonalRlim (DiagonalMod ℓ X)) (LY : DiagonalRlim (DiagonalMod ℓ Y))
      (Rf : DiagonalRightDerived (lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))
      (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ
        (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)))
      (e : ∀ n : ℕ, Rt.R ⋙
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ X)).obj (op n)).mapDerivedCategory ⋙ Rf.R)
      (c : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LY.R)
      (c₀ : (lim : DiagonalSystems ℓ X ⥤ DiagonalMod ℓ X) ⋙
          lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f ≅
        (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f) ⋙ lim),
      (∀ H : DiagonalSystems ℓ X,
        c₀.hom.app H = limit.post H
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)) ∧
      (∀ P : CochainComplex (DiagonalSystems ℓ X) ℤ,
        Rf.η.app (((lim : DiagonalSystems ℓ X ⥤ DiagonalMod ℓ X).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ Rf.R.map (LX.η.app P) ≫ c.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app P) ≫
          LY.η.app ((((Functor.whiskeringRight ℕᵒᵖ
            (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
              (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)).mapHomologicalComplex
                (.up ℤ)).obj P) ≫ LY.R.map (Rt.η.app P)) ∧
      (∀ (P : CochainComplex (DiagonalSystems ℓ X) ℤ), P.IsKInjective → ∀ n : ℕ,
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
          (e n).hom.app (DerivedCategory.Q.obj P) ≫
          Rf.R.map (((evaluation ℕᵒᵖ (DiagonalMod ℓ X)).obj
            (op n)).mapDerivedCategoryFactors.hom.app P) =
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
            (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫ Rf.η.app (P.asFunctor.obj (op n))) ∧
      ∀ (M : DerivedCategory (DiagonalSystems ℓ X)) (n : ℕ),
        c.hom.app M ≫ (LY.projection n).app (Rt.R.obj M) ≫ (e n).hom.app M =
          Rf.R.map ((LX.projection n).app M) := by
  sorry

/-- The completed diagonal class is the limit of the simultaneous reduction of the
positive Cartier boundary. Its endpoints are the supported completed constant and the
completed Tate line shifted by two. The unique lift is specified by its whole underlying
constant-coefficient morphism, not by a claim that individual reductions detect maps.
The reduction isomorphisms are normalized against the canonical limit projections and
the canonical derived quotient units.

Source: blueprint main-20261015, sk-prop-diagonal-tower-limit.md, clauses 1 and 3;
Stacks 099L, 099I and 099M (blueprint: det-prop-diagonal-tower-limit).

Proof:
1. Quotient transitions and the root power transitions are epimorphisms, the latter
by lem-pur-twist-sheaf-locally-free and invertibility of ell. det-pe-milnor-epimorphic
identifies derived and ordinary limits. The ordinary limits are the completed
coefficient sheaf and its Tate line, by det-prop-sfb-qlbar-colimit-x-integral-limit.
2. The diagonal is Cartier. Its complementary open is quasi-compact, since locally
it is the distinguished affine open D(t). lem-exc-proetale-closed-exact preserves
coefficient epimorphisms. Apply the same Milnor comparison to its direct-image
tower; direct image commutes with ordinary limits sectionwise. This gives the
supported completed constant. Clause 2 permits commuting the Tate line and shift.
3. det-prop-diagonal-tower-system identifies simultaneous reduction of the
integral source and G_m[1] with the supported finite constants and roots shifted
by two. Its completion formula identifies Rlim T(partial) with derived completion
of partial, with the intrinsic ell-completeness criterion.
4. lemma-weil-pbc-adic-completion-reduction identifies finite reduction of this
limit with evaluation at that level. The finite quotient has its two-term free
resolution. Naturality identifies the map, not merely the endpoints; its quotient
unit is adjoint to the tower projection. Thus the displayed finite arrow is the
torsion diagonal class with its positive Cartier/Kummer normalization.
5. lem-weil-pbc-constant-completion-equivalence identifies constant and completed
finite reductions and completion units. Both endpoints are derived complete.
Restriction from completed to constant coefficients is fully faithful on these
objects (sk-lem-integral-models, specialized to Q_l). Hence there is exactly one
completed-coefficient arrow inducing the whole constant-coefficient completion.
No assertion of uniqueness from separate finite reductions is used. -/
theorem diagonalTower_limit (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
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
        (preservesLimitIso (diagonalForget ℓ (diagonalSurface Y)) H ≪≫
          HasLimit.isoOfNatIso roots).inv ∧
      IsIso (diagonalSourceLimitMap ℓ Y D a L s₀) ∧
      IsIso (diagonalTargetLimitMap ℓ Y D H b L t₀) ∧
      (∀ P : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ diagonalCompletedDomain ℓ Y)) ∧
      (∀ P : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ diagonalCompletedCodomain ℓ Y)) ∧
      (∃! δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y,
        (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)) ∧
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
                  t.inv := by
  sorry

end AlgebraicGeometry.ProEtale
