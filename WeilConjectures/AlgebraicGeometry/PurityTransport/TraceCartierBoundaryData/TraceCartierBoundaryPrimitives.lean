/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasicDefs
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal

/-! # Integral Kummer boundary primitives

The integral tower, normalized class, and closed-support comparison needed for
native trace Cartier families. No compact-support exchange theorem is used.
Source: relative Kummer boundary construction, smooth trace properties (2).
(blueprint: new-det-sp-trace-cartier-boundary-primitives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.PurityTransport.TraceCartierBoundaryData

variable (ell : ℕ) [Fact ell.Prime]

/-- The integral Kummer limit, with both maps specified on every finite projection.
Source: the integral-limit construction in Steps 1 and 3 of the rank-one Thom proof
(blueprint: new-det-sp-trace-cartier-boundary-primitives). -/
structure IntegralKummer (T : Scheme.{u}) where
  level : ∀ n : ℕ, (tateModuleLevel T ell (n + 1)).X ≅
    Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1))
  level_normalized : ∀ n : ℕ,
    (level n).inv = (rootComparison T (ell ^ (n + 1))).inv ≫
      (λ_ (rootsOfUnitySheaf T (ell ^ (n + 1)))).inv ≫
      η[condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) T] ▷ _
  inclusion : (tateModule T ell).X ⟶ limit (SpTowerClasses.powerUnits ell T)
  inclusion_normalized : ∀ n : ℕ,
    inclusion ≫ limit.π (SpTowerClasses.powerUnits ell T) (op n) =
      (limit.π (tateModuleSystem T ell) (op (n + 1))).hom ≫ (level n).hom ≫
        Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))
  projection : limit (SpTowerClasses.powerUnits ell T) ⟶ Scheme.proEtaleUnitsSheaf T
  projection_normalized : projection =
    limit.π (SpTowerClasses.powerUnits ell T) (op 0) ≫ Scheme.proEtaleUnitsPower T ell
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact

/-- The integral supported constant on the pro-etale site, already used by the
Cartier boundary. Source: the relative frame extension in Step 1
(blueprint: new-det-sp-trace-cartier-boundary-primitives). -/
abbrev integralConstant (X : Scheme.{u}) :=
  (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The coefficient unit sends the integral section one to the ring section one.
Source: the scalar extension in Step 3
(blueprint: new-det-sp-trace-cartier-boundary-primitives). -/
def generator (c : Coefficient ell) (X : Scheme.{u}) :
    integralConstant X ⟶ condensedRingObj (c.obj ell) X :=
  (Functor.Monoidal.εIso (constantSheaf (ProEt.topology X) Ab.{u + 1})).inv ≫ η

/-- The supported unit, before deriving. Source: the source of c_D in Step 1
(blueprint: new-det-sp-trace-cartier-boundary-primitives). -/
abbrev sourceModule (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T) :=
  (CondensedRing.lowerStar (c.obj ell) i).obj (c.line ell D 0)

/-- Degree-two module Ext is the canonical single-to-shifted-single derived Hom.
Source: the displayed supported Cartier arrow in Step 1
(blueprint: new-det-sp-trace-cartier-boundary-primitives). -/
abbrev Class (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T) :=
  Ext (sourceModule ell c i) (c.line ell T 1) 2

/-- The actual scalar insertion into the shifted Tate line. Source: Step 3
(blueprint: new-det-sp-trace-cartier-boundary-primitives). -/
def rootInsertion (c : Coefficient ell) (T : Scheme.{u}) :
    (tateModule T ell).X ⟶ (c.line ell T 1).X :=
  (Mod.extendUnit (coefficientMap (c.integralMap ell) T) (tateModule T ell)).hom ≫
    (λ_ (c.firstLine ell T)).inv.hom

/-- Full-boundary normalization: the pole extension followed by the positive
integral Kummer boundary, with the canonical scalar insertion. This fixes the
local sign -∂κ(f) without choosing local lifts or testing only finite reductions.
Source: Steps 1 and 3 and lem-pur-divisor-class
(blueprint: new-det-sp-trace-cartier-boundary-primitives). -/
def Normalized {T D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (K : IntegralKummer ell T)
    (c : Coefficient ell) (a : Class ell c i) : Prop :=
  cartierScalarBoundaryEquation (Mod.forget (condensedRingObj (c.obj ell) T))
    ((ProEtale.lowerStar Ab.{u + 1} i).map (generator ell c D)) a
    (cartierProBoundary i (Etale.cartierPoleBoundary i hI))
    (cartierKummerClass K.exact (rootInsertion ell c T))

/-- Underived closed direct image into total direct image, fixed as the
adjunct of the ordinary closed counit under the exact inverse-image comparison.
Source: composition normalization, Step 3
(blueprint: new-det-sp-trace-cartier-boundary-primitives). -/
def closedSingleMap (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T) :
    (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i) ⟶
      (actualPush (c.obj ell) i).obj (unit ell c D) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj ell) i).homEquiv _ _ <|
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) i).hom.app _ ≫
      ((CondensedRing.upperStar (c.obj ell) i).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((CondensedRing.upperStarLowerStarAdjunction (c.obj ell) i).counit.app (c.line ell D 0))


end AlgebraicGeometry.ProEtale.PurityTransport.TraceCartierBoundaryData
