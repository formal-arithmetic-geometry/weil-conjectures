/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.PolynomialDualityRestrictionPrimitives

/-! # PolynomialDualityRestrictionAtlas

Source: Stacks duality.tex, 0E2X and 0BV2; dualizing.tex, 0BZI and 0BZJ.
(blueprint: def-trf-polynomial-duality-restriction-atlas).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry

/-- The structural morphism of the smooth ambient polynomial chart.
Source: Stacks 0BV2 (blueprint: def-trf-polynomial-duality-restriction-atlas). -/
def RelativeDualityPolynomialChart.base {X S : Scheme.{u}} {f : X ⟶ S}
    (C : RelativeDualityPolynomialChart f) : C.P ⟶ S :=
  C.ambient ≫ pullback.fst _ _

/-- The differential restriction is the universal-derivation map, followed by equality transport.
Source: Stacks 01UM (blueprint: def-trf-polynomial-duality-restriction-atlas). -/
def polynomialChartDifferentialRestriction {X S : Scheme.{u}} {f : X ⟶ S}
    (C D : RelativeDualityPolynomialChart f) (a : D.P ⟶ C.P) [IsOpenImmersion a]
    (h : a ≫ C.base = D.base) :
    (Scheme.Modules.restrictFunctor a).obj C.base.relativeDifferentials ⟶
      D.base.relativeDifferentials :=
  (C.base.relativeDifferentialsRestrictIso a).hom ≫
    ((a ≫ C.base).relativeDifferentialsCongr h).hom

/-- The coefficient restriction is fixed on every wedge of local differential sections.
This prevents a unit rescaling of the restriction comparison, also in rank zero.
Source: Stacks 0BZI, 0E2X (blueprint: def-trf-polynomial-duality-restriction-atlas). -/
def IsPolynomialChartCoefficientRestriction {X S : Scheme.{u}} {f : X ⟶ S}
    (C D : RelativeDualityPolynomialChart f) (a : D.P ⟶ C.P) [IsOpenImmersion a]
    (hn : C.n = D.n) (h : a ≫ C.base = D.base)
    (q : (Scheme.Modules.restrictFunctor a).obj
      (Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n) ≅
        Scheme.Modules.exteriorSheaf D.base.relativeDifferentials D.n) : Prop :=
  ∀ (V : D.P.Opens)
    (x : Fin C.n → C.base.relativeDifferentials.val.obj (op (a ''ᵁ V))),
    q.hom.val.app (op V)
      ((Scheme.Modules.restrictAppIso a
        (Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n) V).inv
          (Scheme.Modules.exteriorSheafSection C.base.relativeDifferentials C.n
            (a ''ᵁ V) x)) =
      Scheme.Modules.exteriorSheafSection D.base.relativeDifferentials D.n V
        (fun j ↦ (polynomialChartDifferentialRestriction C D a h).val.app (op V)
          ((Scheme.Modules.restrictAppIso a C.base.relativeDifferentials V).inv
            (x (Fin.cast hn.symm j))))

/-- The induced restriction of shifted top forms, with the standard shift comparisons.
Source: Stacks 0BZI, 0E2X (blueprint: def-trf-polynomial-duality-restriction-atlas). -/
@[irreducible] def polynomialChartCoefficientRestriction
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} {f : X ⟶ S} (C D : RelativeDualityPolynomialChart f)
    (a : D.P ⟶ C.P) [IsOpenImmersion a] (hn : C.n = D.n)
    (q : (Scheme.Modules.restrictFunctor a).obj
      (Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n) ≅
        Scheme.Modules.exteriorSheaf D.base.relativeDifferentials D.n) :
    (polynomialOpenRestriction a).obj C.coefficient ≅ D.coefficient :=
  by
  letI : HasDerivedCategory.{w} C.P.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings C.P.toRingedSpace)))
  letI : HasDerivedCategory.{w} D.P.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings D.P.toRingedSpace)))
  exact
    ((Scheme.Modules.restrictFunctor a).mapDerivedCategory.commShiftIso (C.n : ℤ)).app _ ≪≫
    (shiftFunctor _ (C.n : ℤ)).mapIso
      ((Functor.mapDerivedCategorySingleFunctor (Scheme.Modules.restrictFunctor a) 0).app
        (Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n)) ≪≫
    (shiftFunctor _ (C.n : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso q) ≪≫
    eqToIso (congrArg (fun n : ℕ ↦
      ((DerivedCategory.singleFunctor D.P.Modules 0).obj
        (Scheme.Modules.exteriorSheaf D.base.relativeDifferentials D.n))⟦(n : ℤ)⟧) hn)

/-- Restriction on the coinduced model, the mate of the actual evaluation counit.
The two ringed-space equations determine the direct-image-algebra restriction map.
Source: Stacks 0BUZ, 0E2X (blueprint: def-trf-polynomial-duality-restriction-atlas). -/
@[irreducible] def polynomialGeometricRestriction
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} {f : X ⟶ S} (C D : RelativeDualityPolynomialChart f)
    (dC : PolynomialChartExactData C.i) (dD : PolynomialChartExactData D.i)
    (a : D.P ⟶ C.P) [IsOpenImmersion a]
    (b : directImageAlgebraSpace D.i ⟶ directImageAlgebraSpace C.i)
    (hb : polynomialChartAlgebraMap D.i ≫ a.toLRSHom.toShHom =
      b ≫ polynomialChartAlgebraMap C.i)
    (F : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace C.i))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace D.i))))
    (adjF : F ⊣ RingedSpace.derivedModuleDirectImage b)
    (hn : C.n = D.n)
    (q : (Scheme.Modules.restrictFunctor a).obj
      (Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n) ≅
        Scheme.Modules.exteriorSheaf D.base.relativeDifferentials D.n)
    [IsIso (polynomialRestrictionExchange
      (polynomialOpenAdjunction a) adjF
      (polynomialImageSquare (polynomialChartAlgebraMap D.i) a.toLRSHom.toShHom
        b (polynomialChartAlgebraMap C.i) hb)
      ((polynomialChartDerivedHom C.i dC).obj C.coefficient))] :
    F.obj (C.model dC.additive) ⟶ D.model dD.additive :=
  polynomialCoinductionRestriction
      (polynomialOpenAdjunction a) adjF
      (polynomialChartDerivedAdjunction C.i dC) (polynomialChartDerivedAdjunction D.i dD)
      (polynomialImageSquare (polynomialChartAlgebraMap D.i) a.toLRSHom.toShHom
        b (polynomialChartAlgebraMap C.i) hb) C.coefficient ≫
    (polynomialChartDerivedHom D.i dD).map
      (polynomialChartCoefficientRestriction C D a hn q).hom

/-- The other side of the restriction square, the mate of restriction of the source complex.
It uses the same algebra pullback adjunction as the model comparison.
Source: Stacks 0E2X (blueprint: def-trf-polynomial-duality-restriction-atlas). -/
@[irreducible] def polynomialGeometricSourceRestriction
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} {f : X ⟶ S} (C D : RelativeDualityPolynomialChart f)
    (r : D.U.toScheme ⟶ C.U.toScheme) [IsOpenImmersion r]
    (hr : r ≫ C.U.ι = D.U.ι)
    (b : directImageAlgebraSpace D.i ⟶ directImageAlgebraSpace C.i)
    (hg : toDirectImageAlgebraSpace D.i ≫ b =
      r.toLRSHom.toShHom ≫ toDirectImageAlgebraSpace C.i)
    (F : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace C.i))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace D.i))))
    (adjF : F ⊣ RingedSpace.derivedModuleDirectImage b)
    (K : schemeDerivedCategory X) :
    F.obj ((RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace C.i)).obj
      ((polynomialOpenRestriction C.U.ι).obj K)) ⟶
      (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace D.i)).obj
        ((polynomialOpenRestriction D.U.ι).obj K) :=
  by
  letI : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  letI : HasDerivedCategory.{w} C.U.toScheme.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings C.U.toScheme.toRingedSpace)))
  letI : HasDerivedCategory.{w} D.U.toScheme.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings D.U.toScheme.toRingedSpace)))
  exact (adjF.homEquiv _ _).symm
    ((RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace C.i)).map
      ((polynomialOpenAdjunction r).unit.app
        ((polynomialOpenRestriction C.U.ι).obj K)) ≫
      (polynomialImageSquare (toDirectImageAlgebraSpace D.i) b
        r.toLRSHom.toShHom (toDirectImageAlgebraSpace C.i) hg).inv.app _) ≫
    (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace D.i)).map
      ((Functor.mapDerivedCategoryCompIso (Scheme.Modules.restrictFunctor C.U.ι)
        (Scheme.Modules.restrictFunctor r)).inv.app K ≫
      (Functor.mapDerivedCategoryNatIso
        ((Scheme.Modules.restrictFunctorComp r C.U.ι).symm ≪≫
          Scheme.Modules.restrictFunctorCongr hr)).hom.app K)

/-- A global family of chart identifications satisfying the independent canonical
restriction equation. The right side restricts K; the left side restricts the Hom
model by evaluation. Thus these are assertions, not definitions of free transitions.
Identity and composition follow from the unit-normalized direct-image squares and
from the exact open-restriction composition isomorphisms used on the right.
Source: Stacks 0E2X, 0BZI (blueprint: def-trf-polynomial-duality-restriction-atlas). -/
structure PolynomialDualityChartAtlas
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {X S : Scheme.{u}} (f : X ⟶ S) (K : schemeDerivedCategory X) where
  exactData : ∀ C : RelativeDualityPolynomialChart f, PolynomialChartExactData C.i
  identification : ∀ C : RelativeDualityPolynomialChart f,
    (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace C.i)).obj
      ((polynomialOpenRestriction C.U.ι).obj K) ≅ C.model (exactData C).additive
  restriction : ∀ (C D : RelativeDualityPolynomialChart f)
      (r : D.U.toScheme ⟶ C.U.toScheme) [IsOpenImmersion r]
      (a : D.P ⟶ C.P) [IsOpenImmersion a]
      (hr : r ≫ C.U.ι = D.U.ι)
      (b : directImageAlgebraSpace D.i ⟶ directImageAlgebraSpace C.i)
      (hb : polynomialChartAlgebraMap D.i ≫ a.toLRSHom.toShHom =
        b ≫ polynomialChartAlgebraMap C.i)
      (hg : toDirectImageAlgebraSpace D.i ≫ b =
        r.toLRSHom.toShHom ≫ toDirectImageAlgebraSpace C.i)
      (hn : C.n = D.n) (hp : a ≫ C.base = D.base)
      (q : (Scheme.Modules.restrictFunctor a).obj
        (Scheme.Modules.exteriorSheaf C.base.relativeDifferentials C.n) ≅
          Scheme.Modules.exteriorSheaf D.base.relativeDifferentials D.n),
    IsPolynomialChartCoefficientRestriction C D a hn hp q →
    ∀ (F : DerivedCategory
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace C.i))) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace D.i))))
      (adjF : F ⊣ RingedSpace.derivedModuleDirectImage b)
      [IsIso (polynomialRestrictionExchange
        (polynomialOpenAdjunction a) adjF
        (polynomialImageSquare (polynomialChartAlgebraMap D.i) a.toLRSHom.toShHom
          b (polynomialChartAlgebraMap C.i) hb)
        ((polynomialChartDerivedHom C.i (exactData C)).obj C.coefficient))],
      F.map (identification C).hom ≫
        polynomialGeometricRestriction C D (exactData C) (exactData D) a b hb F adjF hn q =
      polynomialGeometricSourceRestriction C D r hr b hg F adjF K ≫ (identification D).hom


end AlgebraicGeometry
