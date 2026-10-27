/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseRealizationData

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-operations).
## Main definitions

* `Scalar` and `Restriction`: actual levelwise operations and fraction formulas.
* `Operations`: the identity, composition and scalar associator equations.
* `Mixed`: compatibility of the two operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace WeilConjectures.ClassicalRawLisse
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : PerAdic.Base D.k)

/-- Sheafification for the existing small coefficient rings, via the recorded
Grothendieck module structure and small etale site.
Source: Weil II (1.1.1) (blueprint: def-zl-classical-raw-lisse-operations). -/
local instance (priority := 100000) moduleSheafify (Y : Scheme.{u})
    (R : Type u) [CommRing R] :
    HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology (ModuleCat.{u + 1} R) Y).isRightAdjoint

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]

/-- Universe-general form of `CompletedLisse.finiteScalarUnit`: the actual tensor
unit followed by sheafification. Source: Weil II (1.1.1)d
(blueprint: def-zl-classical-raw-lisse-operations). -/
def finiteScalarUnit {Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat)).obj M ⟶
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat)).obj
        ((Sheaf.ringExtendScalars.{u, u + 1} Y.smallEtaleTopology φ).obj M) :=
  ⟨Functor.whiskerLeft M.obj (Functor.whiskerRight
      (ModuleCat.ringExtendScalarsAdj.{u, u + 1} φ).unit
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat)) ≫
    Functor.whiskerRight ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} B)).app
      (M.obj ⋙ ModuleCat.ringExtendScalars.{u, u + 1} φ))
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat)⟩

/-- The fixed site-comparison adjoint mate of a finite etale unit.
Source: BS 5.1.5 (blueprint: def-zl-classical-raw-lisse-operations). -/
def completionMate {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {N : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : M ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj N) :
    (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} Y).obj M ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        ((supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} X).obj N) :=
  (supportSiteProEtaleComparisonAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).inv.app M ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} X).map
        ((supportSiteEtaleComparisonAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ |>.symm η))

/-- Finite scalar extension retains finite free levels, with the actual balanced tensor.
The ramified source exponent is the ceiling prescribed in Weil II (1.1.1)d.
Every object below is comparison data in the theorem conclusion.
Source: BS 6.8.4(3),(4) (blueprint: def-zl-classical-raw-lisse-operations). -/
structure Scalar (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b) (i : E →ₐ[ℚ_[l]] F) where
  ramification : ℕ
  positive : 0 < ramification
  ideal : Ideal.map (integralScalarIntegerInclusion l E F i)
    (Padic.coefficientExtensionMaximalIdeal l E) =
      Padic.coefficientExtensionMaximalIdeal l F ^ ramification
  systems : Systems D l E W ⥤ Systems D l F W
  levels (m : ℕ) :
    systems ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
        (CategoryTheory.evaluation _ _).obj (op m) ≅
      ObjectProperty.ι (IsFree D l E W) ⋙
        ObjectProperty.ι (IsLisseIntegralDiagramOfUniverses l E W.scheme) ⋙
        (CategoryTheory.evaluation _ _).obj (op ((m + ramification) / ramification - 1)) ⋙
          Sheaf.ringExtendScalars.{u, u + 1} W.scheme.smallEtaleTopology
            ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (m + 1))).comp
              (integralScalarIntegerInclusion l E F i)) ⋙
            sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
              (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (m + 1))))
  unit (M : Systems D l E W) (m : ℕ) :
    (etaleTower D l E W M).obj (op ((m + ramification) / ramification - 1)) ⟶
      (etaleTower D l F W (systems.obj M)).obj (op m)
  unit_tensor (M : Systems D l E W) (m : ℕ) :
    HEq (unit M m)
      (finiteScalarUnit
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (m + 1))).comp
          (integralScalarIntegerInclusion l E F i))
        (M.obj.obj.obj (op ((m + ramification) / ramification - 1))) ≫
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1}
        (Padic.coefficientExtensionIntegers l F)) AddCommGrpCat)).map
          ((levels m).inv.app M))
  transitions (M : Systems D l E W) (m n : ℕ) (h : m ≤ n)
      (hs : (m + ramification) / ramification - 1 ≤
        (n + ramification) / ramification - 1) :
    unit M n ≫ (etaleTower D l F W (systems.obj M)).map (homOfLE h).op =
      (etaleTower D l E W M).map (homOfLE hs).op ≫ unit M m
  integralUnit (M : Systems D l E W) :
    (forgetLattice l E W.scheme).obj ((s.integral E W).equivalence.inverse.obj M).obj ⟶
      (forgetLattice l F W.scheme).obj
        ((s.integral F W).equivalence.inverse.obj (systems.obj M)).obj
  completion_projection (M : Systems D l E W) (m : ℕ) :
    integralUnit M ≫ ((s.integral F W).completion (systems.obj M)).app (op m) =
      ((s.integral E W).completion M).app
          (op ((m + ramification) / ramification - 1)) ≫
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} W.scheme).map
          (unit M m)
  raw : Rational D l E W ⥤ Rational D l F W
  additive : raw.Additive
  objects (M : Rational D l E W) : raw.obj M = ⟨systems.obj M.obj⟩
  fraction (M N : Rational D l E W) (z : Localization.Away
      (Padic.coefficientExtensionUniformizer l E)) (f : M.obj ⟶ N.obj) :
    HEq (raw.map (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
      ((sfRationalCoefficientEquiv l F).symm (i (sfRationalCoefficientEquiv l E z))
        ⊗ₜ[Padic.coefficientExtensionIntegers l F] systems.map f)
  comparison : (s.raw E W).raw ⋙ (sfRationalHeartProperty l E W.scheme).ι ⋙
      sfRationalScalarExtension l E W.scheme D.p hl F i ≅
    raw ⋙ (s.raw F W).raw ⋙ (sfRationalHeartProperty l F W.scheme).ι
  ordinary : (s.finite E W).modules ⋙
      pbcExtend (a.fieldChange E F i (realizationBase D l hl W)).coefficient ≅
    raw ⋙ (s.finite F W).modules
  ordinary_tensor (M : Rational D l E W) (U : W.scheme.ProEt)
      (x : ((s.integral E W).equivalence.inverse.obj M.obj).obj.val.obj (op U)) :
    HEq (((s.finite F W).objects (raw.obj M)).hom.val.app (op U)
      ((ordinary.hom.app M).val.app (op U)
        (pbcTensorSection (a.fieldChange E F i (realizationBase D l hl W)).coefficient
          ((s.finite E W).modules.obj M) (op U) 1
          (((s.finite E W).objects M).inv.val.app (op U)
            (pbcTensorSection (LisseRealization.scalar D l hl E
              (a.realization E (realizationBase D l hl W)))
              ((s.integral E W).equivalence.inverse.obj M.obj).obj (op U) 1 x)))))
    (pbcTensorSection (LisseRealization.scalar D l hl F
      (a.realization F (realizationBase D l hl W)))
      ((s.integral F W).equivalence.inverse.obj (systems.obj M.obj)).obj (op U) 1
      ((integralUnit M.obj).hom.app (op U) x))
  normalization (M : Rational D l E W) :
    HEq (((a.realization F (realizationBase D l hl W)).sheaf D l hl F).map
        (comparison.hom.app M) ≫ (s.finite F W).comparison.hom.app (raw.obj M))
      (((a.fieldChange E F i (realizationBase D l hl W)).comparison
        ((s.raw E W).raw.obj M).obj ((s.finite E W).lisse M)).hom ≫
      (pbcExtend (a.fieldChange E F i (realizationBase D l hl W)).coefficient).map
        ((s.finite E W).comparison.hom.app M) ≫ ordinary.hom.app M)

  fibre (x : Spec (.of D.k) ⟶ W.scheme) (M : Rational D l E W) :
    (ModuleCat.extendScalars.{u, u, u + 1} i.toRingHom).obj
      (classicalFibre D l E W M.obj x) ≅
        classicalFibre D l F W (raw.obj M).obj x

/-- Locally closed restriction uses inverse image of the actual finite etale levels.
Its module square fixes the comparison on pulled-back basis sections.
Source: BS 6.8.4(1), 6.8.15
(blueprint: def-zl-classical-raw-lisse-operations). -/
structure Restriction (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f] where
  systems : Systems D l E W ⥤ Systems D l E V
  levels (n : ℕ) :
    systems ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
        (CategoryTheory.evaluation _ _).obj (op n) ≅
      ObjectProperty.ι (IsFree D l E W) ⋙
        ObjectProperty.ι (IsLisseIntegralDiagramOfUniverses l E W.scheme) ⋙
        (CategoryTheory.evaluation _ _).obj (op n) ⋙
          supportSiteEtaleComparisonPullback
            (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) f
  unit (M : Systems D l E W) (n : ℕ) :
    (etaleTower D l E W M).obj (op n) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj
        ((etaleTower D l E V (systems.obj M)).obj (op n))
  unit_pullback (M : Systems D l E W) (n : ℕ) :
    unit M n =
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1}
        (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)).map
        ((supportSiteEtaleComparisonAdjunction
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) f).unit.app
            (M.obj.obj.obj (op n))) ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)).map
            ((levels n).inv.app M))
  transitions (M : Systems D l E W) (m n : ℕ) (h : m ≤ n) :
    unit M n ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
        ((etaleTower D l E V (systems.obj M)).map (homOfLE h).op) =
      (etaleTower D l E W M).map (homOfLE h).op ≫ unit M m
  integralUnit (M : Systems D l E W) :
    (forgetLattice l E W.scheme).obj ((s.integral E W).equivalence.inverse.obj M).obj ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        ((forgetLattice l E V.scheme).obj
          ((s.integral E V).equivalence.inverse.obj (systems.obj M)).obj)
  completion_projection (M : Systems D l E W) (n : ℕ) :
    integralUnit M ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
        (((s.integral E V).completion (systems.obj M)).app (op n)) =
      ((s.integral E W).completion M).app (op n) ≫ completionMate f (unit M n)
  raw : Rational D l E W ⥤ Rational D l E V
  additive : raw.Additive
  objects (M : Rational D l E W) : raw.obj M = ⟨systems.obj M.obj⟩
  fraction (M N : Rational D l E W) (z : Localization.Away
      (Padic.coefficientExtensionUniformizer l E)) (g : M.obj ⟶ N.obj) :
    HEq (raw.map (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] g))
      (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] systems.map g)
  comparison : (s.raw E W).raw ⋙ (sfRationalHeartProperty l E W.scheme).ι ⋙
      @rationalDerivedPullback l _ E _ _ _ V.scheme W.scheme f
        (baseInvertible D l hl V) (baseInvertible D l hl W) ≅
    raw ⋙ (s.raw E V).raw ⋙ (sfRationalHeartProperty l E V.scheme).ι
  ordinary : (s.finite E W).modules ⋙ LisseRealization.ordinaryPull l E f ≅
    raw ⋙ (s.finite E V).modules
  ordinary_tensor (M : Rational D l E W) (U : W.scheme.ProEt)
      (x : ((s.integral E W).equivalence.inverse.obj M.obj).obj.val.obj (op U)) :
    HEq
      (((s.finite E V).objects (raw.obj M)).hom.val.app
        (op ((proEtaleBaseChange f).obj U))
        ((ordinary.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
          (ContinuousRational.moduleUnit f (LisseRealization.coefficientPull l E f)
            ((s.finite E W).modules.obj M) U
            (((s.finite E W).objects M).inv.val.app (op U)
              (pbcTensorSection (LisseRealization.scalar D l hl E
                (a.realization E (realizationBase D l hl W)))
                ((s.integral E W).equivalence.inverse.obj M.obj).obj (op U) 1 x)))))
      (pbcTensorSection (LisseRealization.scalar D l hl E
        (a.realization E (realizationBase D l hl V)))
        ((s.integral E V).equivalence.inverse.obj (systems.obj M.obj)).obj
        (op ((proEtaleBaseChange f).obj U)) 1
        ((integralUnit M.obj).hom.app (op U) x))
  normalization (M : Rational D l E W) :
    HEq (((a.realization E (realizationBase D l hl V)).sheaf D l hl E).map
        (comparison.hom.app M) ≫ (s.finite E V).comparison.hom.app (raw.obj M))
      (((a.along E (X := realizationBase D l hl V)
        (Y := realizationBase D l hl W) f).comparison ((s.raw E W).raw.obj M).obj
        ((s.finite E W).lisse M)).hom ≫
      (LisseRealization.ordinaryPull l E f).map
        (X := ((a.realization E (realizationBase D l hl W)).sheaf D l hl E).obj
          ((s.raw E W).raw.obj M).obj)
        (Y := (s.finite E W).modules.obj M)
        ((s.finite E W).comparison.hom.app M) ≫ ordinary.hom.app M)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Simultaneous normalized operations and their identity and composition equations.
All fields occur as conclusions in the realization theorem.
Source: BS 6.8.4, 6.8.15 (blueprint: def-zl-classical-raw-lisse-operations). -/
structure Operations (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b) where
  scalar : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (X : PerAdic.Base D.k) (i : A →ₐ[ℚ_[l]] B), Scalar D l hl A X B a b s i
  restriction : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X Y : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) [IsImmersion f], Restriction D l hl A X a b s Y f

end WeilConjectures.ClassicalRawLisse
