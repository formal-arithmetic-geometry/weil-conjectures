/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteReductionRootCharts
public import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit
public import Sheaf.Paper.SmoothTrace
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

/-! # Reduction of the canonical finite-coefficient purity maps

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
def-pur-finite-reduction-comparisons (blueprint: def-pur-finite-reduction-comparisons).

## Main definitions

- `finiteReductionSourceComparison`: the root-normalized source comparison.
- `finiteReductionCompactSupportComparison`: the scalar-adjunction support mate.
- `finiteReductionExceptionalComparison`: the counit-normalized exceptional mate.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
/-- The exact-derived compositor for the ordinary realization transport.
The additive structures are the published realization's canonical structures.
Source: Stacks 00YV and blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionPullbackPresentationNative (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.sfIntrinsicDerivedPullback P.Ring f ≅ P.finiteReductionPullback f :=
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  Functor.mapDerivedCategoryCompIso
          ((Scheme.sfIntrinsicModuleEquivalence Y P.Ring).inverse ⋙
            ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)
          (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor ≪≫
        Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryCompIso
            (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).inverse
            (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f))
          (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor.mapDerivedCategory

/-- The realization expression for inverse image equals the exact-derived ordinary
transport. The equality is an interface proof, not chosen morphism data.
Source: Stacks 00YV and blueprint Step 1
(blueprint: def-pur-finite-reduction-comparisons).
Proof: unfold the ordinary transported inverse image. The exact-derived compositor
applied twice gives precisely the derived realization functors and fixed inverse image.
The derived equivalence is the mapped ordinary equivalence, so the endpoints coincide. -/
theorem finiteReductionPullbackPresentation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : Scheme.sfIntrinsicDerivedPullback P.Ring f ≅ P.finiteReductionPullback f,
      HEq e
        (P.finiteReductionPullbackPresentationNative f) := by
  sorry

/-- Canonical comparison from tensor-pullback to gamma's untwisted coordinates.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionRawPullbackModel (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.proEtaleConstantRingDerivedPullback P.Ring f ≅ P.finiteReductionPullback f :=
  Scheme.openSquareDerivedPullbackModel P.Ring f ≪≫
    (P.finiteReductionPullbackPresentation f).choose

/-- The constant coefficient square commutes with the actual quotient map.
Source: blueprint Step 1; Stacks 07A4
(blueprint: def-pur-finite-reduction-comparisons).
Proof: both maps take each constant section a to its quotient and then to the
same constant section on the pulled-back scheme. Constant sections locally generate;
sheafification uniqueness gives the equality. -/
theorem finiteReductionCoefficientSquare (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.proEtaleConstantRingComparison f P.Ring).hom ≫
        Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn) =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn)) ≫
          (Scheme.proEtaleConstantRingComparison f
            (P.finiteReductionSetting m hm).Ring).hom := by
  sorry

/-- Actual tensor/pullback coefficient comparison, conjugated into gamma's coordinates.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionPullbackComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X).obj ((P.finiteReductionPullback f).obj K) ≅
      ((P.finiteReductionSetting m hm).finiteReductionPullback f).obj
        ((P.finiteReduction m hm hmn Y).obj K) :=
  (P.finiteReduction m hm hmn X).mapIso ((P.finiteReductionRawPullbackModel f).app K).symm ≪≫
    ((Scheme.proEtaleReductionPullbackIso f
      (Scheme.proEtaleConstantRing Y P.Ring)
      (Scheme.proEtaleConstantRing Y (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRing X P.Ring)
      (Scheme.proEtaleConstantRing X (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingComparison f P.Ring)
      (Scheme.proEtaleConstantRingComparison f (P.finiteReductionSetting m hm).Ring)
      (P.finiteReductionCoefficientSquare m hm hmn f)).app K).symm ≪≫
    ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f).app
      ((P.finiteReduction m hm hmn Y).obj K)

/-- The canonical shift on scalar extension, defined by its adjunction to exact restriction.
Source: Stacks 06YY; blueprint Step 1
(blueprint: def-pur-finite-reduction-comparisons). -/
instance finiteReductionCommShift (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    (P.finiteReduction m hm hmn T).CommShift ℤ :=
  (P.finiteReductionAdjunction m hm hmn T).leftAdjointCommShift ℤ

/-- The source comparison is uniquely specified in every compatible primitive-root
chart. The power map ζ ↦ ζ^(ell^(n-m)) is the actual finite Tate-line transition;
the root charts cancel, so no root choice enters the comparison.
Source: blueprint Step 1, all integer twists and shifts
(blueprint: def-pur-finite-reduction-comparisons).
Proof: choose a primitive ell^n root in the algebraically closed base. Its indicated
power is primitive of order ell^m. Under their rank-one trivializations scalar
extension is the scalar-unit balancing map and pullback is its usual mate.
The displayed square therefore defines an isomorphism. A different primitive root
rescales both charts by the same unit after quotient, so the composite is unchanged.
The equation holds for every compatible pair and determines the isomorphism uniquely. -/
theorem existsUnique_finiteReductionSourceComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    ∃! s : (P.finiteReduction m hm hmn X).obj
        ((P.compositionShiftedPullback f d).obj K) ≅
      (((P.finiteReductionSetting m hm).compositionShiftedPullback f d).obj
        ((P.finiteReduction m hm hmn Y).obj K)),
      ∀ (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
        (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent),
        η = ζ ^ (P.coefficients.l ^ (P.level - m)) →
        s.hom ≫ ((P.finiteReductionSetting m hm).finiteReductionSourceTrivialization
          f d η hη ((P.finiteReduction m hm hmn Y).obj K)).hom =
        (P.finiteReduction m hm hmn X).map
          ((P.finiteReductionSourceTrivialization f d ζ hζ K).hom) ≫
          ((P.finiteReduction m hm hmn X).commShiftIso (2 * (d : ℤ))).hom.app
            ((P.finiteReductionPullback f).obj K) ≫
          ((P.finiteReductionPullbackComparison m hm hmn f K).hom)⟦2 * (d : ℤ)⟧' := by
  sorry

/-- Canonical source comparison, determined by the independent root, tensor,
pullback and shift normalizations above. Source: blueprint Step 1
(blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionSourceComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X).obj
        ((P.compositionShiftedPullback f d).obj K) ≅
      ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).obj
        ((P.finiteReduction m hm hmn Y).obj K) :=
  (P.existsUnique_finiteReductionSourceComparison m hm hmn f d K).choose

/-- The actual degree-zero coefficient-unit realization map. It is the composite
of the comparison unit chart, the exact-derived single-object comparison and the
section-normalized ordinary realization unit, before a finite quotient is substituted.
Source: blueprint reduction Step 1; Stacks 00YV
(blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionUnitModel (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (Scheme.sfIntrinsicDerivedEquivalence T A).functor.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          T).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit (ULift.{u + 1, u} A) T)) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.proEtaleConstantModule T A) :=
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive A T
  (Scheme.sfIntrinsicModuleEquivalence T A).functor.mapDerivedCategory.mapIso
      (finiteReductionComparisonUnitChart (ULift.{u + 1, u} A) T ≪≫
        (_root_.DerivedCategory.singleFunctorObjUnitIso
          (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).symm) ≪≫
    ((Scheme.sfIntrinsicModuleEquivalence T A).functor.mapDerivedCategorySingleFunctor
      0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (Scheme.proEtaleConstantModuleUnit T A)

/-- The scalar-unit map on the actual coefficient ring as a module is fixed on all sections.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-comparisons).
Proof: the coefficient-ring sheaf morphism is additive and linear when its target
is restricted along itself. Its section maps define a natural module morphism.
The displayed equation specifies every component on every element, hence gives uniqueness. -/
theorem existsUnique_finiteReductionUnitSectionMap (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    ∃! a : Scheme.proEtaleConstantModule T P.Ring ⟶
        (Scheme.proEtaleCoefficientRestrictScalars T
          (P.finiteReductionRingHom m hm hmn)).obj
            (Scheme.proEtaleConstantModule T (P.finiteReductionSetting m hm).Ring),
      ∀ (W : T.ProEtᵒᵖ) (x : (Scheme.proEtaleConstantRing T P.Ring).obj.obj W),
        a.val.app W x =
          (Scheme.proEtaleConstantRingMap (T := T)
            (P.finiteReductionRingHom m hm hmn)).hom.app W x := by
  sorry

/-- The degree-zero comparison is the adjoint of its specified ordinary map,
through the exact-derived single-object comparison. Construct this generically
before substituting the constant coefficient sheaves and their scalar adjunction.
Source: blueprint reduction Step 1; Stacks 06YY, 07A6
(blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionUnitAdjunct {C D : Type v} [Category.{w} C] [Category.{w} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{z} C] [HasDerivedCategory.{z} D]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (adj : L ⊣ R.mapDerivedCategory) (M : C) (N : D) (a : M ⟶ R.obj N) :
    L.obj ((_root_.DerivedCategory.singleFunctor C 0).obj M) ⟶
      (_root_.DerivedCategory.singleFunctor D 0).obj N :=
  (adj.homEquiv _ _).symm
    ((_root_.DerivedCategory.singleFunctor C 0).map a ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N)

/-- The coefficient-unit scalar map, as the actual scalar adjunct in degree zero.
The outer unit identifications transport the single-object adjunct; naturality of
adjunction transposition makes this the adjunct of the section-normalized map.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionUnitComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    (P.finiteReduction m hm hmn T).obj (P.coefficientUnit T) ⟶
      (P.finiteReductionSetting m hm).coefficientUnit T :=
  (P.finiteReduction m hm hmn T).map
      (finiteReductionUnitModel P.Ring T).hom ≫
    finiteReductionUnitAdjunct
      (Scheme.proEtaleCoefficientRestrictScalars T (P.finiteReductionRingHom m hm hmn))
      (P.finiteReduction m hm hmn T) (P.finiteReductionAdjunction m hm hmn T)
      (Scheme.proEtaleConstantModule T P.Ring)
      (Scheme.proEtaleConstantModule T (P.finiteReductionSetting m hm).Ring)
      (P.existsUnique_finiteReductionUnitSectionMap m hm hmn T).choose ≫
    (finiteReductionUnitModel (P.finiteReductionSetting m hm).Ring T).inv

/-- The normalized scalar-unit comparison is an isomorphism.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-comparisons).
Proof: the rank-one coefficient sheaf is flat. The universal derived tensor counit
computes its scalar extension by ordinary tensor; the scalar-unit adjunct is
multiplication B tensor_A A → B. Its inverse sends b to b tensor 1. The displayed
realization isomorphisms preserve constant scalar sections, so this computation
is exactly finiteReductionUnitComparison. -/
theorem finiteReductionUnitComparison_isIso (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    IsIso (P.finiteReductionUnitComparison m hm hmn T) := by
  sorry

section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The compact-support coefficient comparison is the scalar adjunct of the actual
proper/open restriction comparison applied to the scalar unit. It is independent
of any purity orientation.
Source: blueprint Step 1; Stacks 0GL5, 0GL6
(blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionCompactSupportComparison (K : Scheme.proEtaleDerivedCategory X P.Ring) :
    (P.finiteReduction m hm hmn Y).obj ((P.smoothCompactSupport f).obj K) ⟶
      ((P.finiteReductionSetting m hm).smoothCompactSupport f).obj
        ((P.finiteReduction m hm hmn X).obj K) := by
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  exact ((P.finiteReductionAdjunction m hm hmn Y).homEquiv _ _).symm
    ((P.smoothCompactSupport f).map
      ((P.finiteReductionAdjunction m hm hmn X).unit.app K) ≫
        (Scheme.sfCompactSupportRestriction (HasCompactification.compactification f)
          (P.finiteReductionRingHom m hm hmn)).hom.app
            ((P.finiteReduction m hm hmn X).obj K))

/-- Finite-Tor constructible coefficient change for the canonical compact-support mate.
Source: blueprint Step 1, lem-fix-operation-reduction
(blueprint: def-pur-finite-reduction-comparisons).
Proof: use a bounded flat model. For a compactification, the proper comparison is
the coefficient/pullback mate computed on that model; proper coefficient change
makes it invertible. Extension by zero commutes termwise with scalar extension.
Pasting these comparisons gives precisely the scalar adjunct defining the map. -/
theorem finiteReductionCompactSupportComparison_isIso
    (K : Scheme.proEtaleDerivedCategory X P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X K) :
    IsIso (P.finiteReductionCompactSupportComparison m hm hmn f K) := by
  sorry

/-- The exceptional coefficient comparison is uniquely determined by the counit
and the already specified compact-support coefficient comparison.
Source: blueprint Step 1, lem-coef-finite-exceptional
(blueprint: def-pur-finite-reduction-comparisons).
Proof: the finite-Tor constructible preservation of smooth exceptional inverse
image supplies the domain for the standing relative Hom equivalence. Transpose
the reduced counit, first using the inverse compact-support coefficient map.
The two adjunctions give existence and uniqueness of the displayed arrow. -/
theorem existsUnique_finiteReductionExceptionalComparison (d : ℕ)
    [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    ∃! b : (P.finiteReduction m hm hmn X).obj ((P.compositionExceptional f).obj K) ⟶
        ((P.finiteReductionSetting m hm).compositionExceptional f).obj
          ((P.finiteReduction m hm hmn Y).obj K),
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionExceptional f).obj K) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map b ≫
          (P.finiteReductionSetting m hm).smoothExceptionalCounit f
            ((P.finiteReduction m hm hmn Y).obj K) =
      (P.finiteReduction m hm hmn Y).map (P.smoothExceptionalCounit f K) := by
  sorry

/-- The counit-normalized exceptional coefficient arrow; no purity map defines it.
Source: blueprint Step 1, lem-coef-finite-exceptional
(blueprint: def-pur-finite-reduction-comparisons). -/
def finiteReductionExceptionalComparison (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReduction m hm hmn X).obj ((P.compositionExceptional f).obj K) ⟶
      ((P.finiteReductionSetting m hm).compositionExceptional f).obj
        ((P.finiteReduction m hm hmn Y).obj K) :=
  (P.existsUnique_finiteReductionExceptionalComparison m hm hmn f d K hK).choose

/-- The canonical exceptional coefficient comparison is invertible on the stated domain.
Source: blueprint Step 1, lem-coef-finite-exceptional
(blueprint: def-pur-finite-reduction-comparisons).
Proof: finite-Tor duality computes exceptional inverse image by the dualizing
complex. Bounded flat representatives give the coefficient comparison for that
complex and for the duality evaluation. Its counit normalization is the equation
in existsUnique_finiteReductionExceptionalComparison; hence the resulting
isomorphism is the specified comparison by uniqueness. -/
theorem finiteReductionExceptionalComparison_isIso (d : ℕ)
    [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    IsIso (P.finiteReductionExceptionalComparison m hm hmn f d K hK) := by
  sorry


end Morphism

end WeilConjectures.PurityFiniteSetting
