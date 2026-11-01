/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportScalarComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionSourceChartIndependence
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptional

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
  refine ⟨P.finiteReductionPullbackPresentationNative f, HEq.rfl, ?_⟩
  intro e he
  cases he
  rfl

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
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f
    (CommRingCat.ofHom (RingHom.ulift (P.finiteReductionRingHom m hm hmn)))).symm

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
  have hl : (P.coefficients.l : P.field.k) ≠ 0 := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    have : Fact P.field.p.Prime := ⟨P.field.prime⟩
    have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    have : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    exact CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨by
    change ((P.coefficients.l ^ P.level : ℕ) : P.field.k) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let η := ζ ^ (P.coefficients.l ^ (P.level - m))
  have hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent := by
    apply hζ.pow (NeZero.pos P.diagonalExponent)
    change P.coefficients.l ^ P.level =
      P.coefficients.l ^ (P.level - m) * P.coefficients.l ^ m
    rw [← pow_add, Nat.sub_add_cancel hmn]
  let a := ((P.finiteReduction m hm hmn X).commShiftIso (2 * (d : ℤ))).app
      ((P.finiteReductionPullback f).obj K) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (P.finiteReductionPullbackComparison m hm hmn f K)
  let s := (P.finiteReduction m hm hmn X).mapIso
      (P.finiteReductionSourceTrivialization f d ζ hζ K) ≪≫ a ≪≫
    ((P.finiteReductionSetting m hm).finiteReductionSourceTrivialization f d η hη
      ((P.finiteReduction m hm hmn Y).obj K)).symm
  refine ⟨s, ?_, ?_⟩
  · intro ζ' η' hζ' hη' he'
    have hs := P.finiteReductionSourceChart_independent m hm hmn f d K a
      ζ η ζ' η' hζ hη hζ' hη' rfl he'
    change s = _ at hs
    rw [hs]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl
  · intro t ht
    apply Iso.ext
    apply (Iso.cancel_iso_hom_right _ _
      ((P.finiteReductionSetting m hm).finiteReductionSourceTrivialization f d η hη
        ((P.finiteReduction m hm hmn Y).obj K))).1
    rw [ht ζ η hζ hη rfl]
    dsimp only [s, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

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
  let φ := Scheme.proEtaleConstantRingMap (T := T)
    (P.finiteReductionRingHom m hm hmn)
  let a : Scheme.proEtaleConstantModule T P.Ring ⟶
      (Scheme.proEtaleCoefficientRestrictScalars T
        (P.finiteReductionRingHom m hm hmn)).obj
          (Scheme.proEtaleConstantModule T (P.finiteReductionSetting m hm).Ring) :=
    { val :=
        { app := fun W ↦ ModuleCat.homMk
            ((forget₂ RingCat AddCommGrpCat).map
              ((forget₂ CommRingCat RingCat).map (φ.hom.app W)))
            (fun r ↦ by ext x; exact ((φ.hom.app W).hom.map_mul r x).symm)
          naturality := by
            intro W V f
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact ConcreteCategory.congr_hom (φ.hom.naturality f) x } }
  refine ⟨a, fun _ _ ↦ rfl, ?_⟩
  intro b hb
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hb W x

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

private theorem single_adjunct
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{z} C] [HasDerivedCategory.{z} D]
    (E : C ⥤ D) (R : D ⥤ C) [E.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : E ⊣ R) (L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (d : L ⊣ R.mapDerivedCategory) (M : C) (N : D) (a : M ⟶ R.obj N)
    (ε : L.obj ((_root_.DerivedCategory.singleFunctor C 0).obj M) ⟶
      _root_.DerivedCategory.Q.obj
        ((E.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)))
    (hd : d.unit.app ((_root_.DerivedCategory.singleFunctor C 0).obj M) ≫
        R.mapDerivedCategory.map ε ≫ R.mapDerivedCategoryFactors.hom.app _ =
      _root_.DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app
          ((CochainComplex.singleFunctor C 0).obj M))) :
    d.homEquiv _ _ (ε ≫ _root_.DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M ≫
        (CochainComplex.singleFunctor D 0).map ((adj.homEquiv _ _).symm a))) =
      (_root_.DerivedCategory.singleFunctor C 0).map a ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app N := by
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
    ((CochainComplex.singleFunctor D 0).obj N))).1
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]
  rw [R.mapDerivedCategoryFactors_hom_naturality]
  rw [reassoc_of% hd]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  change _ = _root_.DerivedCategory.Q.map
    ((CochainComplex.singleFunctor C 0).map a) ≫ _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    change adj.unit.app M ≫ R.map
      ((E.map (𝟙 M) ≫ 𝟙 (E.obj M)) ≫ (adj.homEquiv M N).symm a ≫ 𝟙 N) =
        (a ≫ 𝟙 (R.obj N)) ≫ R.map (𝟙 N)
    rw [E.map_id, R.map_id]
    simpa only [Category.id_comp, Category.comp_id, Adjunction.homEquiv_unit] using
      (adj.homEquiv M N).apply_symm_apply a
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _

private theorem single_adjunct_isIso
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{z} C] [HasDerivedCategory.{z} D]
    (E : C ⥤ D) (R : D ⥤ C) [E.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : E ⊣ R) (L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (d : L ⊣ R.mapDerivedCategory) (M : C) (N : D) (a : M ⟶ R.obj N)
    (b : E.obj M ⟶ N) [IsIso b] (ha : adj.homEquiv M N b = a)
    (ε : L.obj ((_root_.DerivedCategory.singleFunctor C 0).obj M) ⟶
      _root_.DerivedCategory.Q.obj
        ((E.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)))
    [IsIso ε]
    (hd : d.unit.app ((_root_.DerivedCategory.singleFunctor C 0).obj M) ≫
        R.mapDerivedCategory.map ε ≫ R.mapDerivedCategoryFactors.hom.app _ =
      _root_.DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app
          ((CochainComplex.singleFunctor C 0).obj M))) :
    IsIso (finiteReductionUnitAdjunct R L d M N a) := by
  have hs := single_adjunct E R adj L d M N a ε hd
  have hb : (adj.homEquiv M N).symm a = b := by
    rw [← ha, Equiv.symm_apply_apply]
  rw [hb] at hs
  have hh : finiteReductionUnitAdjunct R L d M N a =
      ε ≫ _root_.DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M ≫
          (CochainComplex.singleFunctor _ 0).map b) := by
    exact (d.homEquiv _ _).injective
      (((d.homEquiv _ _).apply_symm_apply _).trans hs.symm)
  rw [hh]
  infer_instance

private def scalarUnitOrdinaryIso {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (Scheme.pbcExtend φ).obj (SheafOfModules.unit
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
      SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
  eqToIso ((Scheme.pbcExtensionExistence φ).choose_spec.choose _) ≪≫
    SheafOfModules.scalarExtensionUnitIso φ

private instance finiteReduction_small (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private theorem scalarUnit_kflat {T : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T) (R := R)
      ((CochainComplex.singleFunctor (Scheme.pbcModules T R) 0).obj
        (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.symmetricCategory.{u, u + 1, u + 1} R
  intro Z hZ
  exact fun i ↦ (hZ i).of_iso (HomologicalComplex.rightUnitor Z).symm

private theorem scalarUnitOrdinaryIso_section {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (W : T.ProEtᵒᵖ) (x : R.obj.obj W) :
    (scalarUnitOrdinaryIso φ).hom.val.app W
      (((Scheme.pbcScalarAdjunction φ).unit.app
        (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))).val.app
          W x) = φ.hom.app W x := by
  erw [(Scheme.pbcScalarAdjunction_exists φ).exists.choose_spec]
  let M := SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let h := (Scheme.pbcExtensionExistence φ).choose_spec.choose M
  have hc : (eqToHom h).val.app W
      ((eqToHom h.symm).val.app W
        (SheafOfModules.scalarExtensionSection φ M W 1 x)) =
        SheafOfModules.scalarExtensionSection φ M W 1 x := by
    have hh := congrArg (fun f ↦ f.val.app W)
      (show eqToHom h.symm ≫ eqToHom h = 𝟙 _ by simp)
    exact ConcreteCategory.congr_hom hh _
  change (SheafOfModules.scalarExtensionUnitIso φ).hom.val.app W
    ((eqToHom h).val.app W ((eqToHom h.symm).val.app W
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} φ M W 1 x))) = _
  exact (congrArg ((SheafOfModules.scalarExtensionUnitIso φ).hom.val.app W) hc).trans
    (by simpa only [one_mul] using SheafOfModules.scalarExtensionUnitIso_tmul φ W 1 x)

private theorem complexCounit_isIso {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : CochainComplex (Scheme.pbcModules T R) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology T) (R := R) K) :
    IsIso (Scheme.pbcComplexCounit φ K) := by
  have := Scheme.pbcExtensionCounit_isIso φ K hK
  dsimp only [Scheme.pbcComplexCounit]
  infer_instance

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem scalarAdjunction_normalization {T : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : CochainComplex (Scheme.pbcModules T R) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology T) (R := R) K) :
    (Scheme.pbcDerivedScalarAdjunction φ).unit.app (_root_.DerivedCategory.Q.obj K) ≫
        (Scheme.pbcDerivedRestrict φ).map (Scheme.pbcComplexCounit φ K) ≫
        (Scheme.pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((Scheme.pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj K) =
      _root_.DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (Scheme.pbcScalarAdjunction φ).unit (.up ℤ)).app K) :=
  (Scheme.pbcDerivedScalarAdjunction_exists φ).exists.choose_spec K hK

attribute [local irreducible] scalarUnitOrdinaryIso Scheme.pbcComplexCounit
  Scheme.pbcScalarAdjunction Scheme.pbcDerivedScalarAdjunction

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
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
  let φ := Scheme.proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn)
  let M := Scheme.proEtaleConstantModule T P.Ring
  let N := Scheme.proEtaleConstantModule T (P.finiteReductionSetting m hm).Ring
  let a := (P.existsUnique_finiteReductionUnitSectionMap m hm hmn T).choose
  let E := Scheme.pbcExtend φ
  let R := Scheme.pbcRestrict φ
  let adj := Scheme.pbcScalarAdjunction φ
  let L := P.finiteReduction m hm hmn T
  let d := P.finiteReductionAdjunction m hm hmn T
  let e := scalarUnitOrdinaryIso φ
  have he : adj.homEquiv M N e.hom = a := by
    change (Scheme.pbcScalarAdjunction φ).homEquiv M N e.hom = a
    rw [Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (scalarUnitOrdinaryIso_section φ W x).trans
      ((P.existsUnique_finiteReductionUnitSectionMap m hm hmn T).choose_spec.1 W x).symm
  let K := (CochainComplex.singleFunctor _ 0).obj M
  let ε := Scheme.pbcComplexCounit φ K
  have hε : IsIso ε := by
    exact complexCounit_isIso φ K (scalarUnit_kflat _)
  have hd := scalarAdjunction_normalization φ K (scalarUnit_kflat _)
  change d.unit.app (_root_.DerivedCategory.Q.obj K) ≫ R.mapDerivedCategory.map ε ≫
    R.mapDerivedCategoryFactors.hom.app _ = _ at hd
  have hi : IsIso (finiteReductionUnitAdjunct R L d M N a) :=
    single_adjunct_isIso E R adj L d M N a e.hom he ε hd
  change IsIso (L.map (finiteReductionUnitModel P.Ring T).hom ≫
    finiteReductionUnitAdjunct R L d M N a ≫
      (finiteReductionUnitModel (P.finiteReductionSetting m hm).Ring T).inv)
  infer_instance

private theorem transported_counit_bijective
    {C D C' D' : Type v} [Category.{w} C] [Category.{w} D]
    [Category.{z} C'] [Category.{z} D'] (E : C ≌ C') (H : D ≌ D')
    (F : C ⥤ D) (F' : C' ⥤ D') (α : E.functor ⋙ F' ≅ F ⋙ H.functor)
    (L : C') (N : C) (K : D') (ε : F.obj N ⟶ H.inverse.obj K)
    (h : Function.Bijective (fun b : E.inverse.obj L ⟶ N ↦ F.map b ≫ ε)) :
    Function.Bijective (fun b : L ⟶ E.functor.obj N ↦
      F'.map b ≫ α.hom.app N ≫ H.functor.map ε ≫ H.counitIso.hom.app K) := by
  let a₀ : (E.functor.obj (E.inverse.obj L) ⟶ E.functor.obj N) ≃
      (L ⟶ E.functor.obj N) :=
    { toFun := fun g ↦ (E.counitIso.app L).inv ≫ g
      invFun := fun g ↦ (E.counitIso.app L).hom ≫ g
      left_inv := by intro g; simp
      right_inv := by intro g; simp }
  let a : (E.inverse.obj L ⟶ N) ≃ (L ⟶ E.functor.obj N) :=
    E.fullyFaithfulFunctor.homEquiv.trans a₀
  let δ := (F'.mapIso (E.counitIso.app L).symm) ≪≫ α.app (E.inverse.obj L)
  let b₀ : (H.functor.obj (F.obj (E.inverse.obj L)) ⟶
      H.functor.obj (H.inverse.obj K)) ≃ (F'.obj L ⟶ K) :=
    { toFun := fun g ↦ δ.hom ≫ g ≫ H.counitIso.hom.app K
      invFun := fun g ↦ δ.inv ≫ g ≫ H.counitIso.inv.app K
      left_inv := by intro g; simp
      right_inv := by intro g; simp }
  let b : (F.obj (E.inverse.obj L) ⟶ H.inverse.obj K) ≃ (F'.obj L ⟶ K) :=
    H.fullyFaithfulFunctor.homEquiv.trans b₀
  have hcomp : (fun b : L ⟶ E.functor.obj N ↦
      F'.map b ≫ α.hom.app N ≫ H.functor.map ε ≫ H.counitIso.hom.app K) ∘ a =
      b ∘ (fun b : E.inverse.obj L ⟶ N ↦ F.map b ≫ ε) := by
    funext g
    change F'.map ((E.counitIso.app L).inv ≫ E.functor.map g) ≫
        α.hom.app N ≫ H.functor.map ε ≫ H.counitIso.hom.app K =
      (F'.map (E.counitIso.app L).inv ≫ α.hom.app (E.inverse.obj L)) ≫
        H.functor.map (F.map g ≫ ε) ≫ H.counitIso.hom.app K
    have hn := α.hom.naturality g
    change F'.map (E.functor.map g) ≫ α.hom.app N =
      α.hom.app (E.inverse.obj L) ≫ H.functor.map (F.map g) at hn
    rw [Functor.map_comp, Category.assoc, reassoc_of% hn, H.functor.map_comp]
    simp only [Category.assoc]
  refine (Function.Bijective.of_comp_iff _ a.bijective).1 ?_
  rw [hcomp]
  exact b.bijective.comp h

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
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  have hl : IsUnit (P.coefficients.l : P.field.k) := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    have : Fact P.field.p.Prime := ⟨P.field.prime⟩
    have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    have : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    exact isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm)
  have _ := (inferInstance : IsSeparated (X ↘ Spec (.of P.field.k)))
  have _ := (inferInstance : IsSeparated (Y ↘ Spec (.of P.field.k)))
  exact Scheme.finiteCompactSupportScalarComparison P.coefficients.l P.extension P.field.k hl
    P.level P.level_pos m hm hmn f (HasCompactification.compactification f) K hK.1
    (P.finiteReduction_preserves_ctf m hm hmn X K hK).1

private theorem finiteReduction_counit_bijective (Q : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of Q.field.k))]
    [Y.Over (Spec (.of Q.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of Q.field.k))]
    [QuasiCompact (X ↘ Spec (.of Q.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of Q.field.k))]
    [QuasiCompact (Y ↘ Spec (.of Q.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of Q.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Scheme.proEtaleDerivedCategory X Q.Ring)
    (hL : finiteTorConstructible Q.coefficients.l Q.extension Q.level Q.level_pos X L)
    (K : Scheme.proEtaleDerivedCategory Y Q.Ring)
    (hK : finiteTorConstructible Q.coefficients.l Q.extension Q.level Q.level_pos Y K) :
    Function.Bijective (fun b : L ⟶ (Q.compositionExceptional f).obj K ↦
      (Q.smoothCompactSupport f).map b ≫ Q.smoothExceptionalCounit f K) := by
  classical
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of Q.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of Q.field.k)))
  let := hasCompactification_of_finiteType_over_field Q.field.k X Y f
  let E := Scheme.sfIntrinsicDerivedEquivalence X Q.Ring
  let H := Scheme.sfIntrinsicDerivedEquivalence Y Q.Ring
  have hL' := (Q.compositionInput_bounded L hL).plusEtaleOrigin
  have hK' := (Q.compositionInput_bounded K hK).plusEtaleOrigin.plus
  have hb := ProEtale.bijective_rightDerivedLowerShriek_map_comp_counit f hL' hK'
  have ht := transported_counit_bijective E H
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Q.Coefficient) f)
    (Q.smoothCompactSupport f)
    (ProEtale.sfIntrinsicCompactSupportComparison Q.Ring
      (HasCompactification.compactification f)) L
    ((Q.smoothPurityExceptionalOver f (Y ↘ Spec (.of Q.field.k))).obj
      (H.inverse.obj K)) K
    (ProEtale.rightDerivedUpperShriekCounit f (H.inverse.obj K) hK') hb
  simpa only [E, H, compositionExceptional, Functor.comp_obj, smoothExceptionalCounit,
    dif_pos hK', Category.assoc] using ht

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
  let Q := P.finiteReductionSetting m hm
  let L := (P.compositionExceptional f).obj K
  have hL := P.compositionExceptional_ctf f d K hK
  let := P.finiteReductionCompactSupportComparison_isIso m hm hmn f L hL
  have hbij := finiteReduction_counit_bijective Q f
    ((P.finiteReduction m hm hmn X).obj L)
    (P.finiteReduction_preserves_ctf m hm hmn X L hL)
    ((P.finiteReduction m hm hmn Y).obj K)
    (P.finiteReduction_preserves_ctf m hm hmn Y K hK)
  let a := P.finiteReductionCompactSupportComparison m hm hmn f L
  let t := (P.finiteReduction m hm hmn Y).map (P.smoothExceptionalCounit f K)
  obtain ⟨b, hb⟩ := hbij.2 (inv a ≫ t)
  dsimp only at hb
  refine ⟨b, ?_, ?_⟩
  · change a ≫ ((Q.smoothCompactSupport f).map b ≫ Q.smoothExceptionalCounit f _) = t
    calc
      _ = a ≫ (inv a ≫ t) := congrArg (fun z ↦ a ≫ z) hb
      _ = t := IsIso.hom_inv_id_assoc a t
  · intro b' hb'
    apply hbij.1
    apply (cancel_epi a).1
    exact hb'.trans (by
      calc
        t = a ≫ (inv a ≫ t) := (IsIso.hom_inv_id_assoc a t).symm
        _ = _ := congrArg (fun z ↦ a ≫ z) hb.symm)

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

end Morphism

end WeilConjectures.PurityFiniteSetting
