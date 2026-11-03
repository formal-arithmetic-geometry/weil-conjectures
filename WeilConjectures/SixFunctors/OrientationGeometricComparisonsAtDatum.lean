/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OrientationEtaleCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekPreservation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition

/-!
# Geometric orientation comparisons at a finite coefficient datum

The source and target of the comparison square are fixed here.  The ordinary line is
built from the finite etale root line, while the native line is built from the finite
root site tensor and its derived tensor powers.  The root comparison is consequently
constructed from the recorded finite-root comparison and the derived site tensor
comparison; it is not a field of the orientation bundle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- The ordinary shifted root-line tensor powers used to put the comparison in a
single source category.  The first two entries are the degree-zero and root-line
entries of `sfOrientationEtaleLine`; subsequent entries use its derived tensor. -/
noncomputable def sfOrientationEtalePower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    ℕ → AlgebraicGeometry.Etale.DerivedCategoryModule A X
  | 0 => sfOrientationEtaleLine A N hA X 0
  | 1 => sfOrientationEtaleLine A N hA X 1
  | d + 2 =>
      (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (sfOrientationEtalePower A X N hN hA (d + 1)) |>.obj
        (sfOrientationEtaleLine A N hA X 1)

/-- The native pro-etale tensor powers of the finite root line. -/
noncomputable def sfOrientationNativePower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (X : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hX : IsUnit (N : Γ(X, ⊤))) :
    ℕ → DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
  | 0 => (AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (sfOrientationEtalePower A X N hN hA 0)
  | 1 => (shiftFunctor _ (2 : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (AlgebraicGeometry.Scheme.finiteRootProTensor A N hN hA X))
  | d + 2 =>
      (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (sfOrientationNativePower A X N hN hA hX (d + 1)) |>.obj
        ((shiftFunctor _ (2 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
          (AlgebraicGeometry.Scheme.finiteRootProTensor A N hN hA X)))

/-- The canonical line source `T_{X,d}` at the finite stage. -/
noncomputable def sfOrientationNativeSource
    {A : Type (u + 1)} [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X : Scheme.{u}} (N : ℕ) (hA : (N : A) = 0) (d : ℕ)
    (hN : 0 < N) (hX : IsUnit (N : Γ(X, ⊤))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  sfOrientationNativePower A X N hN hA hX d

/-- The canonical comparison from the recursively tensorized ordinary line to the
published shifted line. -/
noncomputable def sfOrientationEtalePowerToLine
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (X : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hX : IsUnit (N : Γ(X, ⊤))) : ∀ d : ℕ,
    sfOrientationEtalePower A X N hN hA d ≅ sfOrientationEtaleLine A N hA X d
  | 0 => Iso.refl _
  | 1 => Iso.refl _
  | d + 2 =>
      tensorIso (sfOrientationEtalePowerToLine A X N hN hA hX (d + 1)) (Iso.refl _) ≪≫
        sfOrientationEtaleProduct A N hN hA X hX (d + 1) 1

noncomputable def sfOrientationNativeTarget
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [HasCompactification g] :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A g).obj
    (D(ν^*(Y)[ModuleCat.{u + 1} A]).obj
      (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A Y)))

/-- The unit-induced comparison used by the finite-stage pro-etale maps. -/
noncomputable def sfOrientationUnitInducedExceptionalIsoAtDatum
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (hunit : _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A Y))) :
    D(ν^*(X)[ModuleCat.{u + 1} A]).obj
      ((AlgebraicGeometry.Etale.rightDerivedUpperShriek A f).obj (𝟙_ _)) ≅
      (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A f).obj
        (D(ν^*(Y)[ModuleCat.{u + 1} A]).obj (𝟙_ _)) :=
  letI := AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y (𝟙_ _) hunit
  D(ν^*(X)[ModuleCat.{u + 1} A]).mapIso
    ((AlgebraicGeometry.Etale.rightDerivedUpperShriek A f).mapIso
      (asIso
        ((AlgebraicGeometry.ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} A) Y).unit.app (𝟙_ _))))

/-- Pullback of the recursively tensorized ordinary finite root line. -/
noncomputable def sfOrientationEtalePowerPullback
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (hU : IsUnit (N : Γ(U, ⊤))) (hV : IsUnit (N : Γ(V, ⊤))) :
    ∀ d : ℕ,
      ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj
        (sfOrientationEtalePower A V N hN hA d) ≅
      sfOrientationEtalePower A U N hN hA d
  | 0 => sfOrientationEtaleLinePullback A N hN hA g hU hV 0
  | 1 => sfOrientationEtaleLinePullback A N hN hA g hU hV 1
  | d + 2 =>
      (AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso
        (ModuleCat.{u + 1} A) g
        (sfOrientationEtalePower A V N hN hA (d + 1))
        (sfOrientationEtaleLine A N hA V 1)) ≪≫
        tensorIso
          (sfOrientationEtalePowerPullback A N hN hA g hU hV (d + 1))
          (sfOrientationEtaleLinePullback A N hN hA g hU hV 1)

/-- Multiplication of the recursively tensorized ordinary finite root lines. -/
noncomputable def sfOrientationEtalePowerProduct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X : Scheme.{u}} (hX : IsUnit (N : Γ(X, ⊤))) (d e : ℕ) :
    ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      (sfOrientationEtalePower A X N hN hA d)).obj
      (sfOrientationEtalePower A X N hN hA e) ≅
    sfOrientationEtalePower A X N hN hA (d + e) :=
  (tensorIso
      (sfOrientationEtalePowerToLine A X N hN hA hX d)
      (sfOrientationEtalePowerToLine A X N hN hA hX e)) ≪≫
    sfOrientationEtaleProduct A N hN hA X hX d e ≪≫
    (sfOrientationEtalePowerToLine A X N hN hA hX (d + e)).symm

/-- Native pullback comparison obtained by transporting the ordinary pullback through ν. -/
noncomputable def sfOrientationCanonicalPullback
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {U V : Scheme.{u}} (g : U ⟶ V)
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hU : IsUnit (N : Γ(U, ⊤))) (hV : IsUnit (N : Γ(V, ⊤))) (d : ℕ) :
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
      (sfOrientationNativeSource N hA d hN hV) ≅
      sfOrientationNativeSource N hA d hN hU :=
  ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.mapIso
      (sfOrientationCanonicalRootComparisonAtDatum A N hN hA hV d).symm) ≪≫
    (AlgebraicGeometry.ProEtale.derivedComparisonUpperStarUpperStarIso
      (ModuleCat.{u + 1} A) g).app
      (sfOrientationEtalePower A V N hN hA d) ≪≫
    (D(ν^*(U)[ModuleCat.{u + 1} A]).mapIso
      (sfOrientationEtalePowerPullback A N hN hA g hU hV d)) ≪≫
    sfOrientationCanonicalRootComparisonAtDatum A N hN hA hU d

/-- Native tensor multiplication transported from the ordinary finite root line. -/
noncomputable def sfOrientationCanonicalProduct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {U : Scheme.{u}} (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hU : IsUnit (N : Γ(U, ⊤))) (d e : ℕ) :
    ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).obj
      (sfOrientationNativeSource N hA d hN hU)).obj
      (sfOrientationNativeSource N hA e hN hU) ≅
    sfOrientationNativeSource N hA (d + e) hN hU :=
  let tde := sfOrientationCanonicalRootComparisonAtDatum A N hN hA hU (d + e)
  let td := sfOrientationCanonicalRootComparisonAtDatum A N hN hA hU d
  let te := sfOrientationCanonicalRootComparisonAtDatum A N hN hA hU e
  let q := asIso
    ((AlgebraicGeometry.ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      (sfOrientationEtalePower A U N hN hA d)).hom.app
        (sfOrientationEtalePower A U N hN hA e))
  (tensorIso td te).symm ≪≫ q.symm ≪≫
    (D(ν^*(U)[ModuleCat.{u + 1} A]).mapIso
      (sfOrientationEtalePowerProduct A N hN hA hU d e)) ≪≫ tde

/-- Canonical exceptional base-change map.  This is the ν-transport of the recorded etale
base-change mate, followed by the derived comparison unit at the bottom edge. -/
noncomputable def sfOrientationCanonicalBeta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {U V U' V' : Scheme.{u}} {g : V' ⟶ V} {f' : U' ⟶ V'}
    {f : U ⟶ V} {g' : U' ⟶ U} (sq : IsPullback g' f' f g)
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f] [QuasiCompact f'] :
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj
        (sfOrientationNativeTarget A f) ⟶ sfOrientationNativeTarget A f' := by
  let K := (AlgebraicGeometry.Etale.rightDerivedUpperShriek A f).obj
    ((R(ν_*(V)[ModuleCat.{u + 1} A])).obj
      (D(ν^*(V)[ModuleCat.{u + 1} A]).obj
        (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A V))))
  let unitPullback :
      (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
          (𝟙_ _) ⟶
        D(ν^*(V')[ModuleCat.{u + 1} A]).obj (𝟙_ _) :=
    (((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.mapIso
      (AlgebraicGeometry.ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
        A V).symm) ≪≫
    (AlgebraicGeometry.ProEtale.derivedComparisonUpperStarUpperStarIso
      (ModuleCat.{u + 1} A) g).app
      (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A V)) ≪≫
    ((D(ν^*(V')[ModuleCat.{u + 1} A]).mapIso
      (AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso
        (ModuleCat.{u + 1} A) g)))).hom
  simp only [sfOrientationNativeTarget,
    AlgebraicGeometry.ProEtale.rightDerivedUpperShriek, Functor.comp_obj]
  let comparisonMap :=
    ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
      ((R(ν_*(V)[ModuleCat.{u + 1} A])).map
        (AlgebraicGeometry.ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
          A V).hom)) ≫
    ((AlgebraicGeometry.ProEtale.rightDerivedComparisonBaseChange
      (ModuleCat.{u + 1} A) g).app (𝟙_ _)) ≫
    ((R(ν_*(V')[ModuleCat.{u + 1} A])).map unitPullback)
  exact
    (by simpa only [Functor.comp_obj] using
      ((AlgebraicGeometry.ProEtale.derivedComparisonUpperStarUpperStarIso
        (ModuleCat.{u + 1} A) g').app K).hom) ≫
    D(ν^*(U')[ModuleCat.{u + 1} A]).map
      ((AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap A sq).app
          ((R(ν_*(V)[ModuleCat.{u + 1} A])).obj
            (D(ν^*(V)[ModuleCat.{u + 1} A]).obj
              (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A V))))) ≫
    D(ν^*(U')[ModuleCat.{u + 1} A]).map
      ((AlgebraicGeometry.Etale.rightDerivedUpperShriek A f').map comparisonMap)

/-- The canonical projection tensor map, transported from the etale dualizing tensor mate. -/
noncomputable def sfOrientationCanonicalTheta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {U V : Scheme.{u}} (g : U ⟶ V) [HasCompactification g]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (_hU : IsUnit (N : Γ(U, ⊤))) (hV : IsUnit (N : Γ(V, ⊤)))
    (e : ℕ)
    (hunitV : _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A V))) :
    ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).obj
      (sfOrientationNativeTarget A g)).obj
      ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
        (sfOrientationNativeSource N hA e hN hV)) ⟶
      (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A g).obj
        (sfOrientationNativeSource N hA e hN hV) := by
  let targetIso := sfOrientationUnitInducedExceptionalIsoAtDatum (A := A) g hunitV
  let root := sfOrientationCanonicalRootComparisonAtDatum A N hN hA hV e
  let pull := (AlgebraicGeometry.ProEtale.derivedComparisonUpperStarUpperStarIso
      (ModuleCat.{u + 1} A) g).app
      (sfOrientationEtalePower A V N hN hA e)
  let tensorComparison :=
    asIso (((AlgebraicGeometry.ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      (AlgebraicGeometry.Etale.dualizingComplex A g)).hom.app
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
          (sfOrientationEtalePower A V N hN hA e))))
  let unitMap :=
    ((AlgebraicGeometry.Etale.rightDerivedUpperShriek A g).map
      ((AlgebraicGeometry.ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} A) V).unit.app
        (sfOrientationEtalePower A V N hN hA e))) ≫
    (AlgebraicGeometry.Etale.rightDerivedUpperShriek A g).map
      ((R(ν_*(V)[ModuleCat.{u + 1} A])).map root.hom)
  exact
    (tensorIso targetIso.symm
      ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.mapIso
        root.symm ≪≫ pull)).hom ≫
    tensorComparison.inv ≫
    (D(ν^*(U)[ModuleCat.{u + 1} A]).map
      (AlgebraicGeometry.Etale.dualizingComplexTensorMap A g
        (sfOrientationEtalePower A V N hN hA e))) ≫
    D(ν^*(U)[ModuleCat.{u + 1} A]).map unitMap

/-- The canonical exceptional-composition comparison, obtained by transporting the published
finite-coefficient étale compositor through the comparison units on bounded-below objects.
The middle arrow is `PurityFiniteSetting.finiteExceptionalComposition`, the conjugate of
the specified compact-support compositor. No existence-only choice of an iso occurs.
Boundedness of the intermediate dualizing complex is obtained by applying the existing
single-complex, shift, and iso stability
lemmas to the published smooth-duality decomposition; only a proposition is extracted.
Source: composition convention in def-sf-orientation, clauses 1-2
(blueprint: def-sf-orientation-geometric-comparisons-at-datum). -/
noncomputable def sfOrientationCanonicalAlpha
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {U V W : Scheme.{u}} (g : U ⟶ V) (h : V ⟶ W) (e : ℕ)
    [HasCompactification g] [HasCompactification h] [HasCompactification (g ≫ h)]
    [QuasiCompact g] [QuasiCompact (g ≫ h)]
    [SmoothOfRelativeDimension e h]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hV : IsUnit (N : Γ(V, ⊤)))
    (hunitW : _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A W))) :
    sfOrientationNativeTarget A (g ≫ h) ≅
      (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A g).obj
        (sfOrientationNativeTarget A h) := by
  letI : HasInvertibleExponent A V := ⟨N, hN, hA, hV⟩
  let C := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)
  let hplus : _root_.DerivedCategory.TStructure.t.plus
      ((AlgebraicGeometry.Etale.rightDerivedUpperShriek A h).obj (𝟙_ _)) :=
    (AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor A h e).elim
      fun L hL ↦ hL.2.2.1.elim fun eω ↦
        _root_.DerivedCategory.TStructure.t.plus.prop_of_iso eω.symm
          (_root_.DerivedCategory.TStructure.t.plus.le_shift (2 * (e : ℤ)) _
            (_root_.DerivedCategory.TStructure.t.plus.prop_of_iso
              ((_root_.DerivedCategory.Plus.singleFunctorιIso C 0).app L)
              (((_root_.DerivedCategory.Plus.singleFunctor C 0).obj L).property)))
  let G : _root_.DerivedCategory
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) := 𝟙_ _
  let wgh :=
    AlgebraicGeometry.ProEtale.rightDerivedUpperShriekMapDerivedCategoryObjIso (Λ := A)
      (g ≫ h) G hunitW
  let wh := sfOrientationUnitInducedExceptionalIsoAtDatum (A := A) h hunitW
  let wg :=
    AlgebraicGeometry.ProEtale.rightDerivedUpperShriekMapDerivedCategoryObjIso (Λ := A)
      g (AlgebraicGeometry.Etale.dualizingComplex A h) hplus
  let ecomp := PurityFiniteSetting.finiteExceptionalComposition A g h
  let eapp := ecomp.app G
  change
    (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A (g ≫ h)).obj
        (D(ν^*(W)[ModuleCat.{u + 1} A]).obj G) ≅
      (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A g).obj
        ((AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A h).obj
          (D(ν^*(W)[ModuleCat.{u + 1} A]).obj G))
  exact wgh ≪≫
    D(ν^*(U)[ModuleCat.{u + 1} A]).mapIso eapp ≪≫
    wg.symm ≪≫
    (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A g).mapIso wh

/-- Full geometric-family data at the actual finite coefficient stage.  The fixed datum map
`f` has one component, and `family_component` extends it to every smooth separated map;
`component_spec` ties the two at the datum map.  This is the finite-stage specialization
of the landed geometric comparison interface.
(blueprint: def-sf-orientation-geometric-comparisons-at-datum). -/
structure SfGeometricOrientationAtDatum
    {A : Type (u + 1)} [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) where
  component : ∀ (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension d f]
    [HasCompactification f] (hX : IsUnit (N : Γ(X, ⊤))),
    sfOrientationNativeSource N hA d hN hX ≅
      (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A f).obj
        ((AlgebraicGeometry.ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A Y)))
  family_component : ∀ {U V : Scheme.{u}} (g : U ⟶ V) (d : ℕ)
    [IsSeparated g] [QuasiCompact g] [SmoothOfRelativeDimension d g]
    [HasCompactification g] (hU : IsUnit (N : Γ(U, ⊤))),
    sfOrientationNativeSource N hA d hN hU ≅
      (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A g).obj
        ((AlgebraicGeometry.ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj
          (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A V)))
  component_spec : ∀ (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension d f]
    [HasCompactification f] (hX : IsUnit (N : Γ(X, ⊤))),
    family_component f d hX = component d hX
  /-- Base change of the native component through the canonical declarations. -/
  baseChange : ∀ {U V U' V' : Scheme.{u}} {g : V' ⟶ V} {f' : U' ⟶ V'}
    {f : U ⟶ V} {g' : U' ⟶ U} (sq : IsPullback g' f' f g) (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension d f]
    [HasCompactification f] [IsSeparated f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f'] [HasCompactification f']
    (hU' : IsUnit (N : Γ(U', ⊤))) (hU : IsUnit (N : Γ(U, ⊤))),
    (family_component f' d hU').hom =
      (sfOrientationCanonicalPullback A g' N hN hA hU' hU d).inv ≫
        ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor).map
          (family_component f d hU).hom ≫
        sfOrientationCanonicalBeta A sq
  /-- Smooth composition using the canonical product, pullback, projection, and composition maps. -/
  composition : ∀ {U V W : Scheme.{u}} (g : U ⟶ V) (h : V ⟶ W) (d e : ℕ)
    [IsSeparated g] [QuasiCompact g] [IsSeparated h] [QuasiCompact h]
    [IsSeparated (g ≫ h)] [QuasiCompact (g ≫ h)]
    [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension e h]
    [SmoothOfRelativeDimension (d + e) (g ≫ h)]
    [HasCompactification g] [HasCompactification h] [HasCompactification (g ≫ h)]
    (hU : IsUnit (N : Γ(U, ⊤))) (hV : IsUnit (N : Γ(V, ⊤)))
    (hunitV : _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A V)))
    (hunitW : _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (AlgebraicGeometry.Etale.DerivedCategoryModule A W))),
    (family_component (g ≫ h) (d + e) hU).hom =
      (sfOrientationCanonicalProduct A N hN hA hU d e).inv ≫
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).obj
        (sfOrientationNativeSource N hA d hN hU)).map
          (sfOrientationCanonicalPullback A g N hN hA hU hV e).inv ≫
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).map
        (family_component g d hU).hom).app
        ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
          (sfOrientationNativeSource N hA e hN hV)) ≫
      sfOrientationCanonicalTheta A g N hN hA hU hV e hunitV ≫
      (AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A g).map
        (family_component h e hV).hom ≫
      (sfOrientationCanonicalAlpha A g h e N hN hA hV hunitW).inv

end WeilConjectures
