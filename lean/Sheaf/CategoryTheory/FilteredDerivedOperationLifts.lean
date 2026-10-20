/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.CategoryTheory.FilteredFunctorGradedComparison
import Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.IntegralFinitePullbackComposition
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Filtered derived operation lifts

Source: Stacks Project, Tags 015Q, 015S, 05U2, 015U and 015V; Varshavsky,
Lefschetz--Verdier trace formula, Lemma 5.1.4 and Sections 5.2.1--5.2.2
(blueprint: lem-trf-filtered-derived-operation-lifts).

The records below contain actual filtered functors, triangulated structures, natural
isomorphisms, adjunctions, and equations. They do not hide comparison maps or coherence
laws in unconstrained propositions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe wA vA uA wB vB uB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A filtered lift of a derived operation, with exactness and all comparisons explicit.
Source: Stacks, Tags 015Q, 015S and 05U2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
structure FilteredDerivedOperationLift
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) where
  filtered : ∀ (bounds : Option (ℤ × ℤ)),
    FiniteFilteredDerivedPlus (C := A) bounds ⥤
      FiniteFilteredDerivedPlus (C := B) bounds
  filteredCommShift : ∀ (bounds : Option (ℤ × ℤ)),
    (filtered bounds).CommShift ℤ
  filteredTriangulated : ∀ (bounds : Option (ℤ × ℤ)),
    letI := filteredCommShift bounds
    (filtered bounds).IsTriangulated
  forgetComparison : ∀ (bounds : Option (ℤ × ℤ)),
    filtered bounds ⋙ finiteFilteredDerivedEvaluation (C := B) bounds none ≅
      finiteFilteredDerivedEvaluation (C := A) bounds none ⋙ ordinary
  gradedComparison : ∀ (bounds : Option (ℤ × ℤ)) (r : ℤ),
    filtered bounds ⋙ finiteFilteredDerivedEvaluation (C := B) bounds (some r) ≅
      finiteFilteredDerivedEvaluation (C := A) bounds (some r) ⋙ ordinary

attribute [instance] FilteredDerivedOperationLift.filteredTriangulated

/-- An exact termwise lift, specified on finite filtered objects, on each filtration
subobject inclusion, and on bounded-below filtered homotopy categories. The localization
factorization identifies the filtered functor with that very termwise action.
Source: Stacks, Tags 05RX and 015Q
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
structure FilteredTermwiseLift
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    extends FilteredDerivedOperationLift H.mapDerivedCategoryPlus where
  objectAction : ∀ bounds : Option (ℤ × ℤ),
    FiniteFilteredObjects A bounds false ⥤ FiniteFilteredObjects B bounds false
  [objectActionAdditive : ∀ bounds : Option (ℤ × ℤ), (objectAction bounds).Additive]
  objectComparison : ∀ bounds : Option (ℤ × ℤ),
    objectAction bounds ⋙ filteredEvaluation B bounds false none ≅
      filteredEvaluation A bounds false none ⋙ H
  stepComparison : ∀ (bounds : Option (ℤ × ℤ))
    (K : FiniteFilteredObjects A bounds false) (p : ℤ),
    (((objectAction bounds).obj K).obj.filtration.step p : B) ≅
      H.obj (K.obj.filtration.step p : A)
  stepInclusion : ∀ (bounds : Option (ℤ × ℤ))
    (K : FiniteFilteredObjects A bounds false) (p : ℤ),
    (((objectAction bounds).obj K).obj.filtration.step p).arrow ≫
        (objectComparison bounds).hom.app K =
      (stepComparison bounds K p).hom ≫ H.map (K.obj.filtration.step p).arrow
  localizationComparison : ∀ bounds : Option (ℤ × ℤ),
    finiteFilteredQh A bounds ⋙ filtered bounds ≅
      (objectAction bounds).mapHomotopyCategoryPlus ⋙ finiteFilteredQh B bounds

section Adjunction

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {L : DerivedCategory.Plus B ⥤ DerivedCategory.Plus A}
  {T : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}

/-- Transport the unit of a filtered adjunction through the forgetful comparisons.
Source: Varshavsky, Section 5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
def filteredUnitForgetTransport
    (left : FilteredDerivedOperationLift L)
    (right : FilteredDerivedOperationLift T)
    (adj : ∀ bounds : Option (ℤ × ℤ),
      (left.filtered bounds) ⊣ (right.filtered bounds))
    (bounds : Option (ℤ × ℤ)) :
    finiteFilteredDerivedEvaluation (C := B) bounds none ⟶
      finiteFilteredDerivedEvaluation (C := B) bounds none ⋙ (L ⋙ T) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (adj bounds).unit
      (finiteFilteredDerivedEvaluation (C := B) bounds none) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (left.filtered bounds)
      (right.forgetComparison bounds).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (left.forgetComparison bounds).hom T ≫
    (Functor.associator _ _ _).hom

/-- Transport the counit through the forgetful comparison.
Source: Varshavsky, Section 5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
def filteredCounitForgetTransport
    (left : FilteredDerivedOperationLift L)
    (right : FilteredDerivedOperationLift T)
    (adj : ∀ bounds : Option (ℤ × ℤ),
      (left.filtered bounds) ⊣ (right.filtered bounds))
    (bounds : Option (ℤ × ℤ)) :
    finiteFilteredDerivedEvaluation (C := A) bounds none ⋙ (T ⋙ L) ⟶
      finiteFilteredDerivedEvaluation (C := A) bounds none :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (right.forgetComparison bounds).inv L ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (right.filtered bounds)
      (left.forgetComparison bounds).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (adj bounds).counit
      (finiteFilteredDerivedEvaluation (C := A) bounds none) ≫
    (Functor.leftUnitor _).hom

/-- Transport the graded unit through the graded comparison isomorphisms.
Source: Varshavsky, Section 5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
def filteredUnitGradedTransport
    (left : FilteredDerivedOperationLift L)
    (right : FilteredDerivedOperationLift T)
    (adj : ∀ bounds : Option (ℤ × ℤ),
      (left.filtered bounds) ⊣ (right.filtered bounds))
    (bounds : Option (ℤ × ℤ)) (r : ℤ) :
    finiteFilteredDerivedEvaluation (C := B) bounds (some r) ⟶
      finiteFilteredDerivedEvaluation (C := B) bounds (some r) ⋙ (L ⋙ T) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (adj bounds).unit
      (finiteFilteredDerivedEvaluation (C := B) bounds (some r)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (left.filtered bounds)
      (right.gradedComparison bounds r).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (left.gradedComparison bounds r).hom T ≫
    (Functor.associator _ _ _).hom

/-- Transport the graded counit through the graded comparison isomorphisms.
Source: Varshavsky, Section 5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
def filteredCounitGradedTransport
    (left : FilteredDerivedOperationLift L)
    (right : FilteredDerivedOperationLift T)
    (adj : ∀ bounds : Option (ℤ × ℤ),
      (left.filtered bounds) ⊣ (right.filtered bounds))
    (bounds : Option (ℤ × ℤ)) (r : ℤ) :
    finiteFilteredDerivedEvaluation (C := A) bounds (some r) ⋙ (T ⋙ L) ⟶
      finiteFilteredDerivedEvaluation (C := A) bounds (some r) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (right.gradedComparison bounds r).inv L ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (right.filtered bounds)
      (left.gradedComparison bounds r).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (adj bounds).counit
      (finiteFilteredDerivedEvaluation (C := A) bounds (some r)) ≫
    (Functor.leftUnitor _).hom

/-- A filtered adjunction with actual unit/counit equations after forgetting and grading.
Source: Varshavsky, Section 5.2.2 and Stacks, Tag 05TY
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
structure FilteredDerivedAdjunction
    (ordinaryAdjunction : L ⊣ T)
    (left : FilteredDerivedOperationLift L)
    (right : FilteredDerivedOperationLift T) where
  filteredAdjunction : ∀ (bounds : Option (ℤ × ℤ)),
    (left.filtered bounds) ⊣ (right.filtered bounds)
  unitForget : ∀ (bounds : Option (ℤ × ℤ)),
    filteredUnitForgetTransport left right filteredAdjunction bounds =
      Functor.whiskerLeft
        (finiteFilteredDerivedEvaluation (C := B) bounds none)
        ordinaryAdjunction.unit
  counitForget : ∀ (bounds : Option (ℤ × ℤ)),
    filteredCounitForgetTransport left right filteredAdjunction bounds =
      Functor.whiskerLeft
        (finiteFilteredDerivedEvaluation (C := A) bounds none)
        ordinaryAdjunction.counit
  unitGraded : ∀ (bounds : Option (ℤ × ℤ)) (r : ℤ),
    filteredUnitGradedTransport left right filteredAdjunction bounds r =
      Functor.whiskerLeft
        (finiteFilteredDerivedEvaluation (C := B) bounds (some r))
        ordinaryAdjunction.unit
  counitGraded : ∀ (bounds : Option (ℤ × ℤ)) (r : ℤ),
    filteredCounitGradedTransport left right filteredAdjunction bounds r =
      Functor.whiskerLeft
        (finiteFilteredDerivedEvaluation (C := A) bounds (some r))
        ordinaryAdjunction.counit

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare

universe u w₁ v₁ w₂ v₂

/-- A comparison of compact-support formalisms, including the pseudofunctor and both
adjunction normalizations. The named maps of `CompactSupportFormalism` are composites
of these generators, so this data compares their actual formulas.
Source: Varshavsky §§5.2.1–5.2.2 and Stacks Tags 015U, 015V
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
structure FilteredOperationComparison
    (F : CompactSupportFormalism.{w₁, v₁, u})
    (G : CompactSupportFormalism.{w₂, v₂, u})
    (E : ∀ X : Scheme.{u}, F.obj X ⥤ G.obj X) where
  pb : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), F.pb f ⋙ E X ≅ E Y ⋙ G.pb f
  pf : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), F.pf f ⋙ E Y ≅ E X ⋙ G.pf f
  sh : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j],
    F.sh j ⋙ E Y ≅ E X ⋙ G.sh j
  pbId : ∀ (X : Scheme.{u}) (M : F.obj X),
    (E X).map ((F.pbId X).hom.app M) =
      (pb (𝟙 X)).hom.app M ≫ (G.pbId X).hom.app ((E X).obj M)
  pbComp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : F.obj Z),
    (E X).map ((F.pbComp f g).hom.app M) ≫
        (pb f).hom.app ((F.pb g).obj M) ≫ (G.pb f).map ((pb g).hom.app M) =
      (pb (f ≫ g)).hom.app M ≫ (G.pbComp f g).hom.app ((E Z).obj M)
  unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : F.obj Y),
    (E Y).map ((F.adj f).unit.app M) ≫
        (pf f).hom.app ((F.pb f).obj M) ≫ (G.pf f).map ((pb f).hom.app M) =
      (G.adj f).unit.app ((E Y).obj M)
  counit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : F.obj X),
    (G.pb f).map ((pf f).inv.app M) ≫
        (pb f).inv.app ((F.pf f).obj M) ≫ (E X).map ((F.adj f).counit.app M) =
      (G.adj f).counit.app ((E X).obj M)
  openUnit : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (M : F.obj X),
    (E X).map ((F.shAdj j).unit.app M) ≫
        (pb j).hom.app ((F.sh j).obj M) ≫ (G.pb j).map ((sh j).hom.app M) =
      (G.shAdj j).unit.app ((E X).obj M)
  openCounit : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (M : F.obj Y),
    (G.sh j).map ((pb j).inv.app M) ≫
        (sh j).inv.app ((F.pb j).obj M) ≫ (E Y).map ((F.shAdj j).counit.app M) =
      (G.shAdj j).counit.app ((E Y).obj M)

namespace ProEtale

variable (R : Type u) [CommRing R] [Finite R]

/-- The fixed-scalar coordinates of modules over the canonical constant ring sheaf.
The equivalence `Scheme.sfIntrinsicModuleEquivalence X R` is the recorded realization
of these sheaves as intrinsic module sheaves, including their scalar action.
Source: def-weil-pbc-proetale-operations, def-weil-extension-by-zero, Stacks Tag 00YV
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
abbrev FilteredOperationCoefficients (X : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} R))

/-- The canonical derived pullback-composition comparison in fixed-scalar coordinates.
Source: Stacks Tag 04J0, exact termwise descent
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def filteredOperationPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Functor.mapDerivedCategoryPlusNatIso
      (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f g) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical derived identity comparison, with its sheaf identity normalization.
Source: Stacks Tag 04J0 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
def filteredOperationPullbackId (X : Scheme.{u}) :=
  Functor.mapDerivedCategoryPlusNatIso
      (upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- Coherence witnesses for the displayed, fixed canonical pullback comparisons.
These are proof fields about the explicit constructions, not new choices of maps.
Source: Stacks Tag 04J0, Varshavsky §5.2.2
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
structure FilteredOperationOrdinaryCoherence where
  assoc : ∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : DerivedCategory.Plus (FilteredOperationCoefficients R W)),
    (filteredOperationPullbackComp R (f ≫ g) h).hom.app M ≫
        (filteredOperationPullbackComp R f g).hom.app
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) h).mapDerivedCategoryPlus.obj M) =
      eqToHom (by rw [Category.assoc]) ≫
        (filteredOperationPullbackComp R f (g ≫ h)).hom.app M ≫
          (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f).mapDerivedCategoryPlus.map
            ((filteredOperationPullbackComp R g h).hom.app M)
  id_comp : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory.Plus (FilteredOperationCoefficients R Y)),
    (filteredOperationPullbackComp R (𝟙 X) f).hom.app M ≫
        (filteredOperationPullbackId R X).hom.app
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f).mapDerivedCategoryPlus.obj M) =
      eqToHom (by simp)
  comp_id : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory.Plus (FilteredOperationCoefficients R Y)),
    (filteredOperationPullbackComp R f (𝟙 Y)).hom.app M ≫
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f).mapDerivedCategoryPlus.map
          ((filteredOperationPullbackId R Y).hom.app M) = eqToHom (by simp)

/-- The concrete ordinary formalism. In particular its compactification functor is
literally `D⁺j_! ⋙ R⁺p_*`, the bounded-below candidate of the recorded definition.
Source: def-weil-compact-support-candidate and Varshavsky §5.2.2
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def filteredOperationOrdinaryFormalism (h : FilteredOperationOrdinaryCoherence R) :
    CompactSupportFormalism where
  obj X := DerivedCategory.Plus (FilteredOperationCoefficients R X)
  pb f := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f).mapDerivedCategoryPlus
  pbId := filteredOperationPullbackId R
  pbComp := filteredOperationPullbackComp R
  pbComp_assoc := h.assoc
  pbId_comp := h.id_comp
  pbComp_id := h.comp_id
  pf f := (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f).rightDerivedFunctorPlus
  adj f := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f).derivedPlus
  sh j _ :=
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j).mapDerivedCategoryPlus
  shAdj j _ := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j).derivedPlus.ofNatIsoRight
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j))

end ProEtale
end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] [Finite R]

/-- Filtered lifts of the actual coefficient operations on every scheme. The only
comparison choices here are pullback identity/composition maps; their normalization
is imposed by `FilteredOperationComparison` in the theorem. Pushforward, open,
proper and compactification maps are then the canonical mate constructions of the
resulting `CompactSupportFormalism`, not independently supplied transformations.
Source: Varshavsky §§5.2.1–5.2.2, Stacks Tags 015Q and 05TY
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
structure ProEtaleFilteredOperationData where
  pullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    FilteredTermwiseLift (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f)
  pushforward : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    FilteredDerivedOperationLift
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f).rightDerivedFunctorPlus
  openExtension : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j],
    FilteredTermwiseLift (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j)
  adjunction : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    FilteredDerivedAdjunction
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f).derivedPlus
      (pullback f).toFilteredDerivedOperationLift (pushforward f)
  openAdjunction : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j],
    FilteredDerivedAdjunction
      ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j).derivedPlus.ofNatIsoRight
        (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
          (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j)))
      (openExtension j).toFilteredDerivedOperationLift
      (pullback j).toFilteredDerivedOperationLift
  pullbackId : ∀ (bounds : Option (ℤ × ℤ)) (X : Scheme.{u}),
    (pullback (𝟙 X)).filtered bounds ≅ 𝟭 _
  pullbackComp : ∀ (bounds : Option (ℤ × ℤ)) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z),
    (pullback (f ≫ g)).filtered bounds ≅
      (pullback g).filtered bounds ⋙ (pullback f).filtered bounds
  pullback_assoc : ∀ (bounds : Option (ℤ × ℤ)) {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : FiniteFilteredDerivedPlus (C := FilteredOperationCoefficients R W) bounds),
    (pullbackComp bounds (f ≫ g) h).hom.app M ≫
        (pullbackComp bounds f g).hom.app ((pullback h).filtered bounds |>.obj M) =
      eqToHom (by rw [Category.assoc]) ≫
        (pullbackComp bounds f (g ≫ h)).hom.app M ≫
          ((pullback f).filtered bounds).map ((pullbackComp bounds g h).hom.app M)
  pullback_id_comp : ∀ (bounds : Option (ℤ × ℤ)) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : FiniteFilteredDerivedPlus (C := FilteredOperationCoefficients R Y) bounds),
    (pullbackComp bounds (𝟙 X) f).hom.app M ≫
        (pullbackId bounds X).hom.app (((pullback f).filtered bounds).obj M) =
      eqToHom (congrArg (fun k : X ⟶ Y ↦ ((pullback k).filtered bounds).obj M)
        (Category.id_comp f))
  pullback_comp_id : ∀ (bounds : Option (ℤ × ℤ)) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : FiniteFilteredDerivedPlus (C := FilteredOperationCoefficients R Y) bounds),
    (pullbackComp bounds f (𝟙 Y)).hom.app M ≫
        ((pullback f).filtered bounds).map ((pullbackId bounds Y).hom.app M) =
      eqToHom (congrArg (fun k : X ⟶ Y ↦ ((pullback k).filtered bounds).obj M)
        (Category.comp_id f))

/-- The filtered formalism built from the preceding termwise/resolution lifts.
In particular its adjunction maps are the filtered units and counits just specified.
Source: Varshavsky §5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
def ProEtaleFilteredOperationData.toFormalism (D : ProEtaleFilteredOperationData R)
    (bounds : Option (ℤ × ℤ)) : CompactSupportFormalism where
  obj X := FiniteFilteredDerivedPlus (C := FilteredOperationCoefficients R X) bounds
  pb f := (D.pullback f).filtered bounds
  pbId := D.pullbackId bounds
  pbComp := D.pullbackComp bounds
  pbComp_assoc := D.pullback_assoc bounds
  pbId_comp := D.pullback_id_comp bounds
  pbComp_id := D.pullback_comp_id bounds
  pf f := (D.pushforward f).filtered bounds
  adj f := (D.adjunction f).filteredAdjunction bounds
  sh j _ := (D.openExtension j).filtered bounds
  shAdj j _ := (D.openAdjunction j).filteredAdjunction bounds

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u w v

/-- Finite expressions in the actual pullback, pushforward and open-extension functors.
Source: Varshavsky §5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
inductive FilteredOperation : Scheme.{u} → Scheme.{u} → Type (u + 1)
  | id (X : Scheme.{u}) : FilteredOperation X X
  | pb {X Y : Scheme.{u}} (f : X ⟶ Y) : FilteredOperation Y X
  | pf {X Y : Scheme.{u}} (f : X ⟶ Y) : FilteredOperation X Y
  | sh {X Y : Scheme.{u}} (j : X ⟶ Y) (hj : IsOpenImmersion j) : FilteredOperation X Y
  | comp {X Y Z : Scheme.{u}} (F : FilteredOperation X Y) (G : FilteredOperation Y Z) :
      FilteredOperation X Z

/-- Evaluation of an operation expression; the compactification expression is `sh j; pf p`.
Source: Varshavsky §5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
def FilteredOperation.eval (F : CompactSupportFormalism.{w, v, u})
    {X Y : Scheme.{u}} : FilteredOperation X Y → (F.obj X ⥤ F.obj Y)
  | .id _ => 𝟭 _
  | .pb f => F.pb f
  | .pf f => F.pf f
  | .sh j hj => letI := hj; F.sh j
  | .comp a b => a.eval F ⋙ b.eval F

/-- The reverse adjunction for a clopen immersion, canonically normalized by the
open-extension adjunction: its counit is the inverse of the latter's unit. This
normalization determines the adjunction and its projection unit uniquely, so it is
not a free choice of a natural transformation.
Source: Stacks, Tags 03DI and 0F7B, node proof Step 6
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
class FilteredOperationClopen (F : CompactSupportFormalism.{w, v, u}) where
  adjunction : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    IsClosed (Set.range j.base) → (F.pb j ⊣ F.sh j)
  unit_counit : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (hc : IsClosed (Set.range j.base)),
    (F.shAdj j).unit ≫ (adjunction j hc).counit = 𝟙 _
  counit_unit : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (hc : IsClosed (Set.range j.base)),
    (adjunction j hc).counit ≫ (F.shAdj j).unit = 𝟙 _

/-- The actual proper/open mate for a square factored through its Cartesian pullback
and a clopen section `s`. The intermediate map inserts the normalized clopen projection
`id → s^* ⋙ s_!`, and then uses the canonical pullback/open composition comparisons.
For `s = id` this is the ordinary Cartesian proper/open comparison; for a refinement
it is the projection onto the clopen section, followed by the proper-adjunction mate.
Source: Stacks, Tags 0F7B–0F7F; node proof Step 6
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def CompactSupportFormalism.filteredOperationProperOpen
    (F : CompactSupportFormalism.{w, v, u}) [F.HasBaseChange] [FilteredOperationClopen F]
    {U V S T P : Scheme.{u}} (k : U ⟶ V) (i : S ⟶ T) (r : U ⟶ S) (p : V ⟶ T)
    (b : P ⟶ V) (q : P ⟶ S) (s : U ⟶ P)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    [IsOpenImmersion b] [IsOpenImmersion s]
    (sq : IsPullback q b i p) (hc : IsClosed (Set.range s.base))
    (hsb : s ≫ b = k) (hsq : s ≫ q = r) :
    F.pf r ⋙ F.sh i ⟶ F.sh k ⋙ F.pf p :=
  letI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
  let projection := (FilteredOperationClopen.adjunction (F := F) s hc).unit
  let alpha : F.sh i ⋙ F.pb p ⟶ F.pb r ⋙ F.sh k :=
    inv (F.baseChange q b i p sq.w).natTrans ≫
      Functor.whiskerLeft (F.pb q)
        ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight projection (F.sh b) ≫
          (Functor.associator _ _ _).hom ≫
            Functor.whiskerLeft (F.pb s) (F.shComp' s b k hsb).inv) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (F.pbComp' s q r hsq).inv (F.sh k)
  CategoryTheory.mateEquiv (F.adj r) (F.adj p) alpha

/-- The geometric factorization of a refinement through the pullback of its open
immersion. The section is clopen; the pullback object and every arrow are supplied,
with their universal property and factorization equations, not arbitrary sheaf maps.
Source: Stacks, Tag 0F7B; node proof Step 6
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
structure FilteredRefinementFactorization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) where
  P : Scheme.{u}
  b : P ⟶ c.Z
  q : P ⟶ X
  s : X ⟶ P
  [open_b : IsOpenImmersion b]
  [open_s : IsOpenImmersion s]
  square : IsPullback q b d.i r.hom
  closed : IsClosed (Set.range s.base)
  sb : s ≫ b = c.i
  sq : s ≫ q = 𝟙 X

attribute [instance] FilteredRefinementFactorization.open_b
  FilteredRefinementFactorization.open_s

/-- The actual refinement comparison, including non-Cartesian refinements: insert
`(id)_*`, apply the normalized clopen-section proper/open mate, then compose proper
pushforwards. Its inverse is used only on the specified admissible domains.
Source: Stacks, Tags 0F7B and 0F7F; node proof Steps 6–7
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def CompactSupportFormalism.filteredOperationRefinement
    (F : CompactSupportFormalism.{w, v, u}) [F.HasBaseChange] [FilteredOperationClopen F]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (S : FilteredRefinementFactorization r) :
    F.shriek d ⟶ F.shriek c :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (F.pfId X).inv (F.shriek d) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (F.filteredOperationProperOpen c.i d.i (𝟙 X) r.hom S.b S.q S.s
        S.square S.closed S.sb S.sq) (F.pf d.g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.sh c.i) (F.pfComp' r.hom d.g c.g r.hom_g).inv

/-- The actual compactification composition arrow before asserting invertibility.
This is the formula of `compIso`, retaining only the open-base-change hypothesis;
thus it can be used on the full bounded-below categories. On admissible domains its
ordinary inverse gives the usual compactification composition isomorphism.
Source: Varshavsky §5.2.2, node proof Step 7
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def CompactSupportFormalism.filteredOperationCompositionMap
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (F : CompactSupportFormalism.{w, v, u}) [F.HasBaseChange]
    (T : Compactification.Triangle f g) : F.shriek T.cf ⋙ F.shriek T.cg ⟶ F.shriek T.cfg :=
  letI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) T.isPullback
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.sh T.cf.i)
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (F.exchange T.cf.g T.q T.cg.i T.p T.isPullback.w).natTrans (F.pf T.cg.g) ≫
        (Functor.associator _ _ _).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (F.shComp' T.cf.i T.q T.cfg.i T.i_q).inv _ ≫
    Functor.whiskerLeft _ (F.pfComp' T.p T.cg.g T.cfg.g T.p_g).inv

/-- The canonical maps are generated by identity/composition comparisons, adjunctions,
and the canonical open/proper square mates. No constructor takes an arbitrary derived
natural transformation. Inverses of other expressions are used only when the ordinary
map is invertible on the domain under consideration.
Source: Varshavsky §5.2.2, Stacks Tags 03S6 and 05TY
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
inductive FilteredCanonicalMap : {X Y : Scheme.{u}} →
    FilteredOperation X Y → FilteredOperation X Y → Type (u + 1)
  | id {X Y : Scheme.{u}} (a : FilteredOperation X Y) : FilteredCanonicalMap a a
  | comp {X Y : Scheme.{u}} {a b c : FilteredOperation X Y}
      (h : FilteredCanonicalMap a b) (k : FilteredCanonicalMap b c) : FilteredCanonicalMap a c
  | left {X Y Z : Scheme.{u}} (a : FilteredOperation X Y)
      {b c : FilteredOperation Y Z} (h : FilteredCanonicalMap b c) :
      FilteredCanonicalMap (.comp a b) (.comp a c)
  | right {X Y Z : Scheme.{u}} {a b : FilteredOperation X Y}
      (h : FilteredCanonicalMap a b) (c : FilteredOperation Y Z) :
      FilteredCanonicalMap (.comp a c) (.comp b c)
  | assoc {W X Y Z : Scheme.{u}} (a : FilteredOperation W X)
      (b : FilteredOperation X Y) (c : FilteredOperation Y Z) :
      FilteredCanonicalMap (.comp (.comp a b) c) (.comp a (.comp b c))
  | assocInv {W X Y Z : Scheme.{u}} (a : FilteredOperation W X)
      (b : FilteredOperation X Y) (c : FilteredOperation Y Z) :
      FilteredCanonicalMap (.comp a (.comp b c)) (.comp (.comp a b) c)
  | eq {X Y : Scheme.{u}} {a b : FilteredOperation X Y} (h : a = b) :
      FilteredCanonicalMap a b
  | leftUnitor {X Y : Scheme.{u}} (a : FilteredOperation X Y) :
      FilteredCanonicalMap (.comp (.id X) a) a
  | leftUnitorInv {X Y : Scheme.{u}} (a : FilteredOperation X Y) :
      FilteredCanonicalMap a (.comp (.id X) a)
  | rightUnitor {X Y : Scheme.{u}} (a : FilteredOperation X Y) :
      FilteredCanonicalMap (.comp a (.id Y)) a
  | rightUnitorInv {X Y : Scheme.{u}} (a : FilteredOperation X Y) :
      FilteredCanonicalMap a (.comp a (.id Y))
  | pbComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
      FilteredCanonicalMap (.pb (f ≫ g)) (.comp (.pb g) (.pb f))
  | pbCompInv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
      FilteredCanonicalMap (.comp (.pb g) (.pb f)) (.pb (f ≫ g))
  | pfComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
      FilteredCanonicalMap (.pf (f ≫ g)) (.comp (.pf f) (.pf g))
  | pfCompInv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
      FilteredCanonicalMap (.comp (.pf f) (.pf g)) (.pf (f ≫ g))
  | shComp {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
      (hi : IsOpenImmersion i) (hj : IsOpenImmersion j) :
      FilteredCanonicalMap
        (.sh (i ≫ j) (by have := hi; have := hj; infer_instance)) (.comp (.sh i hi) (.sh j hj))
  | shCompInv {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
      (hi : IsOpenImmersion i) (hj : IsOpenImmersion j) :
      FilteredCanonicalMap (.comp (.sh i hi) (.sh j hj))
        (.sh (i ≫ j) (by have := hi; have := hj; infer_instance))
  | unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
      FilteredCanonicalMap (.id Y) (.comp (.pb f) (.pf f))
  | counit {X Y : Scheme.{u}} (f : X ⟶ Y) :
      FilteredCanonicalMap (.comp (.pf f) (.pb f)) (.id X)
  | openUnit {X Y : Scheme.{u}} (j : X ⟶ Y) (hj : IsOpenImmersion j) :
      FilteredCanonicalMap (.id X) (.comp (.sh j hj) (.pb j))
  | openCounit {X Y : Scheme.{u}} (j : X ⟶ Y) (hj : IsOpenImmersion j) :
      FilteredCanonicalMap (.comp (.pb j) (.sh j hj)) (.id Y)
  | pbId (X : Scheme.{u}) : FilteredCanonicalMap (.pb (𝟙 X)) (.id X)
  | pfId (X : Scheme.{u}) : FilteredCanonicalMap (.pf (𝟙 X)) (.id X)
  | shId (X : Scheme.{u}) : FilteredCanonicalMap (.sh (𝟙 X) (by infer_instance)) (.id X)
  | pbIdInv (X : Scheme.{u}) : FilteredCanonicalMap (.id X) (.pb (𝟙 X))
  | pfIdInv (X : Scheme.{u}) : FilteredCanonicalMap (.id X) (.pf (𝟙 X))
  | shIdInv (X : Scheme.{u}) :
      FilteredCanonicalMap (.id X) (.sh (𝟙 X) (by infer_instance))
  | clopenProjection {U X : Scheme.{u}} (j : U ⟶ X) (hj : IsOpenImmersion j)
      (hc : IsClosed (Set.range j.base)) :
      FilteredCanonicalMap (.id X) (.comp (.pb j) (.sh j hj))
  | properOpen {U V S T P : Scheme.{u}}
      (k : U ⟶ V) (i : S ⟶ T) (r : U ⟶ S) (p : V ⟶ T)
      (b : P ⟶ V) (q : P ⟶ S) (s : U ⟶ P)
      (hk : IsOpenImmersion k) (hi : IsOpenImmersion i)
      (hr : IsProper r) (hp : IsProper p)
      (hb : IsOpenImmersion b) (hs : IsOpenImmersion s)
      (sq : IsPullback q b i p) (hc : IsClosed (Set.range s.base))
      (hsb : s ≫ b = k) (hsq : s ≫ q = r) :
      FilteredCanonicalMap (.comp (.pf r) (.sh i hi)) (.comp (.sh k hk) (.pf p))
  | refinement {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
      (r : c.Refinement d) (S : FilteredRefinementFactorization r) :
      FilteredCanonicalMap (.comp (.sh d.i d.isOpenImmersion) (.pf d.g))
        (.comp (.sh c.i c.isOpenImmersion) (.pf c.g))
  | compactificationComposition {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
      (T : Compactification.Triangle f g) :
      FilteredCanonicalMap
        (.comp (.comp (.sh T.cf.i T.cf.isOpenImmersion) (.pf T.cf.g))
          (.comp (.sh T.cg.i T.cg.isOpenImmersion) (.pf T.cg.g)))
        (.comp (.sh T.cfg.i T.cfg.isOpenImmersion) (.pf T.cfg.g))
  | compactificationExchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (gX : X' ⟶ X) (gY : Y' ⟶ Y) (c : Compactification f) (c' : Compactification f')
      (h : c'.Z ⟶ c.Z) (hi : IsPullback gX c'.i c.i h)
      (hp : IsPullback h c'.g c.g gY) :
      FilteredCanonicalMap (.comp (.comp (.sh c.i c.isOpenImmersion) (.pf c.g)) (.pb gY))
        (.comp (.pb gX) (.comp (.sh c'.i c'.isOpenImmersion) (.pf c'.g)))
  | properSquare {U' U Z' Z : Scheme.{u}} (t : U' ⟶ U) (l : U' ⟶ Z')
      (r : U ⟶ Z) (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b) :
      FilteredCanonicalMap (.comp (.pf r) (.pb b)) (.comp (.pb t) (.pf l))
  | openSquare {U' U Z' Z : Scheme.{u}} (t : U' ⟶ U) (l : U' ⟶ Z')
      (r : U ⟶ Z) (b : Z' ⟶ Z) (hl : IsOpenImmersion l) (hr : IsOpenImmersion r)
      (sq : IsPullback t l r b) :
      FilteredCanonicalMap (.comp (.pb t) (.sh l hl)) (.comp (.sh r hr) (.pb b))
  | openSquareInv {U' U Z' Z : Scheme.{u}} (t : U' ⟶ U) (l : U' ⟶ Z')
      (r : U ⟶ Z) (b : Z' ⟶ Z) (hl : IsOpenImmersion l) (hr : IsOpenImmersion r)
      (sq : IsPullback t l r b) :
      FilteredCanonicalMap (.comp (.sh r hr) (.pb b)) (.comp (.pb t) (.sh l hl))

/-- Evaluate a canonical expression by the existing mate constructions. In particular
`properSquare` is exactly the unit–square–counit mate, and `openSquare` is the open mate.
Source: Varshavsky §5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts). -/
def FilteredCanonicalMap.eval (F : CompactSupportFormalism.{w, v, u}) [F.HasBaseChange]
    [FilteredOperationClopen F]
    {X Y : Scheme.{u}} {a b : FilteredOperation X Y} :
    FilteredCanonicalMap a b → (a.eval F ⟶ b.eval F)
  | .id _ => 𝟙 _
  | .comp h k => h.eval F ≫ k.eval F
  | .left a h => Functor.whiskerLeft (a.eval F) (h.eval F)
  | .right h c => Functor.whiskerRight (h.eval F) (c.eval F)
  | .assoc _ _ _ => (Functor.associator _ _ _).hom
  | .assocInv _ _ _ => (Functor.associator _ _ _).inv
  | .eq h => eqToHom (congrArg (FilteredOperation.eval F) h)
  | .leftUnitor _ => (Functor.leftUnitor _).hom
  | .leftUnitorInv _ => (Functor.leftUnitor _).inv
  | .rightUnitor _ => (Functor.rightUnitor _).hom
  | .rightUnitorInv _ => (Functor.rightUnitor _).inv
  | .pbComp f g => (F.pbComp f g).hom
  | .pbCompInv f g => (F.pbComp f g).inv
  | .pfComp f g => (F.pfComp' f g (f ≫ g) rfl).hom
  | .pfCompInv f g => (F.pfComp' f g (f ≫ g) rfl).inv
  | .shComp i j hi hj => letI := hi; letI := hj; (F.shComp' i j (i ≫ j) rfl).hom
  | .shCompInv i j hi hj => letI := hi; letI := hj; (F.shComp' i j (i ≫ j) rfl).inv
  | .unit f => (F.adj f).unit
  | .counit f => (F.adj f).counit
  | .openUnit j hj => letI := hj; (F.shAdj j).unit
  | .openCounit j hj => letI := hj; (F.shAdj j).counit
  | .pbId X => (F.pbId X).hom
  | .pfId X => (F.pfId X).hom
  | .shId X => (F.shId X).hom
  | .pbIdInv X => (F.pbId X).inv
  | .pfIdInv X => (F.pfId X).inv
  | .shIdInv X => (F.shId X).inv
  | .clopenProjection j hj hc =>
      letI := hj; (FilteredOperationClopen.adjunction (F := F) j hc).unit
  | .properOpen k i r p b q s hk hi hr hp hb hs sq hc hsb hsq =>
      letI := hk; letI := hi; letI := hr; letI := hp; letI := hb; letI := hs
      F.filteredOperationProperOpen k i r p b q s sq hc hsb hsq
  | .refinement r S => F.filteredOperationRefinement r S
  | .compactificationComposition T => F.filteredOperationCompositionMap T
  | .compactificationExchange _ _ c c' h hi hp =>
      (F.shriekBaseChange c c' h hi hp).natTrans
  | .properSquare t l r b w => (F.pfBaseChange t l r b w).natTrans
  | .openSquare t l r b hl hr sq =>
      letI := hl; letI := hr; (F.baseChange t l r b sq.w).natTrans
  | .openSquareInv t l r b hl hr sq =>
      letI := hl; letI := hr
      letI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
      inv (F.baseChange t l r b sq.w).natTrans

end AlgebraicGeometry

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare

universe u w₁ v₁ w₂ v₂

/-- Compose the primitive comparison isomorphisms using the actual functor associators.
Source: Varshavsky §§5.1.3, 5.2.2
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def FilteredOperationComparison.operation
    {F : CompactSupportFormalism.{w₁, v₁, u}} {G : CompactSupportFormalism.{w₂, v₂, u}}
    {E : ∀ X : Scheme.{u}, F.obj X ⥤ G.obj X} (C : FilteredOperationComparison F G E)
    {X Y : Scheme.{u}} (a : FilteredOperation X Y) : a.eval F ⋙ E Y ≅ E X ⋙ a.eval G :=
  match a with
  | .id X => Functor.leftUnitor (E X) ≪≫ (Functor.rightUnitor (E X)).symm
  | .pb f => C.pb f
  | .pf f => C.pf f
  | .sh j hj => letI := hj; C.sh j
  | .comp a b =>
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (a.eval F) (C.operation b) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (C.operation a) (b.eval G) ≪≫ Functor.associator _ _ _

/-- Every canonical expression has exactly its ordinary forgetful/graded map. This
predicate quantifies only the explicitly generated canonical expressions; the maps are
computed by `FilteredCanonicalMap.eval`, with no free exchange-map field.
Source: Varshavsky Lemma 5.1.4 and §5.2.2
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def FilteredOperationComparison.RespectsCanonicalMaps
    {F : CompactSupportFormalism.{w₁, v₁, u}} {G : CompactSupportFormalism.{w₂, v₂, u}}
    [F.HasBaseChange] [G.HasBaseChange]
    [FilteredOperationClopen F] [FilteredOperationClopen G]
    {E : ∀ X : Scheme.{u}, F.obj X ⥤ G.obj X} (C : FilteredOperationComparison F G E) : Prop :=
  ∀ {X Y : Scheme.{u}} {a b : FilteredOperation X Y} (h : FilteredCanonicalMap a b)
    (M : F.obj X),
    (E Y).map ((h.eval F).app M) ≫ (C.operation b).hom.app M =
      (C.operation a).hom.app M ≫ (h.eval G).app ((E X).obj M)

namespace CompactSupportFormalism

universe w v

variable (F : CompactSupportFormalism.{w, v, u}) [F.HasBaseChange]

/-- Vertical pasting for actual compactification exchanges and actual composition arrows.
All six compactifications and their comparison maps are supplied. The two tower squares
commute, and the six displayed squares are Cartesian. No map is an arbitrary parameter.
Inverting the composition arrows on an admissible domain yields the equation in the node.
Source: Varshavsky §5.2.2, node proof Steps 6–7
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def FilteredOperationVerticalPasting : Prop :=
  ∀ {W X Y W' X' Y' : Scheme.{u}} {e : W ⟶ X} {f : X ⟶ Y}
    {e' : W' ⟶ X'} {f' : X' ⟶ Y'}
    (gW : W' ⟶ W) (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    (T : Compactification.Triangle e f) (T' : Compactification.Triangle e' f')
    (hE : T'.cf.Z ⟶ T.cf.Z) (hF : T'.cg.Z ⟶ T.cg.Z) (hEF : T'.cfg.Z ⟶ T.cfg.Z)
    (hiE : IsPullback gW T'.cf.i T.cf.i hE)
    (hpE : IsPullback hE T'.cf.g T.cf.g gX)
    (hiF : IsPullback gX T'.cg.i T.cg.i hF)
    (hpF : IsPullback hF T'.cg.g T.cg.g gY)
    (hiEF : IsPullback gW T'.cfg.i T.cfg.i hEF)
    (hpEF : IsPullback hEF T'.cfg.g T.cfg.g gY),
    hE ≫ T.q = T'.q ≫ hEF → hEF ≫ T.p = T'.p ≫ hF →
    Functor.whiskerRight (F.filteredOperationCompositionMap T) (F.pb gY) ≫
        (F.shriekBaseChange T.cfg T'.cfg hEF hiEF hpEF).natTrans =
      ((F.shriekBaseChange T.cf T'.cf hE hiE hpE) ≫ₕ
        (F.shriekBaseChange T.cg T'.cg hF hiF hpF)).natTrans ≫
          Functor.whiskerLeft (F.pb gW) (F.filteredOperationCompositionMap T')

/-- Refinements intertwine the actual compactification exchanges. This includes
non-Cartesian refinement squares, using the clopen-section formula just defined.
Combined with vertical pasting, it gives exactly the refinement-compatible equation
of the node after inserting the admissible composition/refinement isomorphisms.
Source: Stacks, Tags 0F7F and 0F7J; node proof Step 7
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
def FilteredOperationRefinementPasting [FilteredOperationClopen F] : Prop :=
  ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) {c d : Compactification f}
    {c' d' : Compactification f'} (r : c.Refinement d) (r' : c'.Refinement d')
    (S : FilteredRefinementFactorization r) (S' : FilteredRefinementFactorization r')
    (hc : c'.Z ⟶ c.Z) (hci : IsPullback gX c'.i c.i hc)
    (hcp : IsPullback hc c'.g c.g gY)
    (hd : d'.Z ⟶ d.Z) (hdi : IsPullback gX d'.i d.i hd)
    (hdp : IsPullback hd d'.g d.g gY),
    hc ≫ r.hom = r'.hom ≫ hd →
    Functor.whiskerRight (F.filteredOperationRefinement r S) (F.pb gY) ≫
        (F.shriekBaseChange c c' hc hci hcp).natTrans =
      (F.shriekBaseChange d d' hd hdi hdp).natTrans ≫
        Functor.whiskerLeft (F.pb gX) (F.filteredOperationRefinement r' S')

end CompactSupportFormalism
end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] [Finite R]

/-- The complete specialization package. The ordinary formalism is fixed by the concrete
sheaf operations and their canonical adjunctions. Every comparison map is normalized
on the supplied operation lifts. Compactification candidates, canonical expressions and
vertical pasting consequently refer to the actual maps of these two formalisms.
Source: Varshavsky Lemma 5.1.4 and §§5.2.1–5.2.2, Stacks Tags 015Q–015V
(blueprint: lem-trf-filtered-derived-operation-lifts). -/
structure ProEtaleFilteredOperationPackage where
  intrinsicPullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Scheme.sfIntrinsicTransport R (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f) ≅
      Scheme.proEtaleConstantRingPullback R f
  intrinsicPushforward : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Scheme.sfIntrinsicTransport R (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f) ≅
      Scheme.proEtaleConstantRingPushforward R f
  intrinsicOpen : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j],
    Scheme.sfIntrinsicTransport R
      (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j) =
      Scheme.sfIntrinsicExtensionByZero j R
  ordinaryCoherence : FilteredOperationOrdinaryCoherence R
  data : ProEtaleFilteredOperationData R
  ordinaryBaseChange : (filteredOperationOrdinaryFormalism R ordinaryCoherence).HasBaseChange
  filteredBaseChange : ∀ bounds : Option (ℤ × ℤ), (data.toFormalism R bounds).HasBaseChange
  ordinaryClopen : FilteredOperationClopen
    (filteredOperationOrdinaryFormalism R ordinaryCoherence)
  filteredClopen : ∀ bounds : Option (ℤ × ℤ),
    FilteredOperationClopen (data.toFormalism R bounds)
  comparison : ∀ (bounds : Option (ℤ × ℤ)) (p : Option ℤ),
    FilteredOperationComparison (data.toFormalism R bounds)
      (filteredOperationOrdinaryFormalism R ordinaryCoherence)
      (fun X : Scheme.{u} ↦
        finiteFilteredDerivedEvaluation (C := FilteredOperationCoefficients R X) bounds p)
  pullbackForget : ∀ (bounds : Option (ℤ × ℤ)) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (comparison bounds none).pb f = (data.pullback f).forgetComparison bounds
  pullbackGraded : ∀ (bounds : Option (ℤ × ℤ)) (r : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (comparison bounds (some r)).pb f = (data.pullback f).gradedComparison bounds r
  pushforwardForget : ∀ (bounds : Option (ℤ × ℤ)) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (comparison bounds none).pf f = (data.pushforward f).forgetComparison bounds
  pushforwardGraded : ∀ (bounds : Option (ℤ × ℤ)) (r : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y),
    (comparison bounds (some r)).pf f = (data.pushforward f).gradedComparison bounds r
  openForget : ∀ (bounds : Option (ℤ × ℤ)) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j],
    (comparison bounds none).sh j = (data.openExtension j).forgetComparison bounds
  openGraded : ∀ (bounds : Option (ℤ × ℤ)) (r : ℤ) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j],
    (comparison bounds (some r)).sh j = (data.openExtension j).gradedComparison bounds r
  canonicalMaps : ∀ (bounds : Option (ℤ × ℤ)) (p : Option ℤ),
    letI := ordinaryBaseChange
    letI := filteredBaseChange bounds
    letI := ordinaryClopen
    letI := filteredClopen bounds
    (comparison bounds p).RespectsCanonicalMaps
  detectsIsomorphisms : ∀ (bounds : Option (ℤ × ℤ)) {X Y : Scheme.{u}}
    {a b : FilteredOperation X Y} (h : FilteredCanonicalMap a b)
    (M : FiniteFilteredDerivedPlus (C := FilteredOperationCoefficients R X) bounds),
    letI := ordinaryBaseChange
    letI := filteredBaseChange bounds
    letI := ordinaryClopen
    letI := filteredClopen bounds
    (∀ r : ℤ, IsIso ((h.eval (filteredOperationOrdinaryFormalism R ordinaryCoherence)).app
      ((finiteFilteredDerivedEvaluation (C := FilteredOperationCoefficients R X)
        bounds (some r)).obj M))) → IsIso ((h.eval (data.toFormalism R bounds)).app M)
  compactification : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f),
    FilteredDerivedOperationLift
      (rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c)
  compactificationFormula : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (bounds : Option (ℤ × ℤ)),
    (compactification c).filtered bounds =
      (data.openExtension c.i).filtered bounds ⋙ (data.pushforward c.g).filtered bounds
  ordinaryCandidateFormula : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f),
    (filteredOperationOrdinaryFormalism R ordinaryCoherence).shriek c =
      rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c
  compactificationForget : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (bounds : Option (ℤ × ℤ)),
    (compactification c).forgetComparison bounds =
      eqToIso (congrArg (fun H ↦ H ⋙
        finiteFilteredDerivedEvaluation (C := FilteredOperationCoefficients R Y) bounds none)
        (compactificationFormula c bounds)) ≪≫
      (comparison bounds none).operation (.comp (.sh c.i c.isOpenImmersion) (.pf c.g))
  compactificationGraded : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (bounds : Option (ℤ × ℤ)) (r : ℤ),
    (compactification c).gradedComparison bounds r =
      eqToIso (congrArg (fun H ↦ H ⋙
        finiteFilteredDerivedEvaluation (C := FilteredOperationCoefficients R Y) bounds (some r))
        (compactificationFormula c bounds)) ≪≫
      (comparison bounds (some r)).operation (.comp (.sh c.i c.isOpenImmersion) (.pf c.g))
  refinementFactorization : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d), FilteredRefinementFactorization r
  ordinaryRefinementPasting :
    letI := ordinaryBaseChange
    letI := ordinaryClopen
    (filteredOperationOrdinaryFormalism R ordinaryCoherence).FilteredOperationRefinementPasting
  filteredRefinementPasting : ∀ bounds : Option (ℤ × ℤ),
    letI := filteredBaseChange bounds
    letI := filteredClopen bounds
    (data.toFormalism R bounds).FilteredOperationRefinementPasting
  ordinaryPasting :
    letI := ordinaryBaseChange
    (filteredOperationOrdinaryFormalism R ordinaryCoherence).FilteredOperationVerticalPasting
  filteredPasting : ∀ bounds : Option (ℤ × ℤ),
    letI := filteredBaseChange bounds
    (data.toFormalism R bounds).FilteredOperationVerticalPasting

end AlgebraicGeometry.ProEtale

namespace CategoryTheory

universe u

/-- Filtered right-derived operations, exact termwise operations, their canonical
adjunction maps, and the pro-etale compactification and exchange package.

Source: Stacks Tags 015Q, 015S, 05U2, 015U, 015V and 05TY; Varshavsky Lemma 5.1.4
and §§5.2.1–5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts).

Proof:
1. Apply an exact additive functor to the objects, arrows and filtration inclusions
   degreewise. It preserves the cokernel defining each grade and preserves homology,
   hence graded quasi-isomorphisms. Additivity preserves homotopies, shifts and cones.
   Localizing gives the termwise lift and its displayed localization comparison.
2. Choose filtered-injective resolutions on each finite interval. Every filtration
   on a filtered-injective term splits into a finite sum of injective graded objects.
   Applying T to its filtration inclusions gives a functorial filtration independent
   of splittings. Its graded and total complexes are the images of ordinary injective
   resolutions. Thus the two comparisons compute RT. Shifts and split-sum cones show
   triangulatedness. The same construction works without a fixed interval.
3. For exact L left adjoint to T, T preserves injectives. Compute filtered derived Hom
   with the filtered-injective representative on the right. The ordinary degreewise
   adjunction preserves each filtration condition and transposes filtered homotopies.
   Its natural Hom bijections give the filtered adjunction and triangle identities.
   Their total maps are those of the specified ordinary derived adjunction. Uniqueness
   of supported truncations gives the same equations on every grade.
4. On the small pro-etale sites the constant-coefficient module categories are
   Grothendieck abelian. The recorded realization equivalence identifies fixed-scalar
   sheaves with intrinsic constant-ring modules and transports precisely the recorded
   inverse image, direct image and extension by zero. Apply Steps 1–3 to these canonical
   sheaf functors. For every supplied c=(j,p), take the composite R^Fp_* j_!^F. It has
   the displayed total and graded candidate comparisons. No compactification existence
   or unconditional constructible-domain preservation is used.
5. Descend the canonical sheaf pullback identity/composition comparisons termwise.
   Their identities hold degreewise. Define pushforward/open comparisons by the
   specified adjunction mates. Canonical expressions use these generators, composition
   and whiskering. The comparison equations for generators imply those for expressions.
   The proper square map is exactly its unit–square–counit formula; the open square map
   is the degreewise extension-by-zero mate. The latter is invertible on Cartesian
   squares. A canonical map whose grades are invertible has a cone with zero grades,
   so is invertible in the filtered localization. This also lifts admissible inverses.
6. For a compactification, compose the proper square mate with the open square
   comparison. Refinement maps are the same proper/open mates; in a non-Cartesian
   refinement first project onto the clopen section (identity there, zero on the
   complement), an exact termwise filtration-preserving transformation. Forgetting
   and grading the resulting expressions gives the ordinary canonical expressions.
7. For compatible compactification towers expand both vertical-pasting paths into
   these maps. Proper subrectangles combine by adjunction mate pasting; open ones by
   the degreewise open comparison. Transpose the mixed proper/open cube by the proper
   adjunctions: both paths become the identical pullback/open map. Clopen projections
   commute with pullback and compose by intersection, so refinements intertwine the
   equation as well. This gives the displayed equality with the actual composition
   arrows, and inverting those arrows on the admissible domain gives the node's
   composition-isomorphism form. Every scheme map here is arbitrary over its base.
-/
theorem filteredDerivedOperationLifts
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
    [HasDerivedCategory.{wB} B]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] :
    (∃ lift : FilteredDerivedOperationLift T.rightDerivedFunctorPlus,
      (∀ (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H],
        Nonempty (FilteredTermwiseLift H)) ∧
      (∀ (L : B ⥤ A) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
        (adj : L ⊣ T), ∃ termwiseLeft : FilteredTermwiseLift L,
        Nonempty (FilteredDerivedAdjunction adj.derivedPlus
          termwiseLeft.toFilteredDerivedOperationLift lift))) ∧
    (∀ (R : Type u) [CommRing R] [Finite R],
      Nonempty (AlgebraicGeometry.ProEtale.ProEtaleFilteredOperationPackage R)) := by
  sorry

end CategoryTheory
