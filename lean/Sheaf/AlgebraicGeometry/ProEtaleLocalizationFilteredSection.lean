/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.LocalizeRingedSiteMorphism
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral

/-!
# The ordinary pro-etale localization section and its filtered pullback

Source: Varshavsky, Example 5.2.3 and Sections 5.2.1--5.2.2; Stacks Project,
Tags 09AH, 09BM and 0152 (blueprint: lem-trf-localization-filtered-section-exchange).

The structures below are witnesses for the theorem, with their values on complexes
and their normalization equations included. No witness is selected as a definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Pretriangulated
open CochainComplex.FiniteFiltered

namespace AlgebraicGeometry.Scheme.TrfLocalization

/-- The derived closed adjunction is the recorded normalized sheaf adjunction localized
using K-injective resolutions. Source: Stacks, Tag 07A6
(blueprint: lem-trf-localization-filtered-section-exchange). -/
def closedAdjunction (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (sfIntrinsicConstantModuleAdjunction i A).mapDerivedCategoryRightDerivedAdjunction

variable {CX CU CZ : Type (u + 2)}
    [Category.{u + 1} CX] [Category.{u + 1} CU] [Category.{u + 1} CZ]
    [Abelian CX] [Abelian CU] [Abelian CZ]
    [HasDerivedCategory.{u + 2} CX] [HasDerivedCategory.{u + 2} CU]
    [HasDerivedCategory.{u + 2} CZ]

/-- The derived open counit is the class of the actual open counit, including the
localization composition and identity comparisons. Source: Varshavsky, Example 5.2.3
(blueprint: lem-trf-localization-filtered-section-exchange). -/
def openCounit (Lj : CX ⥤ CU)
    [Lj.Additive] [PreservesFiniteLimits Lj] [PreservesFiniteColimits Lj]
    (Jj : CU ⥤ CX)
    [Jj.Additive] [PreservesFiniteLimits Jj] [PreservesFiniteColimits Jj]
    (aj : Jj ⊣ Lj) : Lj.mapDerivedCategory ⋙ Jj.mapDerivedCategory ⟶ 𝟭 _ :=
  (mapDerivedCategoryCompIso Lj Jj).inv ≫
    (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso CX (ComplexShape.up ℤ))
      ((Lj ⋙ Jj).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((𝟭 CX).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (Lj ⋙ Jj).mapDerivedCategory (𝟭 CX).mapDerivedCategory
      (whiskerRight (NatTrans.mapHomologicalComplex aj.counit (.up ℤ)) DerivedCategory.Q)) ≫
      (mapDerivedCategoryIdIso _).hom

/-- The canonical comparison from derived open parts to their termwise representatives.
Source: Varshavsky, Example 5.2.3
(blueprint: lem-trf-localization-filtered-section-exchange). -/
def openFactors (Lj : CX ⥤ CU)
    [Lj.Additive] [PreservesFiniteLimits Lj] [PreservesFiniteColimits Lj]
    (Jj : CU ⥤ CX)
    [Jj.Additive] [PreservesFiniteLimits Jj] [PreservesFiniteColimits Jj]
    : DerivedCategory.Q ⋙ Lj.mapDerivedCategory ⋙ Jj.mapDerivedCategory ≅
      (Lj ⋙ Jj).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  isoWhiskerRight Lj.mapDerivedCategoryFactors Jj.mapDerivedCategory ≪≫
    isoWhiskerLeft (Lj.mapHomologicalComplex (.up ℤ)) Jj.mapDerivedCategoryFactors

/-- The ordinary closed-square mate. Its transpose is the inverse pullback-square
comparison followed by the closed counit, so no Cartesian closed square is required.
Source: Varshavsky, Section 5.2.2; Stacks, adjunction mate construction
(blueprint: lem-trf-localization-filtered-section-exchange). -/
def closedMate {C Z : Type (u + 2)} [Category.{u + 2} C] [Category.{u + 2} Z]
    {L : C ⥤ Z} {R : Z ⥤ C} (adj : L ⊣ R)
    (T : C ⥤ C) (TZ : Z ⥤ Z) (c : L ⋙ TZ ≅ T ⋙ L) :
    R ⋙ T ⟶ TZ ⋙ R :=
  whiskerLeft (R ⋙ T) adj.unit ≫
    whiskerRight (whiskerLeft R c.inv) R ≫
    whiskerRight (whiskerRight adj.counit TZ) R

/-- Witnesses for the localization section. The filtered category is the existing
localization of bounded-below uniformly finite filtered complexes. All three evaluation
functors are fixed on chain maps by their factorization isomorphisms. The subcomplex
and quotient identifications are normalized by the actual open counit and closed unit.
Source: Varshavsky, Example 5.2.3; Stacks, Tags 09AH and 0152
(blueprint: lem-trf-localization-filtered-section-exchange). -/
structure SectionData (Lj : CX ⥤ CU)
    [Lj.Additive] [PreservesFiniteLimits Lj] [PreservesFiniteColimits Lj]
    (Jj : CU ⥤ CX)
    [Jj.Additive] [PreservesFiniteLimits Jj] [PreservesFiniteColimits Jj]
    (Li : CX ⥤ CZ)
    [Li.Additive] [PreservesFiniteLimits Li] [PreservesFiniteColimits Li]
    (Ii : CZ ⥤ CX) [Ii.Additive]
    (aj : Jj ⊣ Lj) (ai : Li ⊣ Ii)
    (Ri : DerivedCategory CZ ⥤ DerivedCategory CX)
    (aiD : Li.mapDerivedCategory ⊣ Ri) where
  complexSection : CochainComplex.Plus CX ⥤ Complex CX false
  totalComplex : complexSection ⋙ CochainComplex.FiniteFiltered.forget false ≅
    CochainComplex.Plus.ι CX
  subcomplex : ∀ C : CochainComplex.Plus CX,
    ((complexSection.obj C).obj.filtration.F 1 : CochainComplex CX ℤ) ≅
      ((Lj ⋙ Jj).mapHomologicalComplex (.up ℤ)).obj C.obj
  subcomplex_inclusion : ∀ C : CochainComplex.Plus CX,
    (subcomplex C).hom ≫
        (NatTrans.mapHomologicalComplex aj.counit
          (.up ℤ)).app C.obj =
      ((complexSection.obj C).obj.filtration.F 1).arrow ≫ totalComplex.hom.app C
  filtration : ∀ C : CochainComplex.Plus CX,
    (∀ r : ℤ, r ≤ 0 → (complexSection.obj C).obj.filtration.F r = ⊤) ∧
    (∀ r : ℤ, 2 ≤ r → (complexSection.obj C).obj.filtration.F r = ⊥)
  gradeOneComplex : ∀ C : CochainComplex.Plus CX,
    (complexSection.obj C).obj.filtration.gradedPiece 1 ≅
      ((Lj ⋙ Jj).mapHomologicalComplex (.up ℤ)).obj C.obj
  gradeOneComplex_projection : ∀ C : CochainComplex.Plus CX,
    cokernel.π (Subobject.ofLE
        ((complexSection.obj C).obj.filtration.F 2)
        ((complexSection.obj C).obj.filtration.F 1)
        ((complexSection.obj C).obj.filtration.F_succ_le 1)) ≫
      (gradeOneComplex C).hom = (subcomplex C).hom
  quotientComplex : ∀ C : CochainComplex.Plus CX,
    (complexSection.obj C).obj.filtration.gradedPiece 0 ≅
      ((Li ⋙ Ii).mapHomologicalComplex (.up ℤ)).obj C.obj
  quotient_projection : ∀ C : CochainComplex.Plus CX,
    cokernel.π (Subobject.ofLE
        ((complexSection.obj C).obj.filtration.F 1)
        ((complexSection.obj C).obj.filtration.F 0)
        ((complexSection.obj C).obj.filtration.F_succ_le 0)) ≫
          (quotientComplex C).hom =
      ((complexSection.obj C).obj.filtration.F 0).arrow ≫ totalComplex.hom.app C ≫
        (NatTrans.mapHomologicalComplex ai.unit
          (.up ℤ)).app C.obj
  omega : Derived (A := CX) false ⥤ DerivedCategory.Plus CX
  gr : ℤ → Derived (A := CX) false ⥤ DerivedCategory.Plus CX
  omegaFactors : Q false ⋙ omega ⋙ (DerivedCategory.Plus.ι (C := CX)) ≅
    CochainComplex.FiniteFiltered.forget false ⋙ DerivedCategory.Q
  grFactors : ∀ r : ℤ,
    Q false ⋙ gr r ⋙ (DerivedCategory.Plus.ι (C := CX)) ≅ graded false r ⋙
      DerivedCategory.Q
  sectionFunctor : DerivedCategory.Plus CX ⥤ Derived (A := CX) false
  descent : (DerivedCategory.Plus.Q (C := CX)) ⋙ sectionFunctor ≅ complexSection ⋙ Q false
  total : sectionFunctor ⋙ omega ≅ 𝟭 _
  gradeOne : sectionFunctor ⋙ gr 1 ⋙ (DerivedCategory.Plus.ι (C := CX)) ≅
    (DerivedCategory.Plus.ι (C := CX)) ⋙ Lj.mapDerivedCategory ⋙ Jj.mapDerivedCategory
  gradeZero : sectionFunctor ⋙ gr 0 ⋙ (DerivedCategory.Plus.ι (C := CX)) ≅
    (DerivedCategory.Plus.ι (C := CX)) ⋙ Li.mapDerivedCategory ⋙
      Ri
  closedFactors : DerivedCategory.Q ⋙ Ri ≅
    Ii.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  closedFactors_normalization : ∀ C : CochainComplex CX ℤ,
    aiD.unit.app (DerivedCategory.Q.obj C) ≫
      Ri.map (Li.mapDerivedCategoryFactors.hom.app C) ≫
      closedFactors.hom.app
        ((Li.mapHomologicalComplex (.up ℤ)).obj C) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ai.unit
        (.up ℤ)).app C)
  total_normalization : ∀ C : CochainComplex.Plus CX,
    (DerivedCategory.Plus.ι (C := CX)).map (total.hom.app ((DerivedCategory.Plus.Q (C :=
      CX)).obj C)) ≫
      (DerivedCategory.quotientCompQhIso CX).hom.app C.obj =
    (DerivedCategory.Plus.ι (C := CX)).map (omega.map (descent.hom.app C)) ≫
      omegaFactors.hom.app (complexSection.obj C) ≫
        DerivedCategory.Q.map (totalComplex.hom.app C)
  gradeOne_normalization : ∀ C : CochainComplex.Plus CX,
    gradeOne.hom.app ((DerivedCategory.Plus.Q (C := CX)).obj C) ≫
      (Lj.mapDerivedCategory ⋙ Jj.mapDerivedCategory).map
        ((DerivedCategory.quotientCompQhIso CX).hom.app C.obj) ≫
      (openFactors Lj Jj).hom.app C.obj =
    (DerivedCategory.Plus.ι (C := CX)).map ((gr 1).map (descent.hom.app C)) ≫
      (grFactors 1).hom.app (complexSection.obj C) ≫
        DerivedCategory.Q.map (gradeOneComplex C).hom
  gradeZero_normalization : ∀ C : CochainComplex.Plus CX,
    gradeZero.hom.app ((DerivedCategory.Plus.Q (C := CX)).obj C) ≫
      (Li.mapDerivedCategory ⋙ Ri).map
        ((DerivedCategory.quotientCompQhIso CX).hom.app C.obj) ≫
      (Ri).map
        (Li.mapDerivedCategoryFactors.hom.app C.obj) ≫
      closedFactors.hom.app
        ((Li.mapHomologicalComplex (.up ℤ)).obj C.obj) =
    (DerivedCategory.Plus.ι (C := CX)).map ((gr 0).map (descent.hom.app C)) ≫
      (grFactors 0).hom.app (complexSection.obj C) ≫
        DerivedCategory.Q.map (quotientComplex C).hom
  complex_zero : ∀ C : CochainComplex.Plus CX,
    (NatTrans.mapHomologicalComplex aj.counit
      (.up ℤ)).app C.obj ≫
    (NatTrans.mapHomologicalComplex ai.unit
      (.up ℤ)).app C.obj = 0
  complex_shortExact : ∀ C : CochainComplex.Plus CX,
    (ShortComplex.mk
      ((NatTrans.mapHomologicalComplex aj.counit
        (.up ℤ)).app C.obj)
      ((NatTrans.mapHomologicalComplex ai.unit
        (.up ℤ)).app C.obj) (complex_zero C)).ShortExact
  connecting : (DerivedCategory.Plus.ι (C := CX)) ⋙ Li.mapDerivedCategory ⋙
      Ri ⟶
    ((DerivedCategory.Plus.ι (C := CX)) ⋙ Lj.mapDerivedCategory ⋙
      Jj.mapDerivedCategory) ⋙ shiftFunctor _ (1 : ℤ)
  triangle_distinguished : ∀ K : DerivedCategory.Plus CX,
    Triangle.mk ((openCounit Lj Jj aj).app K.obj) (aiD.unit.app K.obj)
      (connecting.app K) ∈ distTriang (DerivedCategory CX)

  connecting_normalization : ∀ C : CochainComplex.Plus CX,
    connecting.app ((DerivedCategory.Plus.Q (C := CX)).obj C) ≫
      (shiftFunctor _ (1 : ℤ)).map
        ((Lj.mapDerivedCategory ⋙ Jj.mapDerivedCategory).map
          ((DerivedCategory.quotientCompQhIso CX).hom.app C.obj) ≫
          (openFactors Lj Jj).hom.app C.obj) =
    (Li.mapDerivedCategory ⋙ Ri).map
        ((DerivedCategory.quotientCompQhIso CX).hom.app C.obj) ≫
      (Ri).map
        (Li.mapDerivedCategoryFactors.hom.app C.obj) ≫
      closedFactors.hom.app
        ((Li.mapHomologicalComplex (.up ℤ)).obj C.obj) ≫
      DerivedCategory.triangleOfSESδ (complex_shortExact C)

end AlgebraicGeometry.Scheme.TrfLocalization

namespace AlgebraicGeometry.Scheme.TrfLocalization

variable {CX CU CZ : Type (u + 2)}
    [Category.{u + 1} CX] [Category.{u + 1} CU] [Category.{u + 1} CZ]
    [Abelian CX] [Abelian CU] [Abelian CZ]
    [HasDerivedCategory.{u + 2} CX] [HasDerivedCategory.{u + 2} CU]
    [HasDerivedCategory.{u + 2} CZ]

/-- Witnesses for the filtered comparison, fixed at complex level by the identity on
underlying complexes. The two graded equations use the canonical open-unit transpose
and the ordinary closed-adjunction mate. All descent comparisons are normalized on
representatives; in particular none of them can be independently rescaled.
Source: Varshavsky, Sections 5.2.1--5.2.2 and Example 5.2.3
(blueprint: lem-trf-localization-filtered-section-exchange). -/
structure PullbackData (Lj : CX ⥤ CU)
    [Lj.Additive] [PreservesFiniteLimits Lj] [PreservesFiniteColimits Lj]
    (Jj : CU ⥤ CX)
    [Jj.Additive] [PreservesFiniteLimits Jj] [PreservesFiniteColimits Jj]
    (Li : CX ⥤ CZ)
    [Li.Additive] [PreservesFiniteLimits Li] [PreservesFiniteColimits Li]
    (Ii : CZ ⥤ CX) [Ii.Additive]
    (aj : Jj ⊣ Lj) (ai : Li ⊣ Ii)
    {Ri : DerivedCategory CZ ⥤ DerivedCategory CX}
    {aiD : Li.mapDerivedCategory ⊣ Ri}
    (s : SectionData Lj Jj Li Ii aj ai Ri aiD)
    (T : CX ⥤ CX) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (TU : DerivedCategory CU ⥤ DerivedCategory CU)
    (TZ : DerivedCategory CZ ⥤ DerivedCategory CZ)
    (cJ : Lj.mapDerivedCategory ⋙ TU ≅
      T.mapDerivedCategory ⋙ Lj.mapDerivedCategory)
    (cI : Li.mapDerivedCategory ⋙ TZ ≅
      T.mapDerivedCategory ⋙ Li.mapDerivedCategory)
    (reverseOpen : TU ⋙ Jj.mapDerivedCategory ⟶
      Jj.mapDerivedCategory ⋙ T.mapDerivedCategory) where
  complexPullback : Complex CX false ⥤ Complex CX false
  complexTotal : complexPullback ⋙ CochainComplex.FiniteFiltered.forget false ≅
    CochainComplex.FiniteFiltered.forget false ⋙
      T.mapHomologicalComplex (.up ℤ)
  complexStep : ∀ (C : Complex CX false) (r : ℤ),
    ((complexPullback.obj C).obj.filtration.F r : CochainComplex CX ℤ) ≅
      (T.mapHomologicalComplex (.up ℤ)).obj
        (C.obj.filtration.F r)
  complexStep_inclusion : ∀ (C : Complex CX false) (r : ℤ),
    (complexStep C r).hom ≫
      (T.mapHomologicalComplex (.up ℤ)).map
        (C.obj.filtration.F r).arrow =
    ((complexPullback.obj C).obj.filtration.F r).arrow ≫ complexTotal.hom.app C
  complexGrade : ∀ (C : Complex CX false) (r : ℤ),
    (complexPullback.obj C).obj.filtration.gradedPiece r ≅
      (T.mapHomologicalComplex (.up ℤ)).obj
        (C.obj.filtration.gradedPiece r)
  complexGrade_projection : ∀ (C : Complex CX false) (r : ℤ),
    cokernel.π (Subobject.ofLE
        ((complexPullback.obj C).obj.filtration.F (r + 1))
        ((complexPullback.obj C).obj.filtration.F r)
        ((complexPullback.obj C).obj.filtration.F_succ_le r)) ≫
      (complexGrade C r).hom =
    (complexStep C r).hom ≫
      (T.mapHomologicalComplex (.up ℤ)).map
        (cokernel.π (Subobject.ofLE (C.obj.filtration.F (r + 1))
          (C.obj.filtration.F r) (C.obj.filtration.F_succ_le r)))
  filteredPullback : Derived (A := CX) false ⥤ Derived (A := CX) false
  pullbackDescent : Q false ⋙ filteredPullback ≅ complexPullback ⋙ Q false
  plusDescent : (DerivedCategory.Plus.Q (C := CX)) ⋙ T.mapDerivedCategoryPlus ≅
    T.mapCochainComplexPlus ⋙ (DerivedCategory.Plus.Q (C := CX))
  plusDescent_normalization : ∀ C : CochainComplex.Plus CX,
    (DerivedCategory.Plus.ι (C := CX)).map (plusDescent.hom.app C) ≫
      (DerivedCategory.quotientCompQhIso CX).hom.app
        ((T.mapHomologicalComplex (.up ℤ)).obj C.obj) =
    T.mapDerivedCategoryPlusCompatibility.hom.app
        ((DerivedCategory.Plus.Q (C := CX)).obj C) ≫
      (T.mapDerivedCategory).map
        ((DerivedCategory.quotientCompQhIso CX).hom.app C.obj) ≫
      T.mapDerivedCategoryFactors.hom.app C.obj
  omegaPullback : filteredPullback ⋙ s.omega ≅
    s.omega ⋙ T.mapDerivedCategoryPlus
  omegaPullback_normalization : ∀ C : Complex CX false,
    (DerivedCategory.Plus.ι (C := CX)).map (omegaPullback.hom.app ((Q false).obj C)) ≫
      T.mapDerivedCategoryPlusCompatibility.hom.app
        (s.omega.obj ((Q false).obj C)) ≫
      (T.mapDerivedCategory).map (s.omegaFactors.hom.app C) ≫
      T.mapDerivedCategoryFactors.hom.app C.obj.obj =
    (DerivedCategory.Plus.ι (C := CX)).map (s.omega.map (pullbackDescent.hom.app C)) ≫
      s.omegaFactors.hom.app (complexPullback.obj C) ≫
      DerivedCategory.Q.map (complexTotal.hom.app C)
  grPullback : ∀ r : ℤ,
    filteredPullback ⋙ s.gr r ⋙ (DerivedCategory.Plus.ι (C := CX)) ≅
      s.gr r ⋙ (DerivedCategory.Plus.ι (C := CX)) ⋙ T.mapDerivedCategory
  grPullback_normalization : ∀ (C : Complex CX false) (r : ℤ),
    (grPullback r).hom.app ((Q false).obj C) ≫
      (T.mapDerivedCategory).map ((s.grFactors r).hom.app C) ≫
      T.mapDerivedCategoryFactors.hom.app
        (C.obj.filtration.gradedPiece r) =
    (DerivedCategory.Plus.ι (C := CX)).map ((s.gr r).map (pullbackDescent.hom.app C)) ≫
      (s.grFactors r).hom.app (complexPullback.obj C) ≫
      DerivedCategory.Q.map (complexGrade C r).hom

set_option maxHeartbeats 600000 in
-- Checking the inherited dependent comparisons needs more elaboration heartbeats.
/-- The comparison between the localization section and its termwise filtered pullback,
including the actual open and closed graded maps and the formulas for every u.
Source: Varshavsky, Example 5.2.3 and Section 5.2.2
(blueprint: lem-trf-localization-filtered-section-exchange). -/
structure ExchangeData (Lj : CX ⥤ CU)
    [Lj.Additive] [PreservesFiniteLimits Lj] [PreservesFiniteColimits Lj]
    (Jj : CU ⥤ CX)
    [Jj.Additive] [PreservesFiniteLimits Jj] [PreservesFiniteColimits Jj]
    (Li : CX ⥤ CZ)
    [Li.Additive] [PreservesFiniteLimits Li] [PreservesFiniteColimits Li]
    (Ii : CZ ⥤ CX) [Ii.Additive]
    (aj : Jj ⊣ Lj) (ai : Li ⊣ Ii)
    {Ri : DerivedCategory CZ ⥤ DerivedCategory CX}
    {aiD : Li.mapDerivedCategory ⊣ Ri}
    (s : SectionData Lj Jj Li Ii aj ai Ri aiD)
    (T : CX ⥤ CX) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (TU : DerivedCategory CU ⥤ DerivedCategory CU)
    (TZ : DerivedCategory CZ ⥤ DerivedCategory CZ)
    (cJ : Lj.mapDerivedCategory ⋙ TU ≅
      T.mapDerivedCategory ⋙ Lj.mapDerivedCategory)
    (cI : Li.mapDerivedCategory ⋙ TZ ≅
      T.mapDerivedCategory ⋙ Li.mapDerivedCategory)
    (reverseOpen : TU ⋙ Jj.mapDerivedCategory ⟶
      Jj.mapDerivedCategory ⋙ T.mapDerivedCategory)
    extends PullbackData Lj Jj Li Ii aj ai s T TU TZ cJ cI reverseOpen where
  complexAlpha : s.complexSection ⋙ complexPullback ≅
    T.mapCochainComplexPlus ⋙ s.complexSection
  complexAlpha_total : ∀ C : CochainComplex.Plus CX,
    (complexAlpha.hom.app C).hom.hom ≫
      s.totalComplex.hom.app (T.mapCochainComplexPlus.obj C) =
    complexTotal.hom.app (s.complexSection.obj C) ≫
      (T.mapHomologicalComplex (.up ℤ)).map
        (s.totalComplex.hom.app C)
  alpha : s.sectionFunctor ⋙ filteredPullback ≅
    T.mapDerivedCategoryPlus ⋙ s.sectionFunctor
  alpha_descent : ∀ C : CochainComplex.Plus CX,
    filteredPullback.map (s.descent.hom.app C) ≫
      pullbackDescent.hom.app (s.complexSection.obj C) ≫
      (Q false).map (complexAlpha.hom.app C) =
    alpha.hom.app ((DerivedCategory.Plus.Q (C := CX)).obj C) ≫
      s.sectionFunctor.map (plusDescent.hom.app C) ≫
      s.descent.hom.app (T.mapCochainComplexPlus.obj C)
  openExchange : Jj.mapDerivedCategory ⋙ T.mapDerivedCategory ≅
    TU ⋙ Jj.mapDerivedCategory
  openExchange_normalization : openExchange.inv = reverseOpen
  closedCounit : ∀ N : DerivedCategory CZ,
    IsIso (aiD.counit.app N)
  total : ∀ K : DerivedCategory.Plus CX,
    s.omega.map (alpha.hom.app K) ≫
      s.total.hom.app (T.mapDerivedCategoryPlus.obj K) =
    omegaPullback.hom.app (s.sectionFunctor.obj K) ≫
      T.mapDerivedCategoryPlus.map (s.total.hom.app K)
  gradeOne : ∀ K : DerivedCategory.Plus CX,
    (DerivedCategory.Plus.ι (C := CX)).map ((s.gr 1).map (alpha.hom.app K)) ≫
      s.gradeOne.hom.app (T.mapDerivedCategoryPlus.obj K) ≫
      (Jj.mapDerivedCategory).map ((Lj.mapDerivedCategory).map
        (T.mapDerivedCategoryPlusCompatibility.hom.app K)) =
    (grPullback 1).hom.app (s.sectionFunctor.obj K) ≫
      (T.mapDerivedCategory).map (s.gradeOne.hom.app K) ≫
      openExchange.hom.app ((Lj.mapDerivedCategory).obj K.obj) ≫
      (Jj.mapDerivedCategory).map
        (cJ.hom.app K.obj)
  gradeZero : ∀ K : DerivedCategory.Plus CX,
    (DerivedCategory.Plus.ι (C := CX)).map ((s.gr 0).map (alpha.hom.app K)) ≫
      s.gradeZero.hom.app (T.mapDerivedCategoryPlus.obj K) ≫
      (Ri).map ((Li.mapDerivedCategory).map
        (T.mapDerivedCategoryPlusCompatibility.hom.app K)) =
    (grPullback 0).hom.app (s.sectionFunctor.obj K) ≫
      (T.mapDerivedCategory).map (s.gradeZero.hom.app K) ≫
      (closedMate aiD T.mapDerivedCategory TZ cI).app ((Li.mapDerivedCategory).obj K.obj) ≫
      (Ri).map
        (cI.hom.app K.obj)
  morphism_total : ∀ (K : DerivedCategory.Plus CX)
      (u : T.mapDerivedCategoryPlus.obj K ⟶ K),
    s.omega.map (alpha.hom.app K ≫ s.sectionFunctor.map u) ≫ s.total.hom.app K =
      omegaPullback.hom.app (s.sectionFunctor.obj K) ≫
        T.mapDerivedCategoryPlus.map (s.total.hom.app K) ≫ u
  morphism_gradeOne : ∀ (K : DerivedCategory.Plus CX)
      (u : T.mapDerivedCategoryPlus.obj K ⟶ K),
    (DerivedCategory.Plus.ι (C := CX)).map
        ((s.gr 1).map (alpha.hom.app K ≫ s.sectionFunctor.map u)) ≫
      s.gradeOne.hom.app K =
    (grPullback 1).hom.app (s.sectionFunctor.obj K) ≫
      (T.mapDerivedCategory).map (s.gradeOne.hom.app K) ≫
      openExchange.hom.app ((Lj.mapDerivedCategory).obj K.obj) ≫
      (Jj.mapDerivedCategory).map
        (cJ.hom.app K.obj ≫
          (Lj.mapDerivedCategory).map
            (T.mapDerivedCategoryPlusCompatibility.inv.app K ≫
              (DerivedCategory.Plus.ι (C := CX)).map u))
  morphism_gradeZero : ∀ (K : DerivedCategory.Plus CX)
      (u : T.mapDerivedCategoryPlus.obj K ⟶ K),
    (DerivedCategory.Plus.ι (C := CX)).map
        ((s.gr 0).map (alpha.hom.app K ≫ s.sectionFunctor.map u)) ≫
      s.gradeZero.hom.app K =
    (grPullback 0).hom.app (s.sectionFunctor.obj K) ≫
      (T.mapDerivedCategory).map (s.gradeZero.hom.app K) ≫
      (closedMate aiD T.mapDerivedCategory TZ cI).app ((Li.mapDerivedCategory).obj K.obj) ≫
      (Ri).map
        (cI.hom.app K.obj ≫
          (Li.mapDerivedCategory).map
            (T.mapDerivedCategoryPlusCompatibility.inv.app K ≫
              (DerivedCategory.Plus.ι (C := CX)).map u))

/-- The localization section exists and commutes canonically with every pullback whose
open square is Cartesian. The closed square need only commute. The witness includes
both graded formulas for every derived morphism, with no invertibility condition.

Source: Varshavsky, Example 5.2.3 and Sections 5.2.1--5.2.2; Stacks, Tags 09AH,
09BM, 015F and 0152 (blueprint: lem-trf-localization-filtered-section-exchange).

Proof:
1. The ringed open-closed localization theorem gives exact extension by zero and exact
closed direct image when the complementary open is quasi-compact, and the short exact
sequence with the specified open counit and closed unit. Exact inverse images and exact
functors applied termwise preserve quasi-isomorphisms. Localizing the sheaf adjunctions
identifies the termwise units and counits with the ordinary derived ones (the general
pre-derived adjunction theorem, at identity resolutions for these exact operations).
2. Give C the filtration C, j!j*C, 0. Naturality of the open counit defines its action
on chain maps. The cokernel of that counit is i*i*C, by the localization sequence;
all other grades vanish. This gives the displayed inclusion and projection equations.
3. Exactness makes the section invert quasi-isomorphisms grade by grade. The localization
universal property descends it to S. Forgetting inverts graded quasi-isomorphisms:
descending induction through the finite filtration uses the long exact sequences and
their natural comparison diagrams, with the five lemma at each stage. The underlying,
subcomplex and quotient identifications descend with their stated normalizations.
4. Apply the short-exact-sequence triangle construction to the termwise localization
sequence. Its natural connecting map descends by the same universal property and gives
the specified localization triangle, including the connecting-map normalization.
5. Exact t* preserves filtration subobjects and their cokernels, so has the displayed
termwise filtered descent. Cartesian open exchange is inverse to the open-unit mate:
identify its right adjoints on the open slice using fibre-product pasting, then use the
unique conjugate of left adjoints and its unit equation. Transposing the counit square
and using the open triangle identity shows that the pair (1, j!(c_j)b_t) is a filtered
chain isomorphism. This gives complexAlpha and its localized natural isomorphism alpha.
6. The transpose of i*(c_i)e_i t*(p_C) is the identity: naturality of c_i inverse reduces
it to the closed counit-unit triangle identity. The transpose of p_(t*C) is also the
identity. Since t*(p_C) is epic, uniqueness of cokernel descent identifies the quotient
map with i*(c_i)e_i. The derived adjunction is the localized sheaf adjunction from Step 1,
so this is precisely the ordinary derived closed mate, without a Cartesian hypothesis.
7. Apply S to arbitrary u and compose with alpha. Naturality of the total and graded
identifications gives the three morphism formulas. Localization naturality handles every
derived morphism u, without choosing a single chain-map representative or assuming u is
invertible. These are exactly the seven steps of this node's natural-language proof. -/
theorem localizationFilteredSectionExchange (A : Type u) [CommRing A] [Finite A]
    {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ X) [IsClosedImmersion i] (h : Set.range j = (Set.range i)ᶜ) :
    ∃ s : SectionData
      (sfIntrinsicPullback A j) (sfIntrinsicExtensionByZero j A)
      (sfIntrinsicPullback A i) (proEtaleConstantModuleDirectImage i A)
      (sfIntrinsicOpenAdjunction A j) (sfIntrinsicConstantModuleAdjunction i A)
      (proEtaleConstantDerivedDirectImage i A) (closedAdjunction A i),
      ∀ (t : X ⟶ X) (tU : U ⟶ U) (tZ : Z ⟶ Z)
        (wU : tU ≫ j = j ≫ t) (wZ : tZ ≫ i = i ≫ t),
        IsPullback tU j j t → Nonempty (ExchangeData
          (sfIntrinsicPullback A j) (sfIntrinsicExtensionByZero j A)
          (sfIntrinsicPullback A i) (proEtaleConstantModuleDirectImage i A)
          (sfIntrinsicOpenAdjunction A j) (sfIntrinsicConstantModuleAdjunction i A)
          s (sfIntrinsicPullback A t)
          (sfIntrinsicDerivedPullback A tU) (sfIntrinsicDerivedPullback A tZ)
          (sfIntrinsicDerivedSquarePullback A tU j j t wU)
          (sfIntrinsicDerivedSquarePullback A tZ i i t wZ)
          (sfIntrinsicDerivedOpenMate A tU j j t wU)) := by
  sorry

end AlgebraicGeometry.Scheme.TrfLocalization
