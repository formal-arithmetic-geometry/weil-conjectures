/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.CategoryTheory.NonnegativeDerivedTotalization
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.CosimplicialInjectiveTotalReplacement

/-!
# Exact units and derived finite totalization

Source: Stacks Project, Derived Categories, Tag 015F, and the seven-step naturality
and exact-postcomposition argument in the node
(blueprint: lem-sfb-exact-unit-derived-total-square).

All totals below are the existing alternating-coface totals of nonnegative complexes.
Resolved targets retain actual strict diagrams. In particular no total is assigned to a
bare diagram in the ordinary derived category. The comparison structures are the recorded
ones of lem-sfb-nonnegative-derived-totalization, including their normalization, uniqueness,
column identifications and augmented-resolution fields.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA wA uB vB wB uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wC} C]

/-- Exact descent on a nonnegative complex, with extension by zero inserted explicitly.
Source: Stacks Tag 015F (blueprint: lem-sfb-exact-unit-derived-total-square). -/
def exactNonnegativeLocalizationIso (L : A ⥤ B) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (X : CochainComplex A ℕ) :
    L.mapDerivedCategory.obj ((nonnegativeComplexLocalization A).obj X) ≅
      (nonnegativeComplexLocalization B).obj
        ((L.mapHomologicalComplex (.up ℕ)).obj X) :=
  L.mapDerivedCategoryFactors.app (X.extend ComplexShape.embeddingUpNat) ≪≫
    DerivedCategory.Q.mapIso (X.mapExtendIso ComplexShape.embeddingUpNat L)

/-- The strict map with component theta on every column and every internal degree.
Source: naturality, Stacks Tag 015F
(blueprint: lem-sfb-exact-unit-derived-total-square). -/
def exactUnitCosimplicialMap (H : A ⥤ A) [H.Additive] (θ : 𝟭 A ⟶ H)
    (K : CosimplicialObject (CochainComplex A ℕ)) :
    K ⟶ K ⋙ H.mapHomologicalComplex (.up ℕ) :=
  K.rightUnitor.inv ≫ Functor.whiskerLeft K
    ((Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv ≫
      NatTrans.mapHomologicalComplex θ (.up ℕ))

variable [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]

/-- Move an exact functor through a resolved finite total, using the summand-normalized
beta from the existing comparison interface. Source: Stacks Tag 015F
(blueprint: lem-sfb-exact-unit-derived-total-square). -/
def exactFiniteTotalLocalizationIso (P : B ⥤ C) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (cP : NonnegativeDerivedTotalizationComparison P)
    (J : CosimplicialObject (CochainComplex B ℕ)) :
    P.mapDerivedCategory.obj ((nonnegativeComplexLocalization B).obj
        ((nonnegativeCosimplicialTotal B).obj J)) ≅
      (nonnegativeComplexLocalization C).obj ((nonnegativeCosimplicialTotal C).obj
        (J ⋙ P.mapHomologicalComplex (.up ℕ))) :=
  exactNonnegativeLocalizationIso P ((nonnegativeCosimplicialTotal B).obj J) ≪≫
    (nonnegativeComplexLocalization C).mapIso (cP.beta J)

/-- The specified comparison u = P_D(chi) P_D RG(a), with the canonical finite-sum
identification at the target. Source: Stacks Tag 015F and the node's step 5
(blueprint: lem-sfb-exact-unit-derived-total-square). -/
def exactPostDerivedTotalComparison (G : A ⥤ B) [G.Additive]
    (cG : NonnegativeDerivedTotalizationComparison G)
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (cP : NonnegativeDerivedTotalizationComparison P)
    (K : CosimplicialObject (CochainComplex A ℕ))
    (R : NonnegativeCosimplicialResolution A K) (M : DerivedCategory A)
    (a : M ≅ (nonnegativeComplexLocalization A).obj
      ((nonnegativeCosimplicialTotal A).obj K)) :
    P.mapDerivedCategory.obj (G.rightDerivedFunctor.obj M) ≅
      (nonnegativeComplexLocalization C).obj ((nonnegativeCosimplicialTotal C).obj
        ((R.diagram ⋙ G.mapHomologicalComplex (.up ℕ)) ⋙
          P.mapHomologicalComplex (.up ℕ))) :=
  P.mapDerivedCategory.mapIso (G.rightDerivedFunctor.mapIso a ≪≫ cG.chi K R) ≪≫
    exactFiniteTotalLocalizationIso P cP (R.diagram ⋙ G.mapHomologicalComplex (.up ℕ))

/-- The total of a strict map of resolved columns, after applying G and P termwise.
Source: the node's step 5, Stacks Tag 015F
(blueprint: lem-sfb-exact-unit-derived-total-square). -/
def exactPostResolvedTotalMap (G : A ⥤ B) [G.Additive] (P : B ⥤ C) [P.Additive]
    {J L : CosimplicialObject (CochainComplex A ℕ)} (g : J ⟶ L) :=
  (nonnegativeComplexLocalization C).map ((nonnegativeCosimplicialTotal C).map
    (Functor.whiskerRight (Functor.whiskerRight g (G.mapHomologicalComplex (.up ℕ)))
      (P.mapHomologicalComplex (.up ℕ))))

/-- Iterated exact postcomposition of the specified comparison. The target uses nested
strict termwise functors, canonically the SP-resolved target. Source: Stacks Tag 015F,
step 7 (blueprint: lem-sfb-exact-unit-derived-total-square). -/
def exactFurtherPostDerivedTotalComparison
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    [Abelian.HasKInjectiveResolutions C]
    (G : A ⥤ B) [G.Additive] (cG : NonnegativeDerivedTotalizationComparison G)
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (cP : NonnegativeDerivedTotalizationComparison P)
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (cS : NonnegativeDerivedTotalizationComparison S)
    (K : CosimplicialObject (CochainComplex A ℕ))
    (R : NonnegativeCosimplicialResolution A K) (M : DerivedCategory A)
    (a : M ≅ (nonnegativeComplexLocalization A).obj
      ((nonnegativeCosimplicialTotal A).obj K)) :=
  S.mapDerivedCategory.mapIso (exactPostDerivedTotalComparison G cG P cP K R M a) ≪≫
    exactFiniteTotalLocalizationIso S cS
      ((R.diagram ⋙ G.mapHomologicalComplex (.up ℕ)) ⋙ P.mapHomologicalComplex (.up ℕ))

/-- The resolved bottom arrow after a further exact functor, retaining all three
termwise operations. Source: Stacks Tag 015F, step 7
(blueprint: lem-sfb-exact-unit-derived-total-square). -/
def exactFurtherResolvedTotalMap
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (G : A ⥤ B) [G.Additive] (P : B ⥤ C) [P.Additive] (S : C ⥤ D) [S.Additive]
    {J L : CosimplicialObject (CochainComplex A ℕ)} (g : J ⟶ L) :=
  (nonnegativeComplexLocalization D).map ((nonnegativeCosimplicialTotal D).map
    (Functor.whiskerRight
      (Functor.whiskerRight (Functor.whiskerRight g (G.mapHomologicalComplex (.up ℕ)))
        (P.mapHomologicalComplex (.up ℕ))) (S.mapHomologicalComplex (.up ℕ))))

/-- Direct SP comparison, transported by the canonical derived composition and termwise
composition identifications to the nested resolved target. Source: Stacks Tag 015F,
step 7 (blueprint: lem-sfb-exact-unit-derived-total-square). -/
def exactCompositePostDerivedTotalComparison
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (G : A ⥤ B) [G.Additive] (cG : NonnegativeDerivedTotalizationComparison G)
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (cPS : NonnegativeDerivedTotalizationComparison (P ⋙ S))
    (K : CosimplicialObject (CochainComplex A ℕ))
    (R : NonnegativeCosimplicialResolution A K) (M : DerivedCategory A)
    (a : M ≅ (nonnegativeComplexLocalization A).obj
      ((nonnegativeCosimplicialTotal A).obj K)) :
    S.mapDerivedCategory.obj (P.mapDerivedCategory.obj (G.rightDerivedFunctor.obj M)) ≅
      (nonnegativeComplexLocalization D).obj ((nonnegativeCosimplicialTotal D).obj
        (((R.diagram ⋙ G.mapHomologicalComplex (.up ℕ)) ⋙
          P.mapHomologicalComplex (.up ℕ)) ⋙ S.mapHomologicalComplex (.up ℕ))) :=
  letI := comp_preservesFiniteLimits P S
  letI := comp_preservesFiniteColimits P S
  ((Functor.mapDerivedCategoryCompIso P S).app (G.rightDerivedFunctor.obj M)).symm ≪≫
    exactPostDerivedTotalComparison G cG (P ⋙ S) cPS K R M a ≪≫
    (nonnegativeComplexLocalization D).mapIso ((nonnegativeCosimplicialTotal D).mapIso
      (Functor.isoWhiskerLeft (R.diagram ⋙ G.mapHomologicalComplex (.up ℕ))
        (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℕ)).symm))

/-- The complete exact-unit square, quantified over all models, compatible resolutions,
and specified augmentations. The beta and chi fields are the existing normalized
comparisons, not freely chosen isomorphisms. Source: Stacks Tag 015F and the node's
steps 1--7 (blueprint: lem-sfb-exact-unit-derived-total-square). -/
structure ExactUnitDerivedTotalSquare (G : A ⥤ B) [G.Additive]
    (H : A ⥤ A) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (θ : 𝟭 A ⟶ H) where
  comparisonG : NonnegativeDerivedTotalizationComparison G
  comparisonH : NonnegativeDerivedTotalizationComparison H
  comparisonP : NonnegativeDerivedTotalizationComparison P
  thetaD : 𝟭 (DerivedCategory A) ⟶ H.mapDerivedCategory
  thetaD_normalized : ∀ X : CochainComplex A ℕ,
    thetaD.app ((nonnegativeComplexLocalization A).obj X) ≫
        (exactNonnegativeLocalizationIso H X).hom =
      (nonnegativeComplexLocalization A).map
        ((Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv.app X ≫
          (NatTrans.mapHomologicalComplex θ (.up ℕ)).app X)
  strict_components : ∀ (K : CosimplicialObject (CochainComplex A ℕ))
      (n : SimplexCategory) (q : ℕ),
    ((exactUnitCosimplicialMap H θ K).app n).f q = θ.app ((K.obj n).X q)
  total_unit : ∀ K : CosimplicialObject (CochainComplex A ℕ),
    (Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv.app
        ((nonnegativeCosimplicialTotal A).obj K) ≫
        (NatTrans.mapHomologicalComplex θ (.up ℕ)).app
          ((nonnegativeCosimplicialTotal A).obj K) ≫ (comparisonH.beta K).hom =
      (nonnegativeCosimplicialTotal A).map (exactUnitCosimplicialMap H θ K)
  localized_unit : ∀ (K : CosimplicialObject (CochainComplex A ℕ))
      (M : DerivedCategory A)
      (a : M ≅ (nonnegativeComplexLocalization A).obj
        ((nonnegativeCosimplicialTotal A).obj K)),
    thetaD.app M ≫ H.mapDerivedCategory.map a.hom ≫
        (exactNonnegativeLocalizationIso H ((nonnegativeCosimplicialTotal A).obj K)).hom ≫
        (nonnegativeComplexLocalization A).map (comparisonH.beta K).hom =
      a.hom ≫ (nonnegativeComplexLocalization A).map
        ((nonnegativeCosimplicialTotal A).map (exactUnitCosimplicialMap H θ K))
  compatible : ∀ K : CosimplicialObject (CochainComplex A ℕ),
    ∃ (R : NonnegativeCosimplicialResolution A K)
      (T : NonnegativeCosimplicialResolution A (K ⋙ H.mapHomologicalComplex (.up ℕ)))
      (g : R.diagram ⟶ T.diagram),
      R.augmentation ≫ g = exactUnitCosimplicialMap H θ K ≫ T.augmentation
  compatible_augmented : ∀ (X : CochainComplex A ℕ)
      (K : CosimplicialObject (CochainComplex A ℕ))
      (b : (Functor.const SimplexCategory).obj X ⟶ K),
    ∃ (I L : CochainComplex A ℕ) (r : X ⟶ I)
      (t : (H.mapHomologicalComplex (.up ℕ)).obj X ⟶ L)
      (R : NonnegativeCosimplicialResolution A K)
      (T : NonnegativeCosimplicialResolution A (K ⋙ H.mapHomologicalComplex (.up ℕ)))
      (g : R.diagram ⟶ T.diagram) (v : I ⟶ L)
      (c : (Functor.const SimplexCategory).obj I ⟶ R.diagram)
      (d : (Functor.const SimplexCategory).obj L ⟶ T.diagram),
      QuasiIso r ∧ QuasiIso t ∧ (∀ q : ℕ, Injective (I.X q)) ∧
      (∀ q : ℕ, Injective (L.X q)) ∧
      (R.augmentation ≫ g = exactUnitCosimplicialMap H θ K ≫ T.augmentation) ∧
      (r ≫ v = ((Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv.app X ≫
        (NatTrans.mapHomologicalComplex θ (.up ℕ)).app X) ≫ t) ∧
      ∀ n : SimplexCategory,
        (b.app n ≫ R.augmentation.app n = r ≫ c.app n) ∧
        ((H.mapHomologicalComplex (.up ℕ)).map (b.app n) ≫ T.augmentation.app n =
          t ≫ d.app n) ∧ (c.app n ≫ g.app n = v ≫ d.app n)
  square : ∀ (K : CosimplicialObject (CochainComplex A ℕ))
      (R : NonnegativeCosimplicialResolution A K)
      (T : NonnegativeCosimplicialResolution A (K ⋙ H.mapHomologicalComplex (.up ℕ)))
      (g : R.diagram ⟶ T.diagram),
    R.augmentation ≫ g = exactUnitCosimplicialMap H θ K ≫ T.augmentation →
    ∀ (M : DerivedCategory A)
      (a : M ≅ (nonnegativeComplexLocalization A).obj
        ((nonnegativeCosimplicialTotal A).obj K)),
    P.mapDerivedCategory.map (G.rightDerivedFunctor.map (thetaD.app M)) ≫
        (exactPostDerivedTotalComparison G comparisonG P comparisonP
          (K ⋙ H.mapHomologicalComplex (.up ℕ)) T (H.mapDerivedCategory.obj M)
          (H.mapDerivedCategory.mapIso a ≪≫
            exactNonnegativeLocalizationIso H ((nonnegativeCosimplicialTotal A).obj K) ≪≫
            (nonnegativeComplexLocalization A).mapIso (comparisonH.beta K))).hom =
      (exactPostDerivedTotalComparison G comparisonG P comparisonP K R M a).hom ≫
        exactPostResolvedTotalMap G P g
  thetaD_unbounded : ∀ X : CochainComplex A ℤ,
    thetaD.app (DerivedCategory.Q.obj X) ≫ H.mapDerivedCategoryFactors.hom.app X =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app X ≫
          (NatTrans.mapHomologicalComplex θ (.up ℤ)).app X)
  column_square : ∀ (K : CosimplicialObject (CochainComplex A ℕ))
      (R : NonnegativeCosimplicialResolution A K)
      (T : NonnegativeCosimplicialResolution A (K ⋙ H.mapHomologicalComplex (.up ℕ)))
      (g : R.diagram ⟶ T.diagram),
    R.augmentation ≫ g = exactUnitCosimplicialMap H θ K ≫ T.augmentation →
    ∀ n : SimplexCategory,
    P.mapDerivedCategory.map (G.rightDerivedFunctor.map
        (thetaD.app ((nonnegativeComplexLocalization A).obj (K.obj n)) ≫
          (exactNonnegativeLocalizationIso H (K.obj n)).hom)) ≫
        P.mapDerivedCategory.map
          ((comparisonG.column (K ⋙ H.mapHomologicalComplex (.up ℕ)) T).hom.app n) ≫
        (exactNonnegativeLocalizationIso P
          ((G.mapHomologicalComplex (.up ℕ)).obj (T.diagram.obj n))).hom =
      P.mapDerivedCategory.map ((comparisonG.column K R).hom.app n) ≫
        (exactNonnegativeLocalizationIso P
          ((G.mapHomologicalComplex (.up ℕ)).obj (R.diagram.obj n))).hom ≫
        (nonnegativeComplexLocalization C).map
          ((P.mapHomologicalComplex (.up ℕ)).map
            ((G.mapHomologicalComplex (.up ℕ)).map (g.app n)))
  naturality : ∀ {K L : CosimplicialObject (CochainComplex A ℕ)} (f : K ⟶ L)
      (R : NonnegativeCosimplicialResolution A K)
      (T : NonnegativeCosimplicialResolution A L) (g : R.diagram ⟶ T.diagram),
    R.augmentation ≫ g = f ≫ T.augmentation →
    ∀ (M N : DerivedCategory A)
      (a : M ≅ (nonnegativeComplexLocalization A).obj
        ((nonnegativeCosimplicialTotal A).obj K))
      (b : N ≅ (nonnegativeComplexLocalization A).obj
        ((nonnegativeCosimplicialTotal A).obj L)) (m : M ⟶ N),
    m ≫ b.hom = a.hom ≫ (nonnegativeComplexLocalization A).map
      ((nonnegativeCosimplicialTotal A).map f) →
    P.mapDerivedCategory.map (G.rightDerivedFunctor.map m) ≫
        (exactPostDerivedTotalComparison G comparisonG P comparisonP L T N b).hom =
      (exactPostDerivedTotalComparison G comparisonG P comparisonP K R M a).hom ≫
        exactPostResolvedTotalMap G P g
  augmentation : ∀ (X I : CochainComplex A ℕ) (r : X ⟶ I)
      (K : CosimplicialObject (CochainComplex A ℕ))
      (R : NonnegativeCosimplicialResolution A K)
      (b : (Functor.const SimplexCategory).obj X ⟶ K)
      (c : (Functor.const SimplexCategory).obj I ⟶ R.diagram),
    QuasiIso r → (∀ q : ℕ, Injective (I.X q)) →
    (∀ n : SimplexCategory, b.app n ≫ R.augmentation.app n = r ≫ c.app n) →
    ∃ (a : X ⟶ (nonnegativeCosimplicialTotal A).obj K)
      (aI : I ⟶ (nonnegativeCosimplicialTotal A).obj R.diagram)
      (eX : G.rightDerivedFunctor.obj ((nonnegativeComplexLocalization A).obj X) ≅
        (nonnegativeComplexLocalization B).obj
          ((G.mapHomologicalComplex (.up ℕ)).obj I)),
      IsNonnegativeTotalAugmentation b a ∧ IsNonnegativeTotalAugmentation c aI ∧
      (eX.hom ≫ nonnegativeRightDerivedUnit G I =
        G.rightDerivedFunctor.map ((nonnegativeComplexLocalization A).map r)) ∧
      (P.mapDerivedCategory.map
          (G.rightDerivedFunctor.map ((nonnegativeComplexLocalization A).map a)) ≫
          (exactPostDerivedTotalComparison G comparisonG P comparisonP K R
            ((nonnegativeComplexLocalization A).obj ((nonnegativeCosimplicialTotal A).obj K))
            (Iso.refl _)).hom =
        P.mapDerivedCategory.map eX.hom ≫
          (exactNonnegativeLocalizationIso P
            ((G.mapHomologicalComplex (.up ℕ)).obj I)).hom ≫
          (nonnegativeComplexLocalization C).map
            ((P.mapHomologicalComplex (.up ℕ)).map
              ((G.mapHomologicalComplex (.up ℕ)).map aI ≫ (comparisonG.beta R.diagram).hom) ≫
                (comparisonP.beta (R.diagram ⋙ G.mapHomologicalComplex (.up ℕ))).hom))
  postcomposition : ∀ {D : Type uD} [Category.{vD} D] [Abelian D]
      [HasDerivedCategory.{wD} D] [IsGrothendieckAbelian.{vD} D]
      [Abelian.HasKInjectiveResolutions C]
      (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S],
    ∃ (cS : NonnegativeDerivedTotalizationComparison S)
      (cPS : NonnegativeDerivedTotalizationComparison (P ⋙ S)),
    (∀ J : CosimplicialObject (CochainComplex B ℕ),
      (S.mapHomologicalComplex (.up ℕ)).mapIso (comparisonP.beta J) ≪≫
          cS.beta (J ⋙ P.mapHomologicalComplex (.up ℕ)) ≪≫
          (nonnegativeCosimplicialTotal D).mapIso
            (Functor.isoWhiskerLeft J (Functor.mapHomologicalComplexCompIso
              (Iso.refl (P ⋙ S)) (.up ℕ))) =
        (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℕ)).app
          ((nonnegativeCosimplicialTotal B).obj J) ≪≫ cPS.beta J) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ))
      (R : NonnegativeCosimplicialResolution A K) (M : DerivedCategory A)
      (a : M ≅ (nonnegativeComplexLocalization A).obj
        ((nonnegativeCosimplicialTotal A).obj K)),
      exactCompositePostDerivedTotalComparison G comparisonG P S cPS K R M a =
        exactFurtherPostDerivedTotalComparison G comparisonG P comparisonP S cS K R M a) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ))
      (R : NonnegativeCosimplicialResolution A K)
      (T : NonnegativeCosimplicialResolution A (K ⋙ H.mapHomologicalComplex (.up ℕ)))
      (g : R.diagram ⟶ T.diagram),
      R.augmentation ≫ g = exactUnitCosimplicialMap H θ K ≫ T.augmentation →
      ∀ (M : DerivedCategory A)
        (a : M ≅ (nonnegativeComplexLocalization A).obj
          ((nonnegativeCosimplicialTotal A).obj K)),
      S.mapDerivedCategory.map
          (P.mapDerivedCategory.map (G.rightDerivedFunctor.map (thetaD.app M))) ≫
          (exactFurtherPostDerivedTotalComparison G comparisonG P comparisonP S cS
            (K ⋙ H.mapHomologicalComplex (.up ℕ)) T (H.mapDerivedCategory.obj M)
            (H.mapDerivedCategory.mapIso a ≪≫
              exactNonnegativeLocalizationIso H ((nonnegativeCosimplicialTotal A).obj K) ≪≫
              (nonnegativeComplexLocalization A).mapIso (comparisonH.beta K))).hom =
        (exactFurtherPostDerivedTotalComparison G comparisonG P comparisonP S cS K R M a).hom ≫
          exactFurtherResolvedTotalMap G P S g)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B] in
@[reassoc]
private lemma exact_localization_naturality (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : CochainComplex A ℕ} (f : X ⟶ Y) :
    F.mapDerivedCategory.map ((nonnegativeComplexLocalization A).map f) ≫
        (exactNonnegativeLocalizationIso F Y).hom =
      (exactNonnegativeLocalizationIso F X).hom ≫
        (nonnegativeComplexLocalization B).map
          ((F.mapHomologicalComplex (.up ℕ)).map f) := by
  dsimp [exactNonnegativeLocalizationIso, nonnegativeComplexLocalization]
  simp only [Category.assoc]
  rw [F.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (F.mapDerivedCategoryFactors.hom.app _ ≫ ·)
  apply congrArg DerivedCategory.Q.map
  exact (ComplexShape.embeddingUpNat.mapExtendFunctorNatIso F).hom.naturality f

omit [Abelian.HasKInjectiveResolutions A] [HasDerivedCategory A] in
private lemma unit_extend_component (H : A ⥤ A) [H.Additive] (θ : 𝟭 A ⟶ H)
    (X : CochainComplex A ℕ) (i : Option ℕ) :
    θ.app (HomologicalComplex.extend.X X i) ≫
        (HomologicalComplex.mapExtendX X H i).hom =
      HomologicalComplex.extend.mapX
        ((Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv.app X ≫
          (NatTrans.mapHomologicalComplex θ (.up ℕ)).app X) i := by
  cases i with
  | none => exact (isZero_zero A).eq_of_src _ _
  | some q =>
    simp only [HomologicalComplex.extend.X, HomologicalComplex.mapExtendX,
      Iso.refl_hom, Category.comp_id, HomologicalComplex.extend.mapX,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
      NatTrans.mapHomologicalComplex_app_f]
    erw [Category.id_comp]

omit [Abelian.HasKInjectiveResolutions A] in
private lemma exists_unit_descent (H : A ⥤ A) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (θ : 𝟭 A ⟶ H) :
    ∃ t : 𝟭 (DerivedCategory A) ⟶ H.mapDerivedCategory,
      (∀ X : CochainComplex A ℤ,
        t.app (DerivedCategory.Q.obj X) ≫ H.mapDerivedCategoryFactors.hom.app X =
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app X ≫
              (NatTrans.mapHomologicalComplex θ (.up ℤ)).app X)) ∧
      (∀ X : CochainComplex A ℕ,
        t.app ((nonnegativeComplexLocalization A).obj X) ≫
            (exactNonnegativeLocalizationIso H X).hom =
          (nonnegativeComplexLocalization A).map
            ((Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv.app X ≫
              (NatTrans.mapHomologicalComplex θ (.up ℕ)).app X)) := by
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let : Localization.Lifting Q W Q (𝟭 (DerivedCategory A)) := ⟨Q.rightUnitor⟩
  let τ : Q ⟶ H.mapHomologicalComplex (.up ℤ) ⋙ Q :=
    Q.leftUnitor.inv ≫ Functor.whiskerRight
      ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv ≫
        NatTrans.mapHomologicalComplex θ (.up ℤ)) Q
  let t := Localization.liftNatTrans Q W Q
    (H.mapHomologicalComplex (.up ℤ) ⋙ Q) (𝟭 _) H.mapDerivedCategory τ
  have ht (X : CochainComplex A ℤ) :
      t.app (DerivedCategory.Q.obj X) ≫ H.mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app X ≫
            (NatTrans.mapHomologicalComplex θ (.up ℤ)).app X) := by
    dsimp [t]
    rw [Localization.liftNatTrans_app]
    simp [Localization.Lifting.iso, τ, Q]
  refine ⟨t, ht, ?_⟩
  intro X
  dsimp [exactNonnegativeLocalizationIso, nonnegativeComplexLocalization]
  rw [← Category.assoc, ht, ← Functor.map_comp]
  congr 1
  ext i
  simp only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f]
  erw [Category.id_comp]
  exact unit_extend_component H θ X _

omit [Abelian.HasKInjectiveResolutions B] in
private lemma beta_ext (F : A ⥤ B) [F.Additive]
    (cF : NonnegativeDerivedTotalizationComparison F)
    (K : CosimplicialObject (CochainComplex A ℕ)) (r : ℕ)
    {Z : B} {f g : F.obj (((nonnegativeCosimplicialTotal A).obj K).X r) ⟶ Z}
    (h : ∀ n q (hnq : n + q = r),
      F.map (HomologicalComplex₂.ιTotal
        ((AlgebraicTopology.alternatingCofaceMapComplex _).obj K)
        (.up ℕ) n q r hnq) ≫ f =
      F.map (HomologicalComplex₂.ιTotal
        ((AlgebraicTopology.alternatingCofaceMapComplex _).obj K)
        (.up ℕ) n q r hnq) ≫ g) : f = g := by
  apply (cancel_epi ((cF.beta K).inv.f r)).mp
  apply HomologicalComplex₂.total.hom_ext
  intro n q hnq
  rw [← cF.beta_summand K n q r hnq]
  have hc : (cF.beta K).hom.f r ≫ (cF.beta K).inv.f r = 𝟙 _ :=
    (HomologicalComplex.Hom.isoApp (cF.beta K) r).hom_inv_id
  simpa only [Category.assoc, reassoc_of% hc, Category.id_comp] using h n q hnq

omit [Abelian.HasKInjectiveResolutions B] in
@[reassoc]
private lemma beta_naturality (F : A ⥤ B) [F.Additive]
    (cF : NonnegativeDerivedTotalizationComparison F)
    {K L : CosimplicialObject (CochainComplex A ℕ)} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℕ)).map ((nonnegativeCosimplicialTotal A).map f) ≫
        (cF.beta L).hom =
      (cF.beta K).hom ≫ (nonnegativeCosimplicialTotal B).map
        (Functor.whiskerRight f (F.mapHomologicalComplex (.up ℕ))) := by
  ext r
  simp only [HomologicalComplex.comp_f]
  apply beta_ext F cF K r
  intro n q hnq
  change F.map (HomologicalComplex₂.ιTotal _ (.up ℕ) n q r hnq) ≫
      F.map ((HomologicalComplex₂.total.map
        ((AlgebraicTopology.alternatingCofaceMapComplex _).map f) (.up ℕ)).f r) ≫
        (cF.beta L).hom.f r = _
  rw [← F.map_comp_assoc, HomologicalComplex₂.ιTotal_map, F.map_comp,
    Category.assoc, cF.beta_summand, reassoc_of% (cF.beta_summand K n q r hnq)]
  change _ = HomologicalComplex₂.ιTotal _ (.up ℕ) n q r hnq ≫
    (HomologicalComplex₂.total.map
      ((AlgebraicTopology.alternatingCofaceMapComplex _).map
        (Functor.whiskerRight f (F.mapHomologicalComplex (.up ℕ)))) (.up ℕ)).f r
  rw [HomologicalComplex₂.ιTotal_map]
  rfl

private lemma total_unit_identity (H : A ⥤ A) [H.Additive]
    (cH : NonnegativeDerivedTotalizationComparison H) (θ : 𝟭 A ⟶ H)
    (K : CosimplicialObject (CochainComplex A ℕ)) :
    (Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv.app
        ((nonnegativeCosimplicialTotal A).obj K) ≫
        (NatTrans.mapHomologicalComplex θ (.up ℕ)).app
          ((nonnegativeCosimplicialTotal A).obj K) ≫ (cH.beta K).hom =
      (nonnegativeCosimplicialTotal A).map (exactUnitCosimplicialMap H θ K) := by
  ext r
  simp only [HomologicalComplex.comp_f]
  dsimp only [Functor.mapHomologicalComplexIdIso, NatTrans.mapHomologicalComplex,
    NatIso.ofComponents, HomologicalComplex.Hom.isoOfComponents, Iso.refl_inv,
    Category.id_comp]
  apply HomologicalComplex₂.total.hom_ext
  intro n q hnq
  erw [Category.id_comp]
  change HomologicalComplex₂.ιTotal _ (.up ℕ) n q r hnq ≫
      θ.app _ ≫ (cH.beta K).hom.f r =
    HomologicalComplex₂.ιTotal _ (.up ℕ) n q r hnq ≫
      (HomologicalComplex₂.total.map
        ((AlgebraicTopology.alternatingCofaceMapComplex _).map
          (exactUnitCosimplicialMap H θ K)) (.up ℕ)).f r
  have hn := θ.naturality (HomologicalComplex₂.ιTotal
    ((AlgebraicTopology.alternatingCofaceMapComplex _).obj K) (.up ℕ) n q r hnq)
  dsimp only [Functor.id_map] at hn
  erw [reassoc_of% hn, cH.beta_summand, HomologicalComplex₂.ιTotal_map]
  simp only [AlgebraicTopology.alternatingCofaceMapComplex_obj,
    AlgebraicTopology.alternatingCofaceMapComplex_map,
    AlgebraicTopology.AlternatingCofaceMapComplex.map, exactUnitCosimplicialMap]
  erw [Category.id_comp, Category.id_comp]
  rfl

@[reassoc]
private lemma finite_total_naturality (P : B ⥤ C) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (cP : NonnegativeDerivedTotalizationComparison P)
    {J L : CosimplicialObject (CochainComplex B ℕ)} (g : J ⟶ L) :
    P.mapDerivedCategory.map ((nonnegativeComplexLocalization B).map
        ((nonnegativeCosimplicialTotal B).map g)) ≫
        (exactFiniteTotalLocalizationIso P cP L).hom =
      (exactFiniteTotalLocalizationIso P cP J).hom ≫
        (nonnegativeComplexLocalization C).map ((nonnegativeCosimplicialTotal C).map
          (Functor.whiskerRight g (P.mapHomologicalComplex (.up ℕ)))) := by
  dsimp only [exactFiniteTotalLocalizationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [exact_localization_naturality_assoc, ← Functor.map_comp,
    beta_naturality, Functor.map_comp, Category.assoc]

private lemma post_comparison_naturality (G : A ⥤ B) [G.Additive]
    (cG : NonnegativeDerivedTotalizationComparison G)
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (cP : NonnegativeDerivedTotalizationComparison P)
    {K L : CosimplicialObject (CochainComplex A ℕ)} (f : K ⟶ L)
    (R : NonnegativeCosimplicialResolution A K)
    (T : NonnegativeCosimplicialResolution A L) (g : R.diagram ⟶ T.diagram)
    (hg : R.augmentation ≫ g = f ≫ T.augmentation)
    (M N : DerivedCategory A)
    (a : M ≅ (nonnegativeComplexLocalization A).obj
      ((nonnegativeCosimplicialTotal A).obj K))
    (b : N ≅ (nonnegativeComplexLocalization A).obj
      ((nonnegativeCosimplicialTotal A).obj L)) (m : M ⟶ N)
    (hm : m ≫ b.hom = a.hom ≫ (nonnegativeComplexLocalization A).map
      ((nonnegativeCosimplicialTotal A).map f)) :
    P.mapDerivedCategory.map (G.rightDerivedFunctor.map m) ≫
        (exactPostDerivedTotalComparison G cG P cP L T N b).hom =
      (exactPostDerivedTotalComparison G cG P cP K R M a).hom ≫
        exactPostResolvedTotalMap G P g := by
  have hc : G.rightDerivedFunctor.map m ≫
        (G.rightDerivedFunctor.map b.hom ≫ (cG.chi L T).hom) =
      (G.rightDerivedFunctor.map a.hom ≫ (cG.chi K R).hom) ≫
        (nonnegativeComplexLocalization B).map ((nonnegativeCosimplicialTotal B).map
          (Functor.whiskerRight g (G.mapHomologicalComplex (.up ℕ)))) := by
    calc
      _ = G.rightDerivedFunctor.map (m ≫ b.hom) ≫ (cG.chi L T).hom := by
        simp only [Functor.map_comp, Category.assoc]
      _ = G.rightDerivedFunctor.map a.hom ≫
          (G.rightDerivedFunctor.map ((nonnegativeComplexLocalization A).map
            ((nonnegativeCosimplicialTotal A).map f)) ≫ (cG.chi L T).hom) := by
        rw [hm, Functor.map_comp, Category.assoc]
      _ = _ := by rw [cG.naturality R T f g hg, Category.assoc]
  dsimp only [exactPostDerivedTotalComparison, Iso.trans_hom, Functor.mapIso_hom]
  rw [← P.mapDerivedCategory.map_comp_assoc, hc, P.mapDerivedCategory.map_comp,
    Category.assoc, finite_total_naturality]
  simp only [exactPostResolvedTotalMap, Category.assoc]

omit [Abelian.HasKInjectiveResolutions B] in
@[reassoc]
private lemma nonnegative_unit_naturality (G : A ⥤ B) [G.Additive]
    {X Y : CochainComplex A ℕ} (f : X ⟶ Y) :
    (nonnegativeComplexLocalization B).map
        ((G.mapHomologicalComplex (.up ℕ)).map f) ≫ nonnegativeRightDerivedUnit G Y =
      nonnegativeRightDerivedUnit G X ≫
        G.rightDerivedFunctor.map ((nonnegativeComplexLocalization A).map f) := by
  dsimp only [nonnegativeRightDerivedUnit, nonnegativeComplexLocalization,
    Functor.comp_map]
  rw [← Category.assoc, ← Functor.map_comp]
  have hn := G.rightDerivedFunctorUnitQ_naturality
    ((ComplexShape.embeddingUpNat.extendFunctor A).map f)
  have he :
      ((ComplexShape.embeddingUpNat.extendFunctor B).map
        ((G.mapHomologicalComplex (.up ℕ)).map f)) ≫
          (Y.mapExtendIso ComplexShape.embeddingUpNat G).inv =
        (X.mapExtendIso ComplexShape.embeddingUpNat G).inv ≫
          (G.mapHomologicalComplex (.up ℤ)).map
            ((ComplexShape.embeddingUpNat.extendFunctor A).map f) :=
    (ComplexShape.embeddingUpNat.mapExtendFunctorNatIso G).inv.naturality f
  rw [he, Functor.map_comp, Category.assoc]
  erw [hn]
  simp only [ComplexShape.Embedding.extendFunctor_obj, Category.assoc]

omit [Abelian.HasKInjectiveResolutions B] in
private lemma nonnegative_unit_isIso (G : A ⥤ B) [G.Additive]
    (I : CochainComplex A ℕ) (hI : ∀ q, Injective (I.X q)) :
    IsIso (nonnegativeRightDerivedUnit G I) := by
  let : ∀ q, Injective (I.X q) := hI
  have : CochainComplex.IsKInjective (I.extend ComplexShape.embeddingUpNat) :=
    CochainComplex.isKInjective_of_injective _ 0
  dsimp only [nonnegativeRightDerivedUnit]
  rw [G.rightDerivedFunctorUnitQ_eq]
  infer_instance

omit [Abelian.HasKInjectiveResolutions B] [HasDerivedCategory B]
  [HasDerivedCategory C] in
private lemma extend_composition
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (P : B ⥤ C) [P.Additive] (S : C ⥤ D) [S.Additive]
    (X : CochainComplex B ℕ) :
    (S.mapHomologicalComplex (.up ℤ)).map
        (X.mapExtendIso ComplexShape.embeddingUpNat P).hom ≫
        (((P.mapHomologicalComplex (.up ℕ)).obj X).mapExtendIso
          ComplexShape.embeddingUpNat S).hom ≫
        (ComplexShape.embeddingUpNat.extendFunctor D).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℕ)).hom.app X) =
      (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℤ)).hom.app
          (X.extend ComplexShape.embeddingUpNat) ≫
        (X.mapExtendIso ComplexShape.embeddingUpNat (P ⋙ S)).hom := by
  ext i
  by_cases hi : ∃ q, ComplexShape.embeddingUpNat.f q = i
  · obtain ⟨q, rfl⟩ := hi
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom, NatTrans.id_app,
      ComplexShape.Embedding.extendFunctor_map,
      HomologicalComplex.extendMap_f _ _ rfl]
    dsimp [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents]
    erw [HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f q),
      HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f q),
      HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f q)]
    simp [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToHom_map]
  · apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
      (by simpa using hi)

omit [Abelian.HasKInjectiveResolutions B] in
@[reassoc]
private lemma localization_composition
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (X : CochainComplex B ℕ) :
    (Functor.mapDerivedCategoryCompIso P S).hom.app
        ((nonnegativeComplexLocalization B).obj X) ≫
        S.mapDerivedCategory.map (exactNonnegativeLocalizationIso P X).hom ≫
        (exactNonnegativeLocalizationIso S ((P.mapHomologicalComplex (.up ℕ)).obj X)).hom ≫
        (nonnegativeComplexLocalization D).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℕ)).hom.app X) =
      (exactNonnegativeLocalizationIso (P ⋙ S) X).hom := by
  let := comp_preservesFiniteLimits P S
  let := comp_preservesFiniteColimits P S
  dsimp only [exactNonnegativeLocalizationIso, Iso.trans_hom, Functor.mapIso_hom,
    nonnegativeComplexLocalization, Functor.comp_obj, Functor.comp_map]
  simp only [S.mapDerivedCategory.map_comp, Category.assoc, Iso.app_hom]
  erw [S.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [← Functor.map_comp, ← Functor.map_comp, extend_composition, Functor.map_comp]
  erw [Functor.mapDerivedCategoryCompIso_fac_assoc]
  rfl


private lemma beta_composition
    {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{wD} D] [Abelian.HasKInjectiveResolutions C]
    (P : B ⥤ C) [P.Additive] (cP : NonnegativeDerivedTotalizationComparison P)
    (S : C ⥤ D) [S.Additive] (cS : NonnegativeDerivedTotalizationComparison S)
    (cPS : NonnegativeDerivedTotalizationComparison (P ⋙ S))
    (J : CosimplicialObject (CochainComplex B ℕ)) :
    (S.mapHomologicalComplex (.up ℕ)).mapIso (cP.beta J) ≪≫
        cS.beta (J ⋙ P.mapHomologicalComplex (.up ℕ)) ≪≫
        (nonnegativeCosimplicialTotal D).mapIso
          (Functor.isoWhiskerLeft J (Functor.mapHomologicalComplexCompIso
            (Iso.refl (P ⋙ S)) (.up ℕ))) =
      (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℕ)).app
        ((nonnegativeCosimplicialTotal B).obj J) ≪≫ cPS.beta J := by
  apply Iso.ext
  ext r
  apply beta_ext (P ⋙ S) cPS J r
  intro n q hnq
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Functor.comp_map]
  rw [← S.map_comp_assoc, cP.beta_summand, reassoc_of% (cS.beta_summand _ n q r hnq)]
  dsimp [nonnegativeCosimplicialTotal]
  rw [HomologicalComplex₂.ιTotal_map]
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom,
    NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp]
  exact (cPS.beta_summand J n q r hnq).symm

@[reassoc]
private lemma finite_total_composition
    {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{wD} D] [Abelian.HasKInjectiveResolutions C]
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (cP : NonnegativeDerivedTotalizationComparison P)
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (cS : NonnegativeDerivedTotalizationComparison S)
    (cPS : NonnegativeDerivedTotalizationComparison (P ⋙ S))
    (J : CosimplicialObject (CochainComplex B ℕ)) :
    (Functor.mapDerivedCategoryCompIso P S).hom.app
        ((nonnegativeComplexLocalization B).obj ((nonnegativeCosimplicialTotal B).obj J)) ≫
        S.mapDerivedCategory.map (exactFiniteTotalLocalizationIso P cP J).hom ≫
        (exactFiniteTotalLocalizationIso S cS (J ⋙ P.mapHomologicalComplex (.up ℕ))).hom =
      (exactFiniteTotalLocalizationIso (P ⋙ S) cPS J).hom ≫
        (nonnegativeComplexLocalization D).map
          ((nonnegativeCosimplicialTotal D).map
            (Functor.isoWhiskerLeft J
              (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℕ))).inv) := by
  let := comp_preservesFiniteLimits P S
  let := comp_preservesFiniteColimits P S
  have hb := congrArg Iso.hom (beta_composition P cP S cS cPS J)
  apply (cancel_mono ((nonnegativeComplexLocalization D).map
    ((nonnegativeCosimplicialTotal D).map
      (Functor.isoWhiskerLeft J
        (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℕ))).hom))).mp
  dsimp only [exactFiniteTotalLocalizationIso, Iso.trans_hom, Functor.mapIso_hom] at *
  simp only [S.mapDerivedCategory.map_comp, Category.assoc]
  rw [exact_localization_naturality_assoc]
  rw [← (nonnegativeComplexLocalization D).map_comp_assoc,
    ← (nonnegativeComplexLocalization D).map_comp, Category.assoc, hb,
    (nonnegativeComplexLocalization D).map_comp]
  simp only [Iso.app_hom]
  rw [localization_composition_assoc]
  rw [← (nonnegativeComplexLocalization D).map_comp,
    ← (nonnegativeCosimplicialTotal D).map_comp]
  have hi := (Functor.isoWhiskerLeft J
    (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ S)) (.up ℕ))).inv_hom_id
  apply congrArg ((exactNonnegativeLocalizationIso (P ⋙ S)
    ((nonnegativeCosimplicialTotal B).obj J)).hom ≫ ·)
  simpa only [Functor.map_id, Category.comp_id] using
    congrArg (fun f ↦ (nonnegativeComplexLocalization D).map (cPS.beta J).hom ≫
      (nonnegativeComplexLocalization D).map ((nonnegativeCosimplicialTotal D).map f))
      hi.symm

private lemma post_comparison_composition
    {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{wD} D] [Abelian.HasKInjectiveResolutions C]
    (G : A ⥤ B) [G.Additive] (cG : NonnegativeDerivedTotalizationComparison G)
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (cP : NonnegativeDerivedTotalizationComparison P)
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (cS : NonnegativeDerivedTotalizationComparison S)
    (cPS : NonnegativeDerivedTotalizationComparison (P ⋙ S))
    (K : CosimplicialObject (CochainComplex A ℕ))
    (R : NonnegativeCosimplicialResolution A K) (M : DerivedCategory A)
    (a : M ≅ (nonnegativeComplexLocalization A).obj
      ((nonnegativeCosimplicialTotal A).obj K)) :
    exactCompositePostDerivedTotalComparison G cG P S cPS K R M a =
      exactFurtherPostDerivedTotalComparison G cG P cP S cS K R M a := by
  let := comp_preservesFiniteLimits P S
  let := comp_preservesFiniteColimits P S
  apply Iso.ext
  dsimp only [exactCompositePostDerivedTotalComparison,
    exactFurtherPostDerivedTotalComparison, exactPostDerivedTotalComparison,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso P S).hom.app
    (G.rightDerivedFunctor.obj M))).mp
  simp only [Category.assoc, Iso.app_inv, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  have hn (X Y : DerivedCategory B) (f : X ⟶ Y) :=
    (Functor.mapDerivedCategoryCompIso P S).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% (hn _ _ (G.rightDerivedFunctor.map a.hom)),
    ← reassoc_of% (hn _ _ (cG.chi K R).hom)]
  rw [finite_total_composition]
  rfl


/-- Exact units commute with the coherent derived finite total, and the full square is
compatible with further exact additive postcomposition.

Source: Stacks Project, Derived Categories, Tag 015F, with the agent-formulated finite-total
argument (blueprint: lem-sfb-exact-unit-derived-total-square).

Proof plan, following the seven steps of the node:
1. Naturality of theta at every coface, codegeneracy and internal differential constructs
   exactUnitCosimplicialMap, with the displayed termwise components.
2. Additivity identifies finite biproducts. The beta_summand equation of the recorded
   comparison for H gives E theta = T(e), by testing on every summand injection.
3. Use lem-weil-pbc-localization-universal-property on Q theta and the exact factorization
   of lem-weil-pbc-exact-functor-derived-factorization. Its unique descended transformation
   is thetaD, with the stated normalization on every unbounded complex. Naturality at a
   and the equation in step 2 give localized_unit.
4. Apply lem-sfb-nonnegative-derived-totalization to G and resolve K, HK and e compatibly.
   Its mapReplacement gives compatible. Resolve HK itself, without applying H to a
   resolution of K. The chi naturality and column normalization give column_square.
5. Apply P_D to chi naturality. Its exact descent preserves quasi-isomorphisms. The
   beta_summand identifications move P into every finite total. Substitution of localized_unit
   gives square, with u and w exactly the formulas in exactPostDerivedTotalComparison.
6. The recorded chi uniqueness and naturality give independence of resolutions and the
   displayed naturality equation for maps of K,M,a. The augmentedReplacement and augmentation
   clauses retain the specified degree-zero maps and give augmentation after applying P_D.
   Apply the same assertions to HK and to maps of augmented diagrams to retain both sides.
7. Apply the same finite-summand equations to S. They identify beta_SP with beta_S S(beta_P),
   so the further comparisons, arrows, choice identifications and augmentations are exactly
   the images of the preceding ones. The displayed further square follows by functoriality.
   For slice-module restriction use lem-pur-site-restriction-module-adjunction-exact, whose
   actual restriction is SheafOfModules.overFunctor with its pulled-back ring. All indices
   are nonnegative: splitting an internal resolution adds s with n+q+s=r, a finite set.
   No preservation of injectives by H, P or S and no product totalization is used. -/
theorem exact_unit_derived_total_square
    [IsGrothendieckAbelian.{vA} A] [IsGrothendieckAbelian.{vB} B]
    [IsGrothendieckAbelian.{vC} C]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    (H : A ⥤ A) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (θ : 𝟭 A ⟶ H) :
    Nonempty (ExactUnitDerivedTotalSquare.{uA, vA, wA, uB, vB, wB, uC, vC, wC,
      uD, vD, wD} G H P θ) := by
  classical
  obtain ⟨cG⟩ := nonnegative_derived_totalization G
  obtain ⟨cH⟩ := nonnegative_derived_totalization H
  obtain ⟨cP⟩ := nonnegative_derived_totalization P
  obtain ⟨t, ht, htn⟩ := exists_unit_descent H θ
  have htotal := total_unit_identity H cH θ
  have hloc : ∀ (K : CosimplicialObject (CochainComplex A ℕ))
      (M : DerivedCategory A)
      (a : M ≅ (nonnegativeComplexLocalization A).obj
        ((nonnegativeCosimplicialTotal A).obj K)),
      t.app M ≫ H.mapDerivedCategory.map a.hom ≫
          (exactNonnegativeLocalizationIso H ((nonnegativeCosimplicialTotal A).obj K)).hom ≫
          (nonnegativeComplexLocalization A).map (cH.beta K).hom =
        a.hom ≫ (nonnegativeComplexLocalization A).map
          ((nonnegativeCosimplicialTotal A).map (exactUnitCosimplicialMap H θ K)) := by
    intro K M a
    rw [← t.naturality_assoc]
    dsimp only [Functor.id_map]
    rw [reassoc_of% (htn _), ← Functor.map_comp, ← htotal]
    simp only [Category.assoc]
  refine ⟨{
    comparisonG := cG
    comparisonH := cH
    comparisonP := cP
    thetaD := t
    thetaD_normalized := htn
    strict_components := ?_
    total_unit := htotal
    localized_unit := hloc
    compatible := fun K ↦ cG.mapReplacement (exactUnitCosimplicialMap H θ K)
    compatible_augmented := ?_
    square := ?_
    thetaD_unbounded := ht
    column_square := ?_
    naturality := post_comparison_naturality G cG P cP
    augmentation := ?_
    postcomposition := ?_ }⟩
  · intro K n q
    simp [exactUnitCosimplicialMap]
  · intro X K b
    obtain ⟨⟨I, η, hη, hI, _⟩, _⟩ :=
      exists_cosimplicial_injective_total_replacement A
    let R : NonnegativeCosimplicialResolution A K :=
      ⟨K ⋙ I, Functor.whiskerLeft K η, fun n ↦ hη (K.obj n),
        fun n ↦ hI (K.obj n)⟩
    let T : NonnegativeCosimplicialResolution A (K ⋙ H.mapHomologicalComplex (.up ℕ)) :=
      ⟨(K ⋙ H.mapHomologicalComplex (.up ℕ)) ⋙ I,
        Functor.whiskerLeft (K ⋙ H.mapHomologicalComplex (.up ℕ)) η,
        fun n ↦ hη _, fun n ↦ hI _⟩
    let bH : (Functor.const SimplexCategory).obj
        ((H.mapHomologicalComplex (.up ℕ)).obj X) ⟶
        K ⋙ H.mapHomologicalComplex (.up ℕ) :=
      (Functor.constComp (J := SimplexCategory) X (H.mapHomologicalComplex (.up ℕ))).inv ≫
        Functor.whiskerRight b (H.mapHomologicalComplex (.up ℕ))
    let eX := (Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv.app X ≫
      (NatTrans.mapHomologicalComplex θ (.up ℕ)).app X
    refine ⟨I.obj X, I.obj ((H.mapHomologicalComplex (.up ℕ)).obj X),
      η.app X, η.app _, R, T,
      Functor.whiskerRight (exactUnitCosimplicialMap H θ K) I, I.map eX,
      (Functor.constComp (J := SimplexCategory) X I).inv ≫ Functor.whiskerRight b I,
      (Functor.constComp (J := SimplexCategory) _ I).inv ≫
        Functor.whiskerRight bH I,
      hη _, hη _, hI _, hI _, ?_, ?_, ?_⟩
    · ext n : 1
      exact (η.naturality ((exactUnitCosimplicialMap H θ K).app n)).symm
    · exact (η.naturality eX).symm
    · intro n
      refine ⟨?_, ?_, ?_⟩
      · simpa [R] using η.naturality (b.app n)
      · dsimp only [T, bH, NatTrans.comp_app, Functor.whiskerRight_app,
          Functor.whiskerLeft_app, Functor.constComp_inv_app, Functor.comp_obj,
          Functor.const_obj_obj]
        erw [Category.id_comp, Category.id_comp]
        exact η.naturality ((H.mapHomologicalComplex (.up ℕ)).map (b.app n))
      dsimp [eX, bH]
      simp only [Category.id_comp]
      rw [← I.map_comp, ← I.map_comp]
      congr 1
      ext q
      simpa [exactUnitCosimplicialMap] using θ.naturality ((b.app n).f q)
  · intro K R T g hg M a
    apply post_comparison_naturality G cG P cP (exactUnitCosimplicialMap H θ K)
      R T g hg M (H.mapDerivedCategory.obj M) a _ (t.app M)
    exact hloc K M a
  · intro K R T g hg n
    have hgn := congr_app hg n
    have hnorm := htn (K.obj n)
    have hcol := cG.column_normalized
    have hnat := nonnegative_unit_naturality G (g.app n)
    have : IsIso (nonnegativeRightDerivedUnit G (T.diagram.obj n)) :=
      nonnegative_unit_isIso G _ (T.injective n)
    have hc :
        G.rightDerivedFunctor.map ((nonnegativeComplexLocalization A).map
          ((exactUnitCosimplicialMap H θ K).app n)) ≫ (cG.column _ T).hom.app n =
          (cG.column K R).hom.app n ≫ (nonnegativeComplexLocalization B).map
            ((G.mapHomologicalComplex (.up ℕ)).map (g.app n)) := by
      apply (cancel_mono (nonnegativeRightDerivedUnit G (T.diagram.obj n))).mp
      rw [Category.assoc, hcol, Category.assoc, hnat, ← Category.assoc, hcol,
        ← G.rightDerivedFunctor.map_comp, ← Functor.map_comp,
        ← G.rightDerivedFunctor.map_comp, ← Functor.map_comp]
      exact congrArg (fun f ↦ G.rightDerivedFunctor.map
        ((nonnegativeComplexLocalization A).map f)) hgn.symm
    rw [hnorm]
    have he : (exactUnitCosimplicialMap H θ K).app n =
        (Functor.mapHomologicalComplexIdIso A (.up ℕ)).inv.app (K.obj n) ≫
          (NatTrans.mapHomologicalComplex θ (.up ℕ)).app (K.obj n) := by
      ext q
      simp [exactUnitCosimplicialMap]
    rw [he] at hc
    rw [← P.mapDerivedCategory.map_comp_assoc, hc, P.mapDerivedCategory.map_comp,
      Category.assoc, exact_localization_naturality]
  · intro X I r K R b c hr hi hb
    obtain ⟨a, aI, eX, ha, haI, heX, he⟩ := cG.augmentation X I r K R b c hr hi hb
    refine ⟨a, aI, eX, ha, haI, heX, ?_⟩
    dsimp only [exactPostDerivedTotalComparison, exactFiniteTotalLocalizationIso,
      Iso.trans_hom, Iso.refl_hom, Functor.mapIso_hom]
    simp only [Functor.map_id, Category.id_comp, Functor.map_comp, Category.assoc]
    rw [← P.mapDerivedCategory.map_comp_assoc, he, P.mapDerivedCategory.map_comp,
      Category.assoc, reassoc_of% (exact_localization_naturality P
        ((G.mapHomologicalComplex (.up ℕ)).map aI ≫ (cG.beta R.diagram).hom))]
    simp only [Functor.map_comp, Category.assoc]
  · intro D _ _ _ _ _ S _ _ _
    let := comp_preservesFiniteLimits P S
    let := comp_preservesFiniteColimits P S
    obtain ⟨cS⟩ := nonnegative_derived_totalization S
    obtain ⟨cPS⟩ := nonnegative_derived_totalization (P ⋙ S)
    refine ⟨cS, cPS, beta_composition P cP S cS cPS,
      post_comparison_composition G cG P cP S cS cPS, ?_⟩
    intro K R T g hg M a
    have hs := post_comparison_naturality G cG P cP (exactUnitCosimplicialMap H θ K)
      R T g hg M (H.mapDerivedCategory.obj M) a
      (H.mapDerivedCategory.mapIso a ≪≫
        exactNonnegativeLocalizationIso H ((nonnegativeCosimplicialTotal A).obj K) ≪≫
        (nonnegativeComplexLocalization A).mapIso (cH.beta K)) (t.app M) (hloc K M a)
    dsimp only [exactFurtherPostDerivedTotalComparison, Iso.trans_hom, Functor.mapIso_hom]
    rw [← S.mapDerivedCategory.map_comp_assoc, hs, S.mapDerivedCategory.map_comp,
      Category.assoc]
    change S.mapDerivedCategory.map _ ≫
      S.mapDerivedCategory.map ((nonnegativeComplexLocalization C).map
        ((nonnegativeCosimplicialTotal C).map
          (Functor.whiskerRight (Functor.whiskerRight g (G.mapHomologicalComplex (.up ℕ)))
            (P.mapHomologicalComplex (.up ℕ))))) ≫ _ = _
    rw [finite_total_naturality]
    simp only [exactFurtherResolvedTotalMap, Category.assoc]

end CategoryTheory
