/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.TraceStalkCompositorTowerRealization
public import Sheaf.Paper.GermReparametrizationDerivedDescent
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization

/-! # Source sections in both stalk-cone coordinates

Source: Stacks Project, sites.tex, Tags 0F4F and 05V1; blueprint
thm-trf-l-function-euler-product, Step 1, Local powers (b)
(blueprint: def-trf-source-section-stalk-cone-data).

## Main definitions

* `trfSourceSectionConeLift`: the specified strict restriction-insertion representative.
* `trfSourceSectionJ`, `trfSourceSectionC`: the specified derived comparison arrows.
* `TrfSourceSectionData`, `TrfSourceSectionNormalized`: the comparison families and
  their full chain-coordinate and derived normalization.

## Main statements

* `TrfSourceSectionNormalized`: every required strict and derived normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (D : FiniteFieldDatum.{u})

/-- The specified section-level representative: restrict and insert, apply the
chosen-resolution zero-homotopy comparison, then the two-coordinate section and
finite germ comparisons. Source: Stacks 0F4F, 05V1
(blueprint: def-trf-source-section-stalk-cone-data). -/
def trfSourceSectionConeLift
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (σ : pointIntegralSections l E D.k ≅
      inverseImageIntegralModules l E g ⋙ pointIntegralSections l E D.k)
    (e : trfQuotientSectionTower l E g ≅ trfQuotientStalkTower l E g)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P ⟶
      integralOperationsRoos ((trfQuotientStalkTower l E g).obj P) :=
  (NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P ≫
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
      (X := ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P)
      (Y := (integralOperationsPullbackComplexFunctor l E g).obj P)
      (inverseImageRoosComparisonComplex l E g P) ≫
    scalarRoosMap (pointIntegralSections l E D.k)
      ((integralOperationsPullbackTowerFunctor l E g).obj P) ≫
    integralOperationsRoosMap (e.hom.app P)


/-- The section comparison j is sections of the specified kappa after restriction.
Source: Bhatt--Scholze 6.5.9(4), Stacks 0F4F
(blueprint: def-trf-source-section-stalk-cone-data). -/
def trfSourceSectionJ
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (hS : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x))
    (ρ : pointFibreIntegralAmbient D l E ≅
      inverseImageIntegralDerived l E g ⋙ pointFibreIntegralAmbient D l E)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (pointFibreIntegralAmbient D l E).obj N ⟶
      (trfCompletedPointFibre l E D g).obj N :=
  ρ.hom.app N ≫ (pointFibreIntegralAmbient D l E).map
    (X := (inverseImageIntegralDerived l E g).obj N)
    (Y := (integralDerivedPullback l E g).obj N)
    (inverseImagePullbackComparisonDerived l E g hS hS N)


/-- Insert the identity unit before the inverse specified compositor, retaining
its canonical equality transport from id followed by g to g.
Source: Stacks 0F4F; blueprint Local powers (b)
(blueprint: def-trf-source-section-stalk-cone-data). -/
def trfSourceSectionC
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
    (I : IntegralComparisonSystem.{u} l)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k))
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (trfCompletedPointFibre l E D g).obj N.obj ⟶
      (trfCompletedPointFibre l E D g).obj N.obj :=
  (pointFibreIntegralAmbient D l E).map
    (X := (integralDerivedPullback l E g).obj N.obj)
    (Y := (integralDerivedPullback l E g).obj N.obj)
    ((integralComparisonUnit l E I (Spec (.of D.k))
        ((constructibleIntegralPullback l E g).obj N)).inv ≫
      (integralComparisonComposition l E I (𝟙 (Spec (.of D.k))) g N).inv ≫
      eqToHom (congrArg (fun f ↦ (integralDerivedPullback l E f).obj N.obj)
        (Category.id_comp g)))


/-- The comparison families whose section and cone normalizations are asserted below.
Source: Stacks 0F4F, 05V1; blueprint Local powers (b)
(blueprint: def-trf-source-section-stalk-cone-data). -/
structure TrfSourceSectionData (α : D.k ≃+* D.k) where
  /-- The specified coherent integral pullback calculus. -/
  I : IntegralComparisonSystem.{u} l
  /-- Coherence fixes its units and compositors. -/
  hI : IntegralComparisonRealizationCoherence l E E (AlgHom.id ℚ_[l] E) I
  /-- Restriction and inverse-image insertion on module sections. -/
  σ : pointIntegralSections l E D.k ≅
    inverseImageIntegralModules l E (Spec.map (CommRingCat.ofHom α.toRingHom)) ⋙
      pointIntegralSections l E D.k
  /-- Its ordinary derived descent. -/
  ρ : pointFibreIntegralAmbient D l E ≅
    inverseImageIntegralDerived l E (Spec.map (CommRingCat.ofHom α.toRingHom)) ⋙
      pointFibreIntegralAmbient D l E
  /-- The normalized quotient-stalk comparisons. -/
  e : ∀ v : Spec (.of D.k) ⟶ Spec (.of D.k),
    trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v
  /-- The strict tower reparametrization. -/
  R : trfQuotientStalkTower l E (𝟙 (Spec (.of D.k))) ≅
    trfQuotientStalkTower l E (Spec.map (CommRingCat.ofHom α.toRingHom))
  /-- The completion unit on sections, followed by identity germs. -/
  a₀ : (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) ⟶
    trfQuotientStalkTower l E (𝟙 (Spec (.of D.k))) ⋙ integralOperationsRoosFunctor

/-- The full chain-coordinate and derived normalization, including every representative
and arbitrary derived arrows. Source: Stacks 0F4F, 05V1; blueprint Local powers (b)
(blueprint: def-trf-source-section-stalk-cone-data). -/
structure TrfSourceSectionNormalized
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
    (hS : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x))
    (α : D.k ≃+* D.k) (B : TrfSourceSectionData l E D α) : Prop where
  /-- restriction clause of the specified source-section comparison. -/
  restriction : ∀ (M : integralTowerModules l E (Spec (.of D.k)))
        (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        HEq (B.σ.hom.app M x) (pointRestrictionRaw l E
          (Spec.map (CommRingCat.ofHom α.toRingHom)) none M x)
  /-- restrictionDerived clause of the specified source-section comparison. -/
  restrictionDerived : ∀ P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
        B.ρ.hom.app (DerivedCategory.Q.obj P) ≫
            (pointFibreIntegralAmbient D l E).map
              (X := (inverseImageIntegralDerived l E
                (Spec.map (CommRingCat.ofHom α.toRingHom))).obj (DerivedCategory.Q.obj P))
              (Y := DerivedCategory.Q.obj
                (((inverseImageIntegralModules l E
                  (Spec.map (CommRingCat.ofHom α.toRingHom))).mapHomologicalComplex (.up ℤ)).obj P))
              ((inverseImageIntegralModules l E
                (Spec.map (CommRingCat.ofHom α.toRingHom))).mapDerivedCategoryFactors.hom.app P) ≫
            (trfIntegralSectionsFactors l E D).hom.app
              (((inverseImageIntegralModules l E
                (Spec.map (CommRingCat.ofHom α.toRingHom))).mapHomologicalComplex (.up ℤ)).obj P) =
          (trfIntegralSectionsFactors l E D).hom.app P ≫
            (trfIntegralModuleQ l E).map
              (X := ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P)
              (Y := ((inverseImageIntegralModules l E
                (Spec.map (CommRingCat.ofHom α.toRingHom)) ⋙
                  pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P)
              ((NatTrans.mapHomologicalComplex B.σ.hom (.up ℤ)).app P)
  /-- germNormalization clause of the specified source-section comparison. -/
  germNormalization : ∀ v : Spec (.of D.k) ⟶ Spec (.of D.k),
        ∃ (γ : ∀ n : ℕ,
            pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
              finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
                (Padic.coefficientExtensionRing l E (n + 1)))
          (δ : ∀ n : ℕ, integralOperationsLevelPullback l E v n ⋙
            pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
              finiteCoefficientModuleStalkFunctor v
                (Padic.coefficientExtensionRing l E (n + 1))),
          TrfQuotientGermNormalized l E D v γ δ (B.e v)
  /-- finiteGerm clause of the specified source-section comparison. -/
  finiteGerm : ∃ (γ : ∀ n : ℕ,
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
        finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
          (Padic.coefficientExtensionRing l E (n + 1)))
    (δ : ∀ n : ℕ, integralOperationsLevelPullback l E
      (Spec.map (CommRingCat.ofHom α.toRingHom)) n ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
          finiteCoefficientModuleStalkFunctor (Spec.map (CommRingCat.ofHom α.toRingHom))
            (Padic.coefficientExtensionRing l E (n + 1))),
    TrfQuotientGermNormalized l E D (Spec.map (CommRingCat.ofHom α.toRingHom))
      γ δ (B.e (Spec.map (CommRingCat.ofHom α.toRingHom))) ∧
    ∀ (n : ℕ) (K : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
      (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
      HEq ((δ n).hom.app (K.X i)
        ((((inverseImageFiniteComparisonComplex l E
          (Spec.map (CommRingCat.ofHom α.toRingHom)) n K).f i).val.app
            (op (ProEt.mk (𝟙 (Spec (.of D.k))))))
              (pointRestrictionRaw l E
                (Spec.map (CommRingCat.ofHom α.toRingHom)) (some n) (K.X i) x)))
        (proEtaleCoefficientModuleGerm (Spec.map (CommRingCat.ofHom α.toRingHom))
          (Padic.coefficientExtensionRing l E (n + 1)) (K.X i)
          (proEtaleConstantGermNeighbourhood (Spec.map (CommRingCat.ofHom α.toRingHom))) x)
  /-- reparamGerm clause of the specified source-section comparison. -/
  reparamGerm : ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (n : ℕ) (i : ℤ),
        HEq (((B.R.hom.app P).app (op n)).f i).hom.toFun
          ((proEtaleStalkReparam (Padic.coefficientExtensionRing l E (n + 1))
            (𝟙 (Spec (.of D.k))) α).hom.app
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)).hom.toFun
  /-- identityCoordinate clause of the specified source-section comparison. -/
  identityCoordinate : ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (n : ℕ) (i : ℤ)
        (x : ((pointIntegralSections l E D.k).obj (P.X i))),
        HEq (((B.a₀.app P ≫ CochainComplex.mappingCocone.fst
            (scalarRoosBoundary ((trfQuotientStalkTower l E
              (𝟙 (Spec (.of D.k)))).obj P)) ≫
            Pi.π (fun m ↦ ((trfQuotientStalkTower l E
              (𝟙 (Spec (.of D.k)))).obj P).obj (op m)) n).f i) x)
          ((colimit.ι ((proEtaleGeometricNeighbourhoodForget (𝟙 (Spec (.of D.k)))).op ⋙
            ((((trfQuotientTower l E (Spec (.of D.k))).obj P).obj (op n)).X i).val.presheaf)
              (op (proEtaleConstantGermNeighbourhood (𝟙 (Spec (.of D.k))))))
            (unrestrictedTowerTensorSection l E (Spec (.of D.k)) n (P.X i)
              (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x))
  /-- identityShifted clause of the specified source-section comparison. -/
  identityShifted : ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ),
        (B.a₀.app P).f (i + 1) ≫
          (CochainComplex.mappingCocone.snd
            (scalarRoosBoundary ((trfQuotientStalkTower l E
              (𝟙 (Spec (.of D.k)))).obj P))).v (i + 1) i (add_neg_cancel_right i 1) = 0
  /-- chainNaturality clause of the specified source-section comparison. -/
  chainNaturality : ∀ (P P' : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (h : P ⟶ P'),
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map h ≫
            trfSourceSectionConeLift l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) B.σ
              (B.e (Spec.map (CommRingCat.ofHom α.toRingHom))) P' =
          trfSourceSectionConeLift l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) B.σ
              (B.e (Spec.map (CommRingCat.ofHom α.toRingHom))) P ≫
            integralOperationsRoosMap
              ((trfQuotientStalkTower l E (Spec.map (CommRingCat.ofHom α.toRingHom))).map h)
  /-- derivedNaturality clause of the specified source-section comparison. -/
  derivedNaturality : ∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))) (h : N ⟶ N'),
        (pointFibreIntegralAmbient D l E).map (X := N.obj) (Y := N'.obj) h.hom ≫
            trfSourceSectionJ l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) hS B.ρ N'.obj ≫
            trfSourceSectionC l E D B.I (Spec.map (CommRingCat.ofHom α.toRingHom)) N' =
          trfSourceSectionJ l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) hS B.ρ N.obj ≫
            trfSourceSectionC l E D B.I (Spec.map (CommRingCat.ofHom α.toRingHom)) N ≫
            (trfCompletedPointFibre l E D
              (Spec.map (CommRingCat.ofHom α.toRingHom))).map
                (X := N.obj) (Y := N'.obj) h.hom
  /-- Each e is the isomorphism specified by the bounded-quotient realization. -/
  realizations : ∀ (v : Spec (.of D.k) ⟶ Spec (.of D.k))
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj),
    IsIso (trfQuotientStalkRealizationArrow l E D v (B.e v) N.obj P q)
  /-- representatives clause of the specified source-section comparison. -/
  representatives : ∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ N.obj),
        IsIso (trfSourceSectionJ l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) hS B.ρ N.obj) ∧
        (pointFibreIntegralAmbient D l E).map
            (X := DerivedCategory.Q.obj P.obj) (Y := N.obj) q.hom ≫
            (pointFibreIntegralAmbient D l E).map
              (X := N.obj)
              (Y := (integralDerivedPullback l E (𝟙 (Spec (.of D.k)))).obj N.obj)
              (integralComparisonUnit l E B.I (Spec (.of D.k)) N).inv ≫
            trfQuotientStalkRealizationArrow l E D (𝟙 (Spec (.of D.k)))
              (B.e (𝟙 _)) N.obj P q =
          (trfIntegralSectionsFactors l E D).hom.app P.obj ≫
            (trfIntegralModuleQ l E).map
              (X := ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P.obj)
              (Y := integralOperationsRoos ((trfQuotientStalkTower l E
                (𝟙 (Spec (.of D.k)))).obj P.obj)) (B.a₀.app P.obj) ∧
        (pointFibreIntegralAmbient D l E).map
            (X := DerivedCategory.Q.obj P.obj) (Y := N.obj) q.hom ≫
            trfSourceSectionJ l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) hS B.ρ N.obj ≫
            trfSourceSectionC l E D B.I (Spec.map (CommRingCat.ofHom α.toRingHom)) N ≫
            trfQuotientStalkRealizationArrow l E D
              (Spec.map (CommRingCat.ofHom α.toRingHom))
              (B.e (Spec.map (CommRingCat.ofHom α.toRingHom))) N.obj P q =
          (trfIntegralSectionsFactors l E D).hom.app P.obj ≫
            (trfIntegralModuleQ l E).map
              (X := ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P.obj)
              (Y := integralOperationsRoos ((trfQuotientStalkTower l E
                (Spec.map (CommRingCat.ofHom α.toRingHom))).obj P.obj))
              (trfSourceSectionConeLift l E D
                (Spec.map (CommRingCat.ofHom α.toRingHom)) B.σ
                (B.e (Spec.map (CommRingCat.ofHom α.toRingHom))) P.obj) ∧
        trfSourceSectionConeLift l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) B.σ
            (B.e (Spec.map (CommRingCat.ofHom α.toRingHom))) P.obj =
          B.a₀.app P.obj ≫ integralOperationsRoosMap (B.R.hom.app P.obj)

end WeilConjectures
