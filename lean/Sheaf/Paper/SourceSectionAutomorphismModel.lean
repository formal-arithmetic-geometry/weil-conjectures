/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.SourceSectionStalkConeData
import Sheaf.Paper.QuotientTensorInsertion
import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence

/-! # Restriction-insertion and the automorphism germ comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
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

/-- On a normalized identity lift, restriction-insertion gives the reparametrized
whole cone and the specified derived representative; the finite insertion has its
explicit pointed-germ formula. This does not construct the identity lift or its
completion-unit normalization.
Source: Stacks Tags 0F4F and 05V1; source-section node, steps 3--6
(blueprint: lem-trf-source-section-automorphism-model).

Proof: at finite level restriction along g followed by insertion and tensoring with
1 is the pullback-unit generator at the graph of g. The normalized finite comparison
sends it to [V,id,a|g], which equals [s,g,a] by the pointed neighbourhood arrow g.
Quotient-tensor insertion commutes with the tower transitions, so these generators
form a compatible product and define the zero-homotopy cone lift. Germ
reparametrization sends [s,id,bar z_n] to [s,g,bar z_n]. Thus the two lifts agree
after every unshifted product projection; both shifted coordinates vanish. The
biproduct identity and joint monicity of the product projections give equality of
whole chain maps. For a good presentation q, the chosen-resolution kappa cancels
G(q) from restriction naturality. Apply the normalized compositor realization and
its quotient compatibility to identify the remaining localized chain map with the
displayed source representative. The normalization of kappa makes it invertible
on derived-complete constructible objects, as is the restriction isomorphism.
All equations hold for every presentation, by the same cancellation. -/
theorem trfSourceSectionAutomorphismModel (hl : l ≠ D.p)
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
    (hS : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x))
    (α : D.k ≃+* D.k) (B : TrfSourceSectionData l E D α)
    (S : TrfStalkCompositorTowerData l E D B.I)
    (hC : TrfStalkCompositorTowerCoherent l E D B.I S)
    (hQ : TrfStalkCompositorQuotientCompatible l E D B.I S)
    (hrestriction : ∀ (M : integralTowerModules l E (Spec (.of D.k)))
        (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        HEq (B.σ.hom.app M x) (pointRestrictionRaw l E
          (Spec.map (CommRingCat.ofHom α.toRingHom)) none M x))
    (hrestrictionDerived : ∀ P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
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
              ((NatTrans.mapHomologicalComplex B.σ.hom (.up ℤ)).app P))
    (hgermNormalization : ∀ v : Spec (.of D.k) ⟶ Spec (.of D.k),
        ∃ (γ : ∀ n : ℕ,
            pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
              finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
                (Padic.coefficientExtensionRing l E (n + 1)))
          (δ : ∀ n : ℕ, integralOperationsLevelPullback l E v n ⋙
            pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
              finiteCoefficientModuleStalkFunctor v
                (Padic.coefficientExtensionRing l E (n + 1))),
          TrfQuotientGermNormalized l E D v γ δ (B.e v))
    (hreparamGerm : ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (n : ℕ) (i : ℤ),
        HEq (((B.R.hom.app P).app (op n)).f i).hom.toFun
          ((proEtaleStalkReparam (Padic.coefficientExtensionRing l E (n + 1))
            (𝟙 (Spec (.of D.k))) α).hom.app
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)).hom.toFun)
    (hidentityCoordinate : ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
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
              (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x)))
    (hidentityShifted : ∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ),
        (B.a₀.app P).f (i + 1) ≫
          (CochainComplex.mappingCocone.snd
            (scalarRoosBoundary ((trfQuotientStalkTower l E
              (𝟙 (Spec (.of D.k)))).obj P))).v (i + 1) i (add_neg_cancel_right i 1) = 0)
    : (∃ (γ : ∀ n : ℕ,
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
          (proEtaleConstantGermNeighbourhood (Spec.map (CommRingCat.ofHom α.toRingHom))) x)) ∧
      (∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ N.obj),
        IsIso (trfSourceSectionJ l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) hS B.ρ N.obj) ∧
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
                (B.e (Spec.map (CommRingCat.ofHom α.toRingHom))) P.obj) ) ∧
      (∀ P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
        trfSourceSectionConeLift l E D (Spec.map (CommRingCat.ofHom α.toRingHom)) B.σ
            (B.e (Spec.map (CommRingCat.ofHom α.toRingHom))) P =
          B.a₀.app P ≫ integralOperationsRoosMap (B.R.hom.app P)) := by sorry

end WeilConjectures
