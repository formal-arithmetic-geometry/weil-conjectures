/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.SourceSectionStalkConeData
import Sheaf.Paper.CompletionUnitStrictQuotientModel

/-! # The identity completion unit in both stalk-cone coordinates -/

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

/-- The actual identity completion unit has a strict lift with zero shifted coordinate,
and this lift represents the specified identity comparison for every good presentation.
Source: Stacks Tags 0F4F, 05V1 and 0941; source-section node, step 2
(blueprint: lem-trf-source-section-identity-model).

Proof: apply completionUnitStrictQuotientModel at Spec k, using the reconstruction
normalization of I to obtain its compatible quotient presentations. On a flat-term K-flat
complex its augmentation sends z to (0,(bar z_n)); exact sections preserve the
products and the zero homotopy. Compose with the identity quotient-section and
normalized germ comparisons. Their naturality makes this a natural transformation
on all complexes. Their two-coordinate normalization gives the displayed coordinate
and zero equations. Use the point-unit equation of the coherent compositor data and
its compatibility with the simultaneous quotient presentation to identify its
localization with the identity realization arrow. Naturality of the actual unit
cancels q against its inverse in that arrow, giving the equation for every q. -/
theorem trfSourceSectionIdentityModel (hl : l ≠ D.p)
    [∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
    (I : IntegralComparisonSystem.{u} l)
    (hI : IntegralComparisonRealizationCoherence l E E (AlgHom.id ℚ_[l] E) I)
    (S : TrfStalkCompositorTowerData l E D I)
    (hC : TrfStalkCompositorTowerCoherent l E D I S)
    (hQ : TrfStalkCompositorQuotientCompatible l E D I S)
    (e : ∀ v : Spec (.of D.k) ⟶ Spec (.of D.k),
      trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v)
    (he : ∀ v : Spec (.of D.k) ⟶ Spec (.of D.k),
        ∃ (γ : ∀ n : ℕ,
            pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
              finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
                (Padic.coefficientExtensionRing l E (n + 1)))
          (δ : ∀ n : ℕ, integralOperationsLevelPullback l E v n ⋙
            pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
              finiteCoefficientModuleStalkFunctor v
                (Padic.coefficientExtensionRing l E (n + 1))),
          TrfQuotientGermNormalized l E D v γ δ (e v)) :
    ∃ a₀ : (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) ⟶
      trfQuotientStalkTower l E (𝟙 (Spec (.of D.k))) ⋙ integralOperationsRoosFunctor,
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (n : ℕ) (i : ℤ)
        (x : ((pointIntegralSections l E D.k).obj (P.X i))),
        HEq (((a₀.app P ≫ CochainComplex.mappingCocone.fst
            (scalarRoosBoundary ((trfQuotientStalkTower l E
              (𝟙 (Spec (.of D.k)))).obj P)) ≫
            Pi.π (fun m ↦ ((trfQuotientStalkTower l E
              (𝟙 (Spec (.of D.k)))).obj P).obj (op m)) n).f i) x)
          ((colimit.ι ((proEtaleGeometricNeighbourhoodForget (𝟙 (Spec (.of D.k)))).op ⋙
            ((((trfQuotientTower l E (Spec (.of D.k))).obj P).obj (op n)).X i).val.presheaf)
              (op (proEtaleConstantGermNeighbourhood (𝟙 (Spec (.of D.k))))))
            (unrestrictedTowerTensorSection l E (Spec (.of D.k)) n (P.X i)
              (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x))) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ),
        (a₀.app P).f (i + 1) ≫
          (CochainComplex.mappingCocone.snd
            (scalarRoosBoundary ((trfQuotientStalkTower l E
              (𝟙 (Spec (.of D.k)))).obj P))).v (i + 1) i (add_neg_cancel_right i 1) = 0) ∧
      (∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ N.obj),
        (pointFibreIntegralAmbient D l E).map
            (X := DerivedCategory.Q.obj P.obj) (Y := N.obj) q.hom ≫
            (pointFibreIntegralAmbient D l E).map
              (X := N.obj)
              (Y := (integralDerivedPullback l E (𝟙 (Spec (.of D.k)))).obj N.obj)
              (integralComparisonUnit l E I (Spec (.of D.k)) N).inv ≫
            trfQuotientStalkRealizationArrow l E D (𝟙 (Spec (.of D.k)))
              (e (𝟙 _)) N.obj P q =
          (trfIntegralSectionsFactors l E D).hom.app P.obj ≫
            (trfIntegralModuleQ l E).map
              (X := ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P.obj)
              (Y := integralOperationsRoos ((trfQuotientStalkTower l E
                (𝟙 (Spec (.of D.k)))).obj P.obj)) (a₀.app P.obj)) := by sorry

end WeilConjectures
