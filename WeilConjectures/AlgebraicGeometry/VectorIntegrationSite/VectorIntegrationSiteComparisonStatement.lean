/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison

/-! # Finite or algebraically closed site comparison statement

Source: literature/stacks-project/proetale.tex, Tags 09AF and 099R, together
with categories.tex Tag 0B65 (blueprint: lem-pur-vector-integration-site-comparison).
The existing comparison coordinates are assembled here into the statement for a
finite or algebraically closed ground field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The finite-level comparison clauses for a finite or algebraically closed field.

Source: Stacks 09AF and 099R, categories.tex Tag 0B65, and the comparison
paragraph of `cor-pur-affine-space-zero-section-purity`
(blueprint: lem-pur-vector-integration-site-comparison).

The first conjunct records the normalized projective, global integration, and
finite-Tor tensor comparisons. The second records independence of the
annihilating exponent for the vector integration. The open counit conjunct
records the actual extension-by-zero counit. The final conjunct records the
canonical root-normalized twist comparisons, their pullback compatibility, and
exponent transitions. Every map is the existing canonical map named by the
dependency nodes; this proposition introduces no new sites, twists, or maps.
-/
def GenericSiteComparison (k : Type u) [Field k]
    (_hfield : Finite k ∨ IsAlgClosed k) (_hchar : ringChar k ≠ l)
    (S : Scheme.{u}) (aS : S ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (hN : IsNoetherian S) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop := by
  letI : IsNoetherian S := hN
  exact ∃ hS : IsUnit (l : Γ(S, ⊤)),
    (∀ (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0),
      ProjectiveCompatibility l E n S hS (infinityCartier S) r hA ∧
      IntegrationCompatibility l E n S hS r hA d F ∧
      ∀ (K : Etale.DerivedCategoryModule
        (Scheme.finiteTateCoefficient l E n) S)
        (hK : Etale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S K),
        TensorCompatibility l E n S hS r hA d F K hK) ∧
    (∀ (r r' : ℕ) (h : r ≤ r')
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
      (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0),
      ((rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (Etale.vectorBundlePurityCompactification S d F)).map
      ((comparison (Scheme.finiteTateCoefficient l E n) _).map
        ((Etale.ordinaryFinitePullback _ (VectorBundleZeroSection.π S d F)).map
          (baseExponentComparison l E n S hS r r' h hA hA' d).hom)) ≫
      vectorIntegration l E n S r hA d F hS =
        vectorIntegration l E n S r' hA' d F hS)) ∧
    (∀ (G : DerivedCategory (Sheaf (ProjectiveLine S).smallEtaleTopology
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))),
      (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
          (((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
            (ProjectiveLine.affineChart S)).ofNatIsoRight
              (Etale.leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
                (ProjectiveLine.affineChart S)).symm).counit.app G) =
        (openProjectionExtensionComparison (Scheme.finiteTateCoefficient l E n)
          (ProjectiveLine.affineChart S)).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
            (ProjectiveLine.affineChart S)).leftDerivedFunctor.obj G) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (ProjectiveLine.affineChart S)).mapDerivedCategory.map
          ((openProjectionRestrictionComparison (Scheme.finiteTateCoefficient l E n)
            (ProjectiveLine.affineChart S)).hom.app G) ≫
        (openAdjunction (Scheme.finiteTateCoefficient l E n)
          (ProjectiveLine.affineChart S)).counit.app
          ((comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).obj G)) ∧
    ((∀ (T : Scheme.{u}) (_aT : T ⟶ S) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      Scheme.IsFiniteTateSiteComparison l E n T r hA k (twistComparison l E n T hT r hA k)) ∧
    (∀ (T T' : Scheme.{u}) (aT : T ⟶ S) (aT' : T' ⟶ S)
      (v : T' ⟶ T) (_hv : v ≫ aT = aT')
      (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
      (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃ (c : (Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).obj
          (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
            Scheme.finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k)
        (d : (ProEtale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).obj
          (Scheme.finiteTateProSheaf l E n T k) ≅ Scheme.finiteTateProSheaf l E n T' k),
      Scheme.IsFiniteTateEtalePullback l E n T v r hA k c ∧
      Scheme.IsFiniteTateProPullback l E n T v k d ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).mapIso
          (twistComparison l E n T hT r hA k) ≪≫ d =
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).app
            (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T').mapIso c ≪≫
          twistComparison l E n T' hT' r hA k) ∧
    (∀ (T : Scheme.{u}) (_aT : T ⟶ S) (hT : IsUnit (l : Γ(T, ⊤)))
      (r r' : ℕ) (_h : r ≤ r')
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
      (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃! t : Scheme.finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
          Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k,
        Scheme.IsFiniteTateEtaleTransition l E n T r r' hA hA' k t ∧
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).mapIso t ≪≫
            twistComparison l E n T hT r hA k =
            twistComparison l E n T hT r' hA' k))

/- The theorem is intentionally statement-only at stage 2. -/
end AlgebraicGeometry.ProEtale.VectorIntegrationSite
