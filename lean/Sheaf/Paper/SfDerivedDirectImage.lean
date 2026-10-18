/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage

/-!
# Finite and integral derived direct images with canonical quotient comparisons

Source: Weil blueprint, order 1468; Bhatt--Scholze, Sections 6.5 and 6.7;
Stacks Tags 03DA, 0D6E and 06YY (blueprint: def-weil-derived-direct-image).
The integral object is presented as a chosen Roos triangle, in accordance with the
recorded definition of derived limit; the finite comparison is the adjunct of its
specified projection, rather than a chosen isomorphism of its endpoints.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- The completed coefficient structure map is uniquely determined by its finite
projections and the canonical constant-section maps.
Source: Stacks Tags 03CO and 03DA (blueprint: def-weil-derived-direct-image).
Proof: direct image is a right adjoint and preserves the inverse limit defining
completed coefficients. The constant-section maps commute with quotient maps, so
compose the projections with them and use the universal property of that limit.
Its projections are jointly monic, which proves uniqueness. -/
theorem sfCompletedCoefficientMap_existsUnique :
    ∃! φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X),
      ∀ n : ℕ,
        φ ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
            (completedIntegralCommRingProjectionUnrestricted l E X n) =
          completedIntegralCommRingProjectionUnrestricted l E Y n ≫
            proEtaleCoefficientDirectImageMap f (Padic.coefficientExtensionRing l E (n + 1)) := by
  sorry

/-- The canonical completed-ring map, with its finite-coordinate normalization.
Source: Stacks Tag 03DA (blueprint: def-weil-derived-direct-image). -/
noncomputable def sfCompletedCoefficientMap :=
  (sfCompletedCoefficientMap_existsUnique l E f).exists.choose

/-- Ordinary direct image over completed coefficients, with the canonical ring map.
Source: Stacks Tag 03DA (blueprint: def-weil-derived-direct-image). -/
noncomputable def sfCompletedModuleDirectImage :
    scalarReductionSource.{u, u} l E X ⥤ scalarReductionSource.{u, u} l E Y :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (K := AlgebraicGeometry.Scheme.ProEt.topology X)
    ⟨Functor.whiskerRight (sfCompletedCoefficientMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Completed-coefficient direct image is additive.
Source: Stacks Tag 03DA (blueprint: def-weil-derived-direct-image).
Proof: the functor precomposes the underlying sheaf and its linear maps with base
change. Addition of maps is sectionwise, and scalar restriction respects it. -/
theorem sfCompletedModuleDirectImage_additive : (sfCompletedModuleDirectImage l E f).Additive := by
  sorry

attribute [instance] sfCompletedModuleDirectImage_additive

/-- K-injective resolutions for the same completed coefficient module category.
Source: Stacks Section 07A5 (blueprint: def-weil-derived-direct-image). -/
noncomputable instance sfCompletedHasKInjectiveResolutions (T : AlgebraicGeometry.Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (scalarReductionSource.{u, u} l E T) :=
  proEtaleRingModules_hasKInjectiveResolutions T
    (completedIntegralCommRingSheafUnrestricted l E T)

/-- The ordinary unbounded derived image for completed coefficients.
Source: Stacks Section 07A5 (blueprint: def-weil-derived-direct-image). -/
noncomputable abbrev sfCompletedDerivedDirectImage :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E Y) :=
  (sfCompletedModuleDirectImage l E f).rightDerivedFunctor

/-- The exact finite-coefficient scalar square, normalized by identity on sections.
Source: Stacks Tag 0D6E (blueprint: def-weil-derived-direct-image).
Proof: both functors have sections N(X times_Y V). Compatibility of the completed
ring map with its finite projection makes their scalar actions identical. Identity
on sections therefore gives a linear natural isomorphism, uniquely. -/
theorem sfDirectImageRestrictionComparison_existsUnique (n : ℕ) :
    ∃! e : proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          scalarReductionRestriction.{u, u} l E Y n ≅
        scalarReductionRestriction.{u, u} l E X n ⋙ sfCompletedModuleDirectImage l E f,
      ∀ (M : scalarReductionTarget.{u, u} l E X n) (U : Y.ProEtᵒᵖ)
        (x : M.val.obj ((proEtaleBaseChange f).op.obj U)),
        (e.hom.app M).val.app U x = x := by
  sorry

/-- The uniquely normalized underived coefficient comparison.
Source: Stacks Tag 0D6E (blueprint: def-weil-derived-direct-image). -/
noncomputable def sfDirectImageRestrictionComparison (n : ℕ) :=
  (sfDirectImageRestrictionComparison_existsUnique l E f n).exists.choose

/-- Derived coefficient restriction comparison, normalized on K-injective resolutions.
Source: Stacks Tags 0D6E and 0D6J (blueprint: def-weil-derived-direct-image).
Proof: exact restriction descends termwise. Apply canonical ringed-topos composition
to the two factorizations of the same morphism of ringed topoi. The equality of the
structural maps follows from the finite-coordinate normalization above. Resolve a
finite-coefficient K-injective complex after restriction, and compare both total
right-derived units with the identity-on-sections square. Composition gives the
stated equation. It uniquely determines the isomorphism on K-injective representatives,
hence on every derived object and every roof, without assuming restriction preserves
K-injectives. -/
theorem sfDerivedRestrictionComparison_existsUnique (n : ℕ) :
    ∃! e : scalarReductionDerivedRestriction.{u, u} l E X n ⋙
          sfCompletedDerivedDirectImage l E f ≅
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          scalarReductionDerivedRestriction.{u, u} l E Y n,
      ∀ (J : CochainComplex (scalarReductionTarget.{u, u} l E X n) ℤ) [J.IsKInjective]
        (I : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) [I.IsKInjective]
        (j : ((scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex (.up ℤ)).obj
          J ⟶ I) [QuasiIso j],
        e.hom.app (DerivedCategory.Q.obj J) ≫
            (scalarReductionDerivedRestriction.{u, u} l E Y n).map
              ((proEtaleConstantModuleDirectImage f
                (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctorObjQIso J).hom ≫
            (scalarReductionRestriction.{u, u} l E Y n).mapDerivedCategoryFactors.hom.app
              (((proEtaleConstantModuleDirectImage f
                (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
                  (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (sfDirectImageRestrictionComparison l E f n) (.up ℤ)).hom.app J) ≫
            DerivedCategory.Q.map
              (((sfCompletedModuleDirectImage l E f).mapHomologicalComplex (.up ℤ)).map j) =
          (sfCompletedDerivedDirectImage l E f).map
              ((scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactors.hom.app J) ≫
            (sfCompletedDerivedDirectImage l E f).map (DerivedCategory.Q.map j) ≫
            ((sfCompletedModuleDirectImage l E f).rightDerivedFunctorObjQIso I).hom := by
  sorry

/-- The canonical derived comparison selected by its resolution characterization.
Source: Stacks Tag 0D6E (blueprint: def-weil-derived-direct-image). -/
noncomputable def sfDerivedRestrictionComparison (n : ℕ) :=
  (sfDerivedRestrictionComparison_existsUnique l E f n).exists.choose

/-- The finite derived image of the derived reduction of K at exponent n+1.
Source: blueprint order 1468 (blueprint: def-weil-derived-direct-image). -/
noncomputable abbrev sfFiniteDerivedDirectImage
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1))).obj
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)

/-- The restricted finite-image term in the integral tower.
Source: blueprint order 1468 (blueprint: def-weil-derived-direct-image). -/
noncomputable abbrev sfDirectImageTerm
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (scalarReductionDerivedRestriction.{u, u} l E Y n).obj (sfFiniteDerivedDirectImage l E f K n)

/-- The coefficient transition, transported through the canonical restriction square.
Source: blueprint order 1468 (blueprint: def-weil-derived-direct-image). -/
noncomputable def sfDirectImageTransition
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    sfDirectImageTerm l E f K (n + 1) ⟶ sfDirectImageTerm l E f K n :=
  (sfDerivedRestrictionComparison l E f (n + 1)).inv.app
      ((scalarReductionDerivedExtension.{u, u} l E X (n + 1)).obj K) ≫
    (sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionTransition l E X n).app K) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)

/-- The integral direct image is a derived limit with its specified Roos projection.
Its objects are exactly the chosen derived limits of the finite-image tower; its
projection supplies the canonical finite-reduction comparison.
Source: blueprint order 1468; Bhatt--Scholze, Section 6.5
(blueprint: def-weil-derived-direct-image). -/
structure SfIntegralDirectImage
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    [HasProduct (sfDirectImageTerm l E f K)] where
  obj : DerivedCategory (scalarReductionSource.{u, u} l E Y)
  projection : obj ⟶ ∏ᶜ (sfDirectImageTerm l E f K)
  boundary : (∏ᶜ (sfDirectImageTerm l E f K)) ⟶ obj⟦(1 : ℤ)⟧
  roos : IsDerivedLimitTriangle (sfDirectImageTransition l E f K) obj projection boundary

/-- The actual finite-reduction comparison: the scalar-extension adjunct of the
n-th projection of the specified Roos triangle.
Source: blueprint order 1468; Stacks Tag 07A6
(blueprint: def-weil-derived-direct-image). -/
noncomputable def sfDirectImageReductionComparison
    {K : DerivedCategory (scalarReductionSource.{u, u} l E X)}
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E Y n).obj L.obj ⟶
      sfFiniteDerivedDirectImage l E f K n :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose.homEquiv
    L.obj (sfFiniteDerivedDirectImage l E f K n)).symm
      (L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n)

end WeilConjectures
