/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionOrdinary

/-! # Twisted coordinate-section Kummer normalization

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one and even-shift paragraphs
(blueprint: def-pur-coordinate-section-site-arrows).

The helpers below are the canonical arrows in this normalization statement. In particular,
composition is identified with the identity by conjugating the normalized compact-support
comparison, and the affine comparison is the existing integration transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite

variable (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})

/-- The closed exceptional inverse image in ordinary-adjoint coordinates. This is the
same finite-etale-origin construction as sfFiniteExceptionalAt, with the canonical
proper-compactification comparison already absorbed into the closed adjunction.
Source: blueprint finite exceptional transport
(blueprint: def-pur-coordinate-section-site-arrows). -/
def proClosed :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} T))
      (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  (comparisonLowerStar (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).rightDerivedFunctor ⋙
    (closedImage A T).rightAdjoint ⋙ VectorIntegrationSite.comparison A T

/-- The actual comparison unit at the ordinary p-exceptional value. Inverting this
unit is the only intermediate cancellation in exceptional composition.
Source: blueprint adjunction-preserving composition transport
(blueprint: def-pur-coordinate-section-site-arrows). -/
def middleUnit (K : DerivedCategory
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} A)
    (AffineSpace PUnit.{u + 1} T)).unit.app
      ((compact A T).rightAdjoint.obj
        ((comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor.obj K))

/-- The conjugate composition, transported using precisely the comparison unit and
counit. The invertibility premise concerns the specified unit, not an arbitrary map.
Source: blueprint ps=id, ordinary-origin composition
(blueprint: def-pur-coordinate-section-site-arrows). -/
def proComposition (K : DerivedCategory
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : IsIso (middleUnit A T K)) :
    (proClosed A T).obj
      ((sfFiniteExceptionalAt A (affineTraceLineCompactification T)).obj K) ⟶ K := by
  letI := h
  exact (VectorIntegrationSite.comparison A T).map
      ((closedImage A T).rightAdjoint.map (inv (middleUnit A T K)) ≫
        (exceptionalComposition A T).hom.app _) ≫
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K

/-- Unit and Tate inputs; r=0 is retained separately so the untwisted displayed
identity has exactly the literal unit as its source, without a shift-zero cast.
Source: blueprint A and M_r (blueprint: def-pur-coordinate-section-site-arrows). -/
def IsTateInput (N : ℕ) (hA : (N : A) = 0)
    (M : Etale.DerivedCategoryModule A T) : Prop :=
  M = Etale.ordinaryFiniteUnit A T ∨
    ∃ r : ℕ, M = Etale.SectionLocalDualizingComparisons.tateObject A N hA T r

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Actual gamma with its source expressed as the compared ordinary tensor source.
Source: blueprint site transport of the integration transpose
(blueprint: def-pur-coordinate-section-site-arrows). -/
def gammaCoordinates (b : ℕ)
    (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (M : Etale.DerivedCategoryModule (Ring P) T)
    (hM : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) T M)
    (hplus : DerivedCategory.TStructure.t.plus
      ((VectorIntegrationSite.comparison (Ring P) T).obj M)) :=
  (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
      (CoordinateLine.sourceCoordinates P T b hA M).inv ≫
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T b hA
      ((VectorIntegrationSite.comparison (Ring P) T).obj M) M (Iso.refl _)).hom ≫
    affineLinePurityComparison P T b hA aT
      ⟨(VectorIntegrationSite.comparison (Ring P) T).obj M, hplus⟩ M hM (Iso.refl _)

/-- The closed exceptional adjunct in the finite-origin Hom chain. This uses the
actual comparison unit rho; it is not an assumed ambient pro-etale adjunction.
Source: blueprint u_(s,M) under site comparison
(blueprint: def-pur-coordinate-section-site-arrows). -/
def proOrientation (b : ℕ)
    (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
    (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)))
    (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule (Ring P) T)
    (hpf : IsIso (closedProjection (Ring P) T M)) :=
  (VectorIntegrationSite.comparison (Ring P) T).map
      (ordinaryOrientation (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI M hpf) ≫
    boundedSiteRho (Ring P) (closedImage (Ring P) T).rightAdjoint
      ((CoordinateLine.right (Ring P) (P.coefficients.l ^ (b + 1)) hA T).obj M)

/-- Pro-etale isomorphy and literal derived-morphism identity for both A and every
M_r. The comparison with gamma is the specific published map, with no ramification
hypothesis; all auxiliary boundedness and unit-invertibility facts are conclusions.
Source: blueprint Steps 5--6, 8--9
(blueprint: def-pur-coordinate-section-site-arrows). -/
def ProNormalization (b : ℕ)
    (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)))
    (hI : (sectionMap T).ker.IsInvertible) : Prop :=
  ∀ M : Etale.DerivedCategoryModule (Ring P) T,
    IsTateInput (Ring P) T (P.coefficients.l ^ (b + 1)) hA M →
    ∃ (hM : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (Ring P)) T M)
      (hplus : DerivedCategory.TStructure.t.plus
        ((VectorIntegrationSite.comparison (Ring P) T).obj M))
      (hpf : IsIso (closedProjection (Ring P) T M))
      (hunit : IsIso (middleUnit (Ring P) T
        ((VectorIntegrationSite.comparison (Ring P) T).obj M))),
      IsIso (proOrientation T P b hA hT hI M hpf) ∧
      IsIso (gammaCoordinates T P b hA aT M hM hplus) ∧
      (proOrientation T P b hA hT hI M hpf ≫
        (proClosed (Ring P) T).map (gammaCoordinates T P b hA aT M hM hplus) ≫
        proComposition (Ring P) T _ hunit = 𝟙 _)

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
