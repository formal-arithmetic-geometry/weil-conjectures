/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.MappedSmartTruncationTower
public import Sheaf.CategoryTheory.SpecifiedResolutionDerivedSingle
public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
import Sheaf.CategoryTheory.CartanEilenbergTruncationResolution
import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import Sheaf.CategoryTheory.DerivedUpperTruncationComparison
import Sheaf.CategoryTheory.FilteredComplexDecalageTower

/-! Comparing resolved smart-truncation towers with the canonical derived spectral object. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uA vA uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
  [HasDerivedCategory B] [HasDerivedCategory C]

/-- Apply derived G and cohomology to the canonical truncation spectral object. -/
noncomputable def derivedTruncationSpectralObjectFunctor (G : B ⥤ C) [G.Additive] :
    DerivedCategory.Plus B ⥤ Abelian.SpectralObject C EInt :=
  DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
    G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt ⋙
    (DerivedCategory.Plus.homologyFunctor C 0).mapHomologicalSpectralObject EInt

/-- The spectral object of the totals of the smart horizontal cuts computes derived G
of the canonical truncation intervals of the resolved image complex.
Source: Stacks Project, Tag 015X, Remark 13.26.15; Tag 015K, Remark 13.21.4
(blueprint: lem-sp-ce-smart-truncation-spectral-object).

Proof. For each integer b, finite diagonals identify the total of the mapped
CE smart cut at b-1 with G of the total of that CE smart cut.
The CE truncated augmentation makes that latter
total an injective resolution of the smart cut of F(J). These augmentations commute
with cutoff maps and presentation comparisons by cancellation of their monic
inclusions and the total-coordinate formulas. The cone of each square of these
augmentations is a quasi-isomorphism between bounded-below cones, and its target
is termwise injective. The inverse derived unit therefore computes derived G
on every interval cone, naturally for squares of intervals. Compare the localized
smart-cut cone triangle with the canonical truncation triangle: the normalized
first two maps uniquely determine its third map by t-structure orthogonality.
For triples of cutoffs, the same uniqueness compares the cone octahedron with
the truncation triangles, including the connecting arrows. At minus infinity use
the zero complex and at plus infinity the full CE total resolution. Applying
cohomology gives the asserted spectral-object morphism. On bottom intervals it
is the composite of the specified-resolution isomorphism and the unique
cochain/derived upper-truncation isomorphism. Naturality follows from all the
normalized augmentation squares above. This comparison stops at Q(F(J)); it does
not identify that object with RF(X) or use any filtered complex. -/
theorem cartanEilenberg_smartTruncation_spectralObject_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∃ e : ∀ P : CartanEilenbergPresentation F,
      (cochainTowerSpectralObjectFunctor C).obj
          (CartanEilenbergPresentation.mappedSmartTruncationTower G P.I) ⟶
        (derivedTruncationSpectralObjectFunctor G).obj
          (DerivedCategory.Plus.Q.obj (F.specifiedResolutionComplex P.J)),
      (∀ (P : CartanEilenbergPresentation F) (n : ℤ) (b : EInt),
        IsIso (((e P).hom n).app (ComposableArrows.mk₁
          (homOfLE (bot_le : (⊥ : EInt) ≤ b))))) ∧
      ∀ (P Q : CartanEilenbergPresentation F) (d : P.Comparison Q),
        (cochainTowerSpectralObjectFunctor C).map
            (CartanEilenbergPresentation.mappedSmartTruncationTowerMap G d.α) ≫ e Q =
          e P ≫ (derivedTruncationSpectralObjectFunctor G).map
            (DerivedCategory.Plus.Q.map (ObjectProperty.homMk
              ((F.mapHomologicalComplex (.up ℤ)).map
                (HomologicalComplex.extendMap d.β ComplexShape.embeddingUpNat)) :
              F.specifiedResolutionComplex P.J ⟶ F.specifiedResolutionComplex Q.J)) := by
  sorry

end CategoryTheory
