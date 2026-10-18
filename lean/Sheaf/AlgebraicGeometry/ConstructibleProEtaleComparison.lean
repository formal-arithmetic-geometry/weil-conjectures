/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical
import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules

/-!
# Constructible comparison for discrete Noetherian coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-thm-pe-constructible-comparison; Stacks Project, Tags 09AJ, 09AK and 09AL
(blueprint: sk-thm-pe-constructible-comparison).

We use the recorded equivalent coefficient-sized sites and intrinsic modules over their
constant ring sheaves. The two full subcategories have all ambient morphisms. The forward
functors are identified with the canonical comparison inverse image, including its
localization on complexes; an arbitrary equivalence of categories would not suffice.

## Main definitions

- `constructibleComparisonRingMap`: the canonical constant-section coefficient map.
- `constructibleComparisonPullback`: the module comparison inverse image.
- `constructibleComparisonComplexPullback`: its termwise action on cochain complexes.

## Main statements

- `constructibleComparison`: local constructibility, classicality and both equivalences.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The constant-section map on the recorded equivalent sites. This is sheafification of
`a ↦` the constant section `a`, along the transported inclusion of etale objects.
Source: Stacks Tags 099R and 00WX; blueprint constructible comparison, proof step 1
(blueprint: sk-thm-pe-constructible-comparison). -/
def constructibleComparisonRingMap (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    siteModuleRings (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⟶
    ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
      RingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj
        (siteModuleRings (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
  (sheafCompose (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).map
    (((sheafificationAdjunction (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      CommRingCat.{max v (u + 1)}).homEquiv
        ((Functor.const (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ).obj
          (CommRingCat.of A))
        ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          CommRingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) |>.obj
            (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, v} X)
              A))).symm
        (Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, v} X).op
          (toSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
            ((Functor.const _).obj (CommRingCat.of A)))))

/-- Module comparison inverse image, constructed by module Kan extension and sheafification.
The ring map is the canonical constant-section map, so this is inverse image with the
canonical identification of the constant coefficient rings. No arbitrary map is chosen.
Source: Stacks Tags 00WX and 03D2; blueprint constructible comparison, proof steps 1 and 3
(blueprint: sk-thm-pe-constructible-comparison). -/
abbrev constructibleComparisonPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) :=
  SheafOfModules.pullback.{max v (u + 1)}
    (F := Scheme.smallModelComparisonInclusion.{u, v} X) (constructibleComparisonRingMap X A)

/-- Termwise comparison pullback on cochain complexes. Zero-morphism preservation is
supplied by Mathlib's theorem for the existing module pullback adjunction, explicitly
rather than by an expensive instance search. No mathematical assertion is postponed here.
Source: Stacks Tag 09AL; blueprint constructible comparison, proof step 4
(blueprint: sk-thm-pe-constructible-comparison). -/
def constructibleComparisonComplexPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
    ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) :=
  @Functor.mapHomologicalComplex ℤ _ _ _ _ _ _ (constructibleComparisonPullback X A)
    (@Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
      (SheafOfModules.pullbackPushforwardAdjunction
        (F := Scheme.smallModelComparisonInclusion.{u, v} X)
        (constructibleComparisonRingMap X A)).isLeftAdjoint) (.up ℤ)

/-- Constructibility is local finite stratification with finite-type constant models.
On qcqs schemes every such module is classical, and comparison induces equivalences on
constructible sheaves and on bounded constructible derived categories.

Source: blueprint main-20261015, sk-thm-pe-constructible-comparison, paragraphs 1--2;
Stacks Tags 09AJ, 09AK and 09AL (blueprint: sk-thm-pe-constructible-comparison).

Proof, following the node's four steps:
1. Over the Noetherian coefficient ring, finite type is equivalent to finite presentation
   (lem-sc-noetherian-finite-module-finite-presentation). Thus the finite models of
   sk-def-sfb-constructible give the recorded affine-local condition. Refine point
   neighborhoods by affine opens using lem-weil-pbc-affine-opens-basis. On qcqs X choose
   a finite affine cover, then use lem-weil-pbc-etale-stratification-local-gluing-core
   to obtain a finite global constructible locally closed stratification factoring
   through the local strata. Pull back the same constant models. Conversely intersect
   global strata with affine opens; constructibility and the constant models restrict.
2. Apply det-pe-constructible-comparison-classical, including its locally stratified
   clause. The continuity map is precisely det-pe-classical-definition-continuity-map:
   sections on stages form a diagram over the opposite cofiltered presentation category,
   and the cocone consists of restriction along its projections. Restrict the intrinsic
   scalar actions along the constant-section unit, using coefficientModelFixedScalars.
   Transport to the equivalent small sites does not change this map.
3. Pullback to each stratum commutes with comparison by sk-thm-pe-direct-image-comparison.
   Apply det-pe-finite-local-systems-twist and finite type = finite presentation to the
   local models. Comparison is fully faithful by det-pe-classical-sheaves-modules.
   For constructible F, its classicality gives nu* nu_* F isomorphic to F. On every
   stratum the local-system comparison and full faithfulness show that nu_* F has the
   same finite constant models. Hence nu_* F is etale constructible, proving the first
   equivalence with forward functor the specified module inverse image.
4. By sk-prop-sf-comparison the derived unit is invertible; apply
   det-pe-classical-derived-equivalence. Exact inverse image commutes with every
   cohomology functor and preserves the finite interval of vanishing. Step 3 identifies
   the constructible cohomology sheaves on both sides. Conversely classicality from
   step 2 supplies a bounded-below etale antecedent; full faithfulness reflects zero
   cohomology outside the finite interval and step 3 reflects constructibility inside.
   Restrict to the full bounded constructible subcategories. Localization identifies
   the derived forward functor on every cochain complex with termwise inverse image,
   as expressed by the first natural isomorphism in the final clause. -/
theorem constructibleComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F ↔
        ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ S : Scheme.LocallyClosedStratification U.toScheme,
            (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
            ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
              (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain a)) A
              ((Scheme.coefficientProEtaleFixedModulePullback.{u, v}
                (S.immersion a ≫ U.ι) A).obj
                  ((coefficientModelFixedScalars _ A).obj F))) ∧
    (∀ [CompactSpace X] [QuasiSeparatedSpace X],
      (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F →
          ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
            (P : AffinePresentation X I),
            IsIso (continuityMap P
              ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
                ((coefficientModelFixedScalars _ A).obj F).obj))) ∧
      (∃ e : Scheme.CoefficientConstructibleEtaleModuleCategory.{u, v} X A ≌
          ObjectProperty.FullSubcategory
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A),
        Nonempty (e.functor ⋙
          ObjectProperty.ι
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A) ≅
            ObjectProperty.ι (Scheme.IsCoefficientConstructibleEtaleModule X A) ⋙
              constructibleComparisonPullback X A)) ∧
      (∃ D : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
            ConstantCompletion.D (ConstantCompletion.constant
              (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Nonempty (ConstantCompletion.Q _ ⋙ D ≅
          constructibleComparisonComplexPullback X A ⋙
            ConstantCompletion.Q _) ∧
        ∃ e : Scheme.CoefficientBoundedConstructibleEtaleCategory.{u, v} X A ≌
            (coefficientBoundedConstructibleProEtale X A).FullSubcategory,
          Nonempty (e.functor ⋙ (coefficientBoundedConstructibleProEtale X A).ι ≅
            ObjectProperty.ι (Scheme.IsCoefficientBoundedConstructibleEtale X A) ⋙ D))) := by
  sorry

end AlgebraicGeometry.ProEtale
