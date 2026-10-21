/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ModuleDerivedCompositorCoherence
public import Sheaf.Paper.DerivedDirectImageOpenCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Derived direct image over a common identity open

Source: Stacks Project, sites-cohomology.tex, Tags 0D6G and 0D6E;
blueprint main-20261015, det-sf-comp-coherence-cocycle, Refinement isomorphisms
and Independence (blueprint: lem-sfb-identity-open-derived-restriction).

The maps specialize the existing open-square mates to the identity map of the common
open. Their targets are identified using the existing module direct-image identity
comparisons. Thus all coefficient actions and all derived functors are the published
ones, on the ordinary unbounded categories, with no completion or boundedness condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical underived restriction, followed by the identity direct-image comparison.
Source: Stacks 0D6G and the sectionwise identity direct image
(blueprint: lem-sfb-identity-open-derived-restriction). -/
noncomputable def identityOpenRestriction {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (h : Z' ⟶ Z) (w : j' ≫ h = j) :
    lowerStar Λ h ⋙ upperStar Λ j ⟶ upperStar Λ j' :=
  directImageOpenRestriction Λ (CommSq.mk (w.trans (Category.id_comp j).symm)) ≫
    Functor.whiskerLeft (upperStar Λ j') (lowerStarId Λ U).hom ≫
    (Functor.rightUnitor (upperStar Λ j')).hom

/-- The normalized derived restriction map `r_h`. It is a mate, followed by the
sectionwise-normalized derived identity comparison, rather than a chosen arbitrary map.
Source: Stacks 0D6G and 0D6E
(blueprint: lem-sfb-identity-open-derived-restriction). -/
noncomputable def identityOpenDerivedRestriction {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (h : Z' ⟶ Z) (w : j' ≫ h = j) :
    (lowerStar Λ h).rightDerivedFunctor ⋙ (upperStar Λ j).mapDerivedCategory ⟶
      (upperStar Λ j').mapDerivedCategory :=
  derivedDirectImageOpenRestriction Λ (CommSq.mk (w.trans (Category.id_comp j).symm)) ≫
    Functor.whiskerLeft (upperStar Λ j').mapDerivedCategory
      (moduleDerivedIdentity Λ U).hom ≫
    (Functor.rightUnitor (upperStar Λ j').mapDerivedCategory).hom

/-- The map from `V` to its base change along `h`: identity on `V` and `j' v` on `Z'`.
Its pullback projections specify the identification under which restriction is identity.
Source: Stacks 0D6G, fibre-product computation
(blueprint: lem-sfb-identity-open-derived-restriction). -/
noncomputable def identityOpenSectionArrow {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (h : Z' ⟶ Z) (w : j' ≫ h = j)
    [IsOpenImmersion j] [IsOpenImmersion j'] (V : U.ProEt) :
    (MorphismProperty.Over.map (f := j') ⊤ (inferInstance : WeaklyEtale j')).obj V ⟶
      (Scheme.proEtaleBaseChange h).obj
        ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 V.left) (V.hom ≫ j')
      ((Category.id_comp _).trans
        ((Category.assoc V.hom j' h).trans
          (congrArg (fun t : U ⟶ Z ↦ V.hom ≫ t) w)).symm))
    (pullback.lift_snd _ _ _)

/-- The canonical restriction is invertible, is sectionwise the identity under
`V ×_Z Z' ≅ V`, and is represented by the termwise restriction on every K-injective.
Source: Stacks 0D6G, 079P, 070I and 08BJ
(blueprint: lem-sfb-identity-open-derived-restriction).

Proof plan (steps 1--4 of the node): identify open pullback with slice restriction using
lem-weil-proetale-weakly-etale-localization and lem-sfb-coefficient-sections-localization.
The coefficient comparison is invertible for every commutative condensed ring; module
pullback is exact by det-prop-sfb-module-pullback-exact-main. The inverse-image condition
identifies V ×_Z Z' with V, with inverse (1_V,j'v). Evaluation of the canonical mate gives
the displayed section formula, linear for the pulled-back coefficient actions. Transport
through lem-sfb-internal-module-operations-transport. Take K-injective resolutions by
prop-pur-kinjective-resolutions-exist and compute the ordinary total direct image by
sk-def-sfb-module-derived-pushpull. The termwise comparison localizes to the displayed
formula. The K-injective Hom bijection of lem-weil-pbc-kinjective-hom-derived proves
independence and naturality. Exact module inverse image and its adjunction also give
preservation of K-injectives by direct image (lem-weil-pbc-right-adjoint-preserves-kinjective).
-/
theorem identity_open_derived_restriction (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion j'] [QuasiCompact j'] (h : Z' ⟶ Z) (w : j' ≫ h = j)
    (hw : h ⁻¹' Set.range j = Set.range j') :
    IsIso (identityOpenDerivedRestriction Λ j j' h w) ∧
    IsIso (identityOpenRestriction Λ j j' h w) ∧
    (∀ V : U.ProEt, IsIso (identityOpenSectionArrow j j' h w V)) ∧
    (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z') AddCommGrpCat.{u + 1})
        (condensedRingObj Λ Z')) (V : U.ProEt)
      (s : M.X.obj.obj (op ((Scheme.proEtaleBaseChange h).obj
        ((MorphismProperty.Over.map (f := j) ⊤
          (inferInstance : WeaklyEtale j)).obj V)))),
      ((identityOpenRestriction Λ j j' h w).app M).hom.hom.app (op V)
          (openCoherenceSectionCoprojection Λ j ((lowerStar Λ h).obj M) V s) =
        openCoherenceSectionCoprojection Λ j' M V
          (M.X.obj.map (identityOpenSectionArrow j j' h w V).op s)) ∧
    (∀ (I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology Z') AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z')) ℤ) [I.IsKInjective],
      (identityOpenDerivedRestriction Λ j j' h w).app (DerivedCategory.Q.obj I) ≫
          (upperStar Λ j').mapDerivedCategoryFactors.hom.app I =
        (upperStar Λ j).mapDerivedCategory.map
            ((lowerStar Λ h).rightDerivedFunctorObjQIso I).hom ≫
          (upperStar Λ j).mapDerivedCategoryFactors.hom.app
            (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (identityOpenRestriction Λ j j' h w) (.up ℤ)).app I)) := by
  sorry

/-- Transitivity of the common-open comparison, with the specified derived compositor.
Source: Stacks 0D6G and 0D6E; blueprint Refinement isomorphisms and Independence
(blueprint: lem-sfb-identity-open-derived-restriction).

Proof plan (steps 4--5): take a K-injective I on Z''. The exact-left-adjoint criterion
lem-weil-pbc-right-adjoint-preserves-kinjective makes k_*I K-injective. Thus all three
comparisons are computed on I, k_*I and h_*k_*I with no extra replacement. By
lem-sfb-module-derived-compositor-coherence the compositor is the inverse of the termwise
module compositor. The associator of fibre products identifies the successive inverses
(1_V,j'v) and (1_V,j''v) with (1_V,j''v) for hk: both projections agree. Hence the maps
of complexes agree sectionwise, with the same module actions. Localize and use the
representative formula above; naturality gives the displayed equality of transformations.
-/
theorem identity_open_derived_restriction_comp (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' Z'' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (j'' : U ⟶ Z'')
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion j'] [QuasiCompact j']
    [IsOpenImmersion j'']
    (h : Z' ⟶ Z) (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j')
    (k : Z'' ⟶ Z') (w' : j'' ≫ k = j') (hw' : k ⁻¹' Set.range j' = Set.range j'') :
    identityOpenDerivedRestriction Λ j j'' (k ≫ h)
        ((Category.assoc j'' k h).symm.trans
          ((congrArg (fun t : U ⟶ Z' ↦ t ≫ h) w').trans w)) =
      Functor.whiskerRight (moduleDerivedCompositor Λ k h).hom
          (upperStar Λ j).mapDerivedCategory ≫
        (Functor.associator (lowerStar Λ k).rightDerivedFunctor
          (lowerStar Λ h).rightDerivedFunctor (upperStar Λ j).mapDerivedCategory).hom ≫
        Functor.whiskerLeft (lowerStar Λ k).rightDerivedFunctor
          (identityOpenDerivedRestriction Λ j j' h w) ≫
        identityOpenDerivedRestriction Λ j' j'' k w' := by
  sorry

/-- Identity normalization of the common-open comparison.
Source: Stacks 0D6G and 0D6E
(blueprint: lem-sfb-identity-open-derived-restriction).

Proof plan (step 6): for h = 1_Z the inverse (1_V,jv) is the ordinary identity
base-change identification. The section formula is therefore the sectionwise identity
after lowerStarId. The theorem module_derived_identity_normalization of
lem-sfb-module-derived-compositor-coherence identifies its localization with the
canonical derived identity comparison. Apply the representative formula on every
K-injective and then the K-injective Hom bijection to obtain this natural equality.
No properness, density or field hypothesis enters any step. -/
theorem identity_open_derived_restriction_id (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z : Scheme.{u}}
    (j : U ⟶ Z) [IsOpenImmersion j] [QuasiCompact j] :
    identityOpenDerivedRestriction Λ j j (𝟙 Z) (Category.comp_id j) =
      Functor.whiskerRight (moduleDerivedIdentity Λ Z).hom
          (upperStar Λ j).mapDerivedCategory ≫
        (Functor.leftUnitor (upperStar Λ j).mapDerivedCategory).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
