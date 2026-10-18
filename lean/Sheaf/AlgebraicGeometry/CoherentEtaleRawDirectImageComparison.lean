/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X5
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The coherent comparison before sheafification

Source: Stacks Project, Tags 03P2, 03Q8, 01XK, 02KH, 02N7 and 01F2.
(blueprint: lem-weil-pbc-coherent-etale-raw-direct-image-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The raw cohomology presheaf maps locally bijectively to the tensor-section sheaf
of its Zariski higher image, with the scalar normalization on restricted coefficients.
This statement involves no smoothness, properness, dimension, or local freeness.

Source: Stacks Project, Tag 03P2 (quasi-coherent comparison), Tag 03Q8 (higher-image
presheaf), Tag 01XK (affine-base sections), Tags 02KH and 02N7
(flat base change and its canonical map), and Tag 01F2 (Leray).
(blueprint: lem-weil-pbc-coherent-etale-raw-direct-image-comparison).

Proof: Put E = R^q f_* O_X. It is quasi-coherent for a qc separated morphism.
For an affine etale object v : V -> S, put p : X_V -> V and j : X_V -> X.
Flat base change identifies v^*E with R^q p_* O_X_V; the tensor-unit map identifies
j^*O_X with O_X_V. The affine Leray edge is invertible because all higher images
are quasi-coherent and have zero positive cohomology on V. Compose raw evaluation,
localization of the additive structure sheaf, the quasi-coherent etale/Zariski
cohomology comparison, this Leray edge, and inverse flat base change. This gives
an additive bijection from raw classes over V to ULift Gamma(V,v^*E).
For an arrow of affine etale objects, the normalized cohomology pullback square
and composition of the base-change adjunction units identify the two composites.
Thus these bijections commute with restrictions. For an arbitrary etale U,
restrict a raw class to affine opens of U and glue their images. On overlaps
check equality after further affine refinement. Sheaf uniqueness makes the glued
map independent of the cover and natural for every etale arrow. Its affine
components are bijective, so it is locally injective and locally surjective.
For a base function a, the displayed coefficient normalization identifies mu
with multiplication by the pullback of a under localization: the localization
map is an isomorphism on every test object. Coefficient naturality of etale/Zariski
comparison and linearity of the Leray and flat-base-change maps therefore give
the scalar formula on each affine open. Restricting the assumed equality of raw
evaluations and using naturality gives that formula on every affine refinement
of U. The tensor-section sheaf's uniqueness axiom then gives the equality on U.
All maps include the same explicit sectionwise ULift; no coefficient-universe
identification is implicit. Empty objects and q=0 use the same construction. -/
theorem exists_coherent_etale_raw_direct_image_comparison
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    [HasInjectiveResolutions X.Modules] (q : ℕ) :
    let E := (Scheme.Modules.higherDirectImage f q).obj
      (SheafOfModules.unit X.ringCatSheaf)
    let _ : E.IsQuasicoherent := Scheme.Modules.isQuasicoherent_higherDirectImage f
      (SheafOfModules.unit X.ringCatSheaf) q
    ∃ b : abelianHigherDirectImageRawPresheaf f q X.etaleAdditiveSheaf ⟶
        (Scheme.Modules.liftedCoherentEtaleSheaf E).obj,
      Presheaf.IsLocallyInjective S.smallEtaleTopology b ∧
      Presheaf.IsLocallySurjective S.smallEtaleTopology b ∧
      ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
        (μ : (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
            X.etaleAdditiveSheaf ⟶
          (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
            X.etaleAdditiveSheaf),
        (∀ (T : (pullback U.hom f).Etale)
          (x : ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
            X.etaleAdditiveSheaf).obj.obj (op T)),
          (((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
            (pullback.snd U.hom f) inferInstance).hom.app
              X.etaleAdditiveSheaf).hom.app (op T)) (μ.hom.app (op T) x) =
          ULift.up (@id Γ(T.left, ⊤) ((T.hom ≫ pullback.fst U.hom f).appTop a) *
            (@id Γ(T.left, ⊤) ((((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
              (pullback.snd U.hom f) inferInstance).hom.app
                X.etaleAdditiveSheaf).hom.app (op T)) x).down))) →
        ∀ (z z' : (abelianHigherDirectImageRawPresheaf f q
            X.etaleAdditiveSheaf).obj (op U)),
          rawRestrictedCohomologyComparison f q X.etaleAdditiveSheaf U z' =
            (cohomology AddCommGrpCat.{u + 1} (pullback U.hom f) q).map
              (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map μ))
              (rawRestrictedCohomologyComparison f q X.etaleAdditiveSheaf U z) →
          b.app (op U) z' = ULift.up
            (a • @id Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)
              (b.app (op U) z).down) := by
  sorry

end AlgebraicGeometry.Etale
