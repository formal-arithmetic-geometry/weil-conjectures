/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.PurityDncComparisons
public import Sheaf.Paper.PurityDncFamily
public import Sheaf.Paper.PurityNormalCone
import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.FiniteTypeExceptionalInverseImage
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Paper.CohomologicalSmoothComposition
import Sheaf.Paper.CohomologicalSmoothEtaleLocality
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.PurityDncFamilyIntrinsic
import Sheaf.Paper.TwistPreservesFiniteness

/-! # Deformation invariance of the section dualizing object

Source: blueprint sec-smooth-purity/sk-thm-dnc/thm-pur-dnc-invariance.md
(blueprint: thm-pur-dnc-invariance).

The normal cone and DNC are the actual extended-Rees constructions. Normalization
is expressed by reading a family trivialization at 1 and 0 through the canonical
adjunction-mate fibre maps. Quantifying this equation over every finite-type base
change expresses both coordinate normalization and arbitrary base-change compatibility.
The ordinary-etale presentation in this equation is transported by the explicit ν*
comparison; the isomorphism itself is between the actual pro-etale section objects.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.Dnc

/-- Canonical commutation of finite pro-etale pullback with ν*, derived from the
ordinary inverse-image comparison and the exact-functor derivation comparisons.
Source: Bhatt--Scholze comparison; blueprint derived pullback
(blueprint: thm-pur-dnc-invariance). -/
noncomputable def pullComparison (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}}
    (b : B' ⟶ B)
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) b).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj K) ≪≫
    (ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) b).app K ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) b).app K).symm

/-- The canonical comparison of the finite source object with its ν* presentation.
Source: blueprint finite section invariant
(blueprint: thm-pur-dnc-invariance). -/
noncomputable def sourceComparison (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) :
    sourceSection P d g aB s ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
          (sourceEtale P d g aB s) :=
  letI := SmoothOfRelativeDimension.smooth d g
  letI := compactifiable P g aB
  sectionComparison P g aB s

/-- The canonical comparison for the actual normal-bundle zero section.
Source: blueprint finite normal section invariant
(blueprint: thm-pur-dnc-invariance). -/
noncomputable def normalComparison (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    normalSection P d g aB s hs ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
          (normalEtale P d g aB s hs) :=
  letI := normalCompactifiable P d g aB s hs
  sectionComparison P (Scheme.Hom.normalConeProj g s) aB s.normalConeZeroSection

/-- There is a unique coordinate-normalized isomorphism from the section invariant
of a smooth separated finite-type map to that of its normal-bundle zero section.
The equation reads a restricted DNC family trivialization at 1 and 0. It is required
for every k-morphism from a separated finite-type B', including identity, etale, and
nonflat base changes, and for every trivialization of the restricted family pulled
back from B'. In standard coordinates the two readings are the same standard object,
so this equation says that the comparison is its identity. Conversely local standard
coordinates supply such trivializations on a covering, so this is precisely the stated
normalization and naturality, with no auxiliary comparison choices as hypotheses.
Source: blueprint sec-smooth-purity/sk-thm-dnc
(blueprint: thm-pur-dnc-invariance).
Proof:
1. Finite type over k makes B and V Noetherian. The centre (I,t), its blowup, the
   quasi-compact DNC open, and the normal vector bundle stay separated and finite
   type; arbitrary finite-type base changes remain in this domain. The geometry
   lemma identifies the two fibres and the punctured family by canonical mates.
2. The family-constancy proposition gives the unique κ:F≅a*C(g,s), normalized by
   the canonical fibre map at 1. Restrict κ inverse to 0 and compose with the canonical
   fibre map there; use i0*a*=id. This defines the required isomorphism.
3. Etale coordinates near the section give x_i=t*u_i on the DNC. Through open and
   etale exceptional-pullback comparisons this is the standard affine-space family.
   Its readings at 1 and 0 agree, giving the identity normalization. The same argument
   applies after restricting to every trivialization pulled back from any B'.
4. Cancel the common twist and shift in local coordinates. The objects are then
   sheaves of free rank one in degree zero. Fully faithful embedding of these sheaves
   in the derived category and sheaf descent make two normalized morphisms equal.
   This uses faithfulness only on the relevant sheaf Hom, not arbitrary derived Hom.
5. Extended Rees base change and the canonical adjunction-mate fibre comparisons
   commute with arbitrary base change in B. The unique κ normalized at 1 therefore
   restricts to the corresponding κ'. Restriction at 0 gives precisely the displayed
   equation, hence etale localization and nonflat base-change compatibility. -/
theorem existsUnique_dncInvariance (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    ∃! α : sourceSection P d g aB s ≅ normalSection P d g aB s hs,
      ∀ (B' : Scheme.{u}) (aB' : B' ⟶ Spec (.of P.field.k))
        [IsSeparated aB'] [LocallyOfFiniteType aB'] [QuasiCompact aB']
        (b : B' ⟶ B) (_hb : b ≫ aB = aB')
        (C₀ : _root_.DerivedCategory
          (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (e : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
            (familyEtale P d g aB s hs) ≅
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B')).leftDerivedFunctor.obj C₀),
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso α =
          (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
              (sourceComparison P d g aB s) ≪≫
            pullComparison P b (sourceEtale P d g aB s) ≪≫
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
              (Etale.sectionRestrictionIso _ b _ (AffineSpace.oneSection_comp_map b)
                  (AffineSpace.oneSection_comp_over _ B') (fibreOne P d g aB s hs) e ≪≫
                (Etale.sectionRestrictionIso _ b _ (AffineSpace.zeroSection_comp_map b)
                  (AffineSpace.zeroSection_comp_over _ B') (fibreZero P d g aB s hs) e).symm) ≪≫
            ((ProEtale.upperStar
                (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
                (normalComparison P d g aB s hs) ≪≫
              pullComparison P b (normalEtale P d g aB s hs)).symm := by
  sorry

end WeilConjectures.PurityFiniteSetting.Dnc
