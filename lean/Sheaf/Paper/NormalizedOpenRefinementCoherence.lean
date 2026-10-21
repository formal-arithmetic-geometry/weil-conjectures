/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.IdentityOpenDerivedRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps
import Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-!
# Normalized open refinement arrows

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-cocycle.proof.md, Refinement isomorphisms; and
det-sf-comp-coherence-refinement.proof.md (1), (3)
(blueprint: lem-sfb-normalized-open-refinement-coherence).

The canonical adjunction transpose defines the arrow on ordinary unbounded module-object
derived categories. Its normalization, uniqueness, naturality and composition laws do not
require properness, density, boundedness, constructibility or a field of definition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual open derived adjunction unit is invertible.
Source: blueprint det-sf-comp-coherence-refinement, The restriction to X
(blueprint: lem-sfb-normalized-open-refinement-coherence).

Proof plan (node step 1): choose the reduced closed complement of the quasi-compact open.
Apply lem-sfb-condensed-support-derived-localization to its complementary pair. Its first
clause gives invertibility of the openSupportDerivedAdjunction unit. Transport along
supportPullbackIsoUpperStar, the same canonical alpha identification used by
openSupportDerivedAdjunction in def-sfb-open-closed-internal-hom-comparisons, to the
published derivedOpenImmersionLowerShriekUpperStarAdjunction. No restriction on the
unbounded input or the coefficient ring is needed. -/
theorem normalized_open_refinement_unit_isIso {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] [QuasiCompact j] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  sorry

/-- The open unit, with its actual adjunction map as forward morphism.
Source: blueprint det-sf-comp-coherence-refinement, The restriction to X
(blueprint: lem-sfb-normalized-open-refinement-coherence). -/
noncomputable def normalizedOpenRefinementUnitIso {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] [QuasiCompact j] :
    𝟭 (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ U))) ≅
      (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (upperStar Λ j).mapDerivedCategory :=
  letI := normalized_open_refinement_unit_isIso Λ j
  asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit

/-- The canonical arrow e_h, the adjoint of eta_j' followed by the inverse restriction r_h.
Source: blueprint det-sf-comp-coherence-refinement (1), Uniqueness
(blueprint: lem-sfb-normalized-open-refinement-coherence). -/
noncomputable def normalizedOpenRefinement (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion j'] [QuasiCompact j'] (h : Z' ⟶ Z) (w : j' ≫ h = j)
    (hw : h ⁻¹' Set.range j = Set.range j')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ U))) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj K ⟶
      (lowerStar Λ h).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ j').mapDerivedCategory.obj K) :=
  letI := (identity_open_derived_restriction Λ ℓ hΛ j j' h w hw).1
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv K _).symm
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').unit.app K ≫
      inv ((identityOpenDerivedRestriction Λ j j' h w).app
        ((openImmersionLowerShriek Λ j').mapDerivedCategory.obj K)))

/-- Normalization and uniqueness of the specified adjunction transpose.
Source: blueprint det-sf-comp-coherence-refinement (1), Uniqueness
(blueprint: lem-sfb-normalized-open-refinement-coherence).

Proof plan (steps 1--3): the open units are invertible by the complementary-support
localization lemma, as above. The open adjunction sends a to eta_j followed by j^*(a).
Postcompose with r_h and eta_j' inverse, both invertible, using
lem-sfb-identity-open-derived-restriction. This gives the bijection B_h(K,L) of step 2.
Its inverse sends v to the counit after j_! of v, eta_j' and r_h inverse; the adjunction
triangle identities prove both inverse identities. The definition is B_h(K,K) inverse
of 1_K, which proves normalization; injectivity proves uniqueness. -/
theorem normalized_open_refinement_coherence (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion j'] [QuasiCompact j'] (h : Z' ⟶ Z) (w : j' ≫ h = j)
    (hw : h ⁻¹' Set.range j = Set.range j')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ U))) :
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app K ≫
        (upperStar Λ j).mapDerivedCategory.map
          (normalizedOpenRefinement Λ ℓ hΛ j j' h w hw K) ≫
        (identityOpenDerivedRestriction Λ j j' h w).app
          ((openImmersionLowerShriek Λ j').mapDerivedCategory.obj K) ≫
        (normalizedOpenRefinementUnitIso Λ j').inv.app K = 𝟙 K) ∧
    (∀ a : (openImmersionLowerShriek Λ j).mapDerivedCategory.obj K ⟶
        (lowerStar Λ h).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ j').mapDerivedCategory.obj K),
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app K ≫
          (upperStar Λ j).mapDerivedCategory.map a ≫
          (identityOpenDerivedRestriction Λ j j' h w).app
            ((openImmersionLowerShriek Λ j').mapDerivedCategory.obj K) ≫
          (normalizedOpenRefinementUnitIso Λ j').inv.app K = 𝟙 K →
        a = normalizedOpenRefinement Λ ℓ hΛ j j' h w hw K) := by
  sorry

/-- The normalized refinement arrows are natural in the arbitrary unbounded input.
Source: blueprint det-sf-comp-coherence-refinement (1), used in (2)
(blueprint: lem-sfb-normalized-open-refinement-coherence).

Proof plan (step 4): apply the injective B_h(K,L) from steps 2--3 to both sides.
Naturality of r_h (lem-sfb-identity-open-derived-restriction) and eta_j' makes the first
image v by normalization at K. Naturality of eta_j makes the second image v by
normalization at L. Injectivity proves the equality. -/
theorem normalized_open_refinement_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion j'] [QuasiCompact j'] (h : Z' ⟶ Z) (w : j' ≫ h = j)
    (hw : h ⁻¹' Set.range j = Set.range j')
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ U))} (v : K ⟶ L) :
    normalizedOpenRefinement Λ ℓ hΛ j j' h w hw K ≫
        (lowerStar Λ h).rightDerivedFunctor.map
          ((openImmersionLowerShriek Λ j').mapDerivedCategory.map v) =
      (openImmersionLowerShriek Λ j).mapDerivedCategory.map v ≫
        normalizedOpenRefinement Λ ℓ hΛ j j' h w hw L := by
  sorry

/-- Identity refinement, using exactly the canonical derived direct-image identity.
Source: blueprint det-sf-comp-coherence-refinement (3), Identity and transitivity
(blueprint: lem-sfb-normalized-open-refinement-coherence).

Proof plan (step 5): lem-sfb-module-derived-compositor-coherence supplies
moduleDerivedIdentity and lem-sfb-identity-open-derived-restriction identifies r_1 with
its restriction. Under this comparison the identity of j_!K normalizes to eta_j followed
by its inverse, hence to 1_K. Uniqueness from step 3 proves the displayed equation. -/
theorem normalized_open_refinement_id (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z : Scheme.{u}}
    (j : U ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ U))) :
    normalizedOpenRefinement Λ ℓ hΛ j j (𝟙 Z) (Category.comp_id j) rfl K ≫
        (moduleDerivedIdentity Λ Z).hom.app
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K) =
      𝟙 ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K) := by
  sorry

/-- Transitivity, with the canonical derived direct-image compositor in its stated direction.
Source: blueprint det-sf-comp-coherence-refinement (3), Identity and transitivity
(blueprint: lem-sfb-normalized-open-refinement-coherence).

Proof plan (steps 6--7): on maps into Rh_*Rk_*j''_!K apply the open adjunction followed
by r_h, r_k and eta_j'' inverse. This map T is injective since each postcomposition is
an isomorphism. Naturality of r_h at e_k and normalization of e_h and e_k show that
T(e_h followed by Rh_*(e_k)) is 1_K. The inverse-image conditions compose, so e_hk is
also defined and normalized. The composition law of
lem-sfb-identity-open-derived-restriction, using the compositor of
lem-sfb-module-derived-compositor-coherence, identifies T(kappa followed after e_hk)
with its normalization 1_K. Injectivity of T proves the equation. All steps take place
in ordinary unbounded categories and do not require either e_h or e_k to be invertible. -/
theorem normalized_open_refinement_comp (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) {U Z Z' Z'' : Scheme.{u}}
    (j : U ⟶ Z) (j' : U ⟶ Z') (j'' : U ⟶ Z'')
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion j'] [QuasiCompact j']
    [IsOpenImmersion j''] [QuasiCompact j'']
    (h : Z' ⟶ Z) (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j')
    (k : Z'' ⟶ Z') (w' : j'' ≫ k = j') (hw' : k ⁻¹' Set.range j' = Set.range j'')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ U))) :
    normalizedOpenRefinement Λ ℓ hΛ j j'' (k ≫ h)
        ((Category.assoc j'' k h).symm.trans
          ((congrArg (fun t : U ⟶ Z' ↦ t ≫ h) w').trans w))
        ((congrArg (fun S : Set Z' ↦ k ⁻¹' S) hw).trans hw') K ≫
        (moduleDerivedCompositor Λ k h).hom.app
          ((openImmersionLowerShriek Λ j'').mapDerivedCategory.obj K) =
      normalizedOpenRefinement Λ ℓ hΛ j j' h w hw K ≫
        (lowerStar Λ h).rightDerivedFunctor.map
          (normalizedOpenRefinement Λ ℓ hΛ j' j'' k w' hw' K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
