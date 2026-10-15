/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import Sheaf.AlgebraicGeometry.ClopenSectionDirectImage
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProperOpenSection
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Composition and identity of proper-open comparison maps

Source: blueprint sec-smooth-purity/sk-def-sf-operations,
lem-weil-pbc-proper-open-comparison-composition, order 1483
(blueprint: lem-weil-pbc-proper-open-comparison-composition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical composition identification for bounded below derived direct images.
Source: Stacks Project, Tag 0D6E, and the composition identification in blueprint
lem-weil-pbc-proper-open-comparison-composition
(blueprint: lem-weil-pbc-proper-open-comparison-composition).
It derives the fibre-product-pasting isomorphism `lowerStarComp` on injectives.
The injective-preservation structure comes from the exact inverse-image adjunction. -/
noncomputable def properOpenDirectImageCompIso (Λ : Type (u + 1)) [CommRing Λ]
    {T₁ T₂ T₃ : Scheme.{u}} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g ≅
      rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (f ≫ g) := by
  letI : (lowerStar (ModuleCat.{u + 1} Λ) f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  exact Functor.rightDerivedFunctorPlusCompIso'
    (lowerStar (ModuleCat.{u + 1} Λ) f) (lowerStar (ModuleCat.{u + 1} Λ) g)
    (lowerStarComp (ModuleCat.{u + 1} Λ) f g)

/-- Proper-open comparisons compose, using the canonical derived direct-image identification.
Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1483
(blueprint: lem-weil-pbc-proper-open-comparison-composition).

Proof:
1. Choose a bounded below injective representative I of an arbitrary L, using
lem-weil-pbc-dplus-injective-representative. The section
W → W ×[T_b] T_a induced by (id,j_a) gives a linear restriction map
 t_w : j_b⁻¹ Rw_* L → j_a⁻¹ L. Restriction commutes with differentials and
homotopies; lem-weil-pbc-kinjective-hom-derived gives independence and naturality.
Use def-weil-pbc-direct-image, lem-weil-pbc-open-immersion-etale,
lem-weil-pbc-etale-inverse-image-restriction and
prop-weil-pbc-inverse-image-modules-exact for these computations.
2. For L = j_a! K, the clopen distinguished section and the sectionwise identity
of derived open restriction identify t_w with the specified theta, by
lem-weil-pbc-proper-open-section, lem-weil-pbc-etale-restriction-injectives,
lem-weil-pbc-derived-open-restriction, lem-weil-pbc-clopen-section-direct-image
and lem-weil-pbc-proper-open-identification.
3. By lem-weil-pbc-direct-image-preserves-injectives, f_* I computes the second
pushforward as well. The fibre-product associator identifies successive section
restrictions with the section for f ≫ g, since j₁ ≫ f = j₂ and j₂ ≫ g = j₃.
Contravariant functoriality gives t_(fg) = t_g followed by t_f.
Use lem-weil-pbc-inverse-image-composition-module-linear for linearity and
lem-weil-pbc-right-derived-plus-injective for the canonical normalization.
4. The open extension-by-zero adjunction has identity unit after j⁻¹j! ≅ id,
by cor-cbc-derived-extension-zero-base-change and the sectionwise transpose in
lem-weil-pbc-extension-by-zero-adjunction. Thus the restriction of alpha_w is
theta_w inverse, and this restriction detects equality of maps out of j_b! K.
5. Naturality of t_g at alpha_f and step 3 show that theta_(fg) composed with
the restriction of alpha_g followed by Rg_*(alpha_f) is id_K, just as for
alpha_(fg). Cancel theta_(fg), then use the adjunction bijection of step 4.
The composite is proper by lem-weil-pbc-proper-composition. -/
theorem properOpenComparison_comp (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ T₃ X : Scheme.{u}} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
    [IsProper f] [IsProper g]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (j₃ : X ⟶ T₃)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (hf : j₁ ≫ f = j₂) (hg : j₂ ≫ g = j₃)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenComparison Λ (f ≫ g) j₁ j₃
        ((Category.assoc j₁ f g).symm.trans ((congrArg (· ≫ g) hf).trans hg)) K =
      properOpenComparison Λ g j₂ j₃ hg K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g).map
          (properOpenComparison Λ f j₁ j₂ hf K) ≫
        (properOpenDirectImageCompIso Λ f g).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K) := by
  sorry

/-- The proper-open comparison for the identity, under R(id)_* ≅ id, is the identity.
Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1483, final sentence
(blueprint: lem-weil-pbc-proper-open-comparison-composition).

Proof (step 6 of the node): For w = id the section W → W ×[T] T is the identity
fibre-product identification, so the restriction formula in steps 1–2 of the
composition proof makes theta the identity under `lowerStarIdDerivedPlus`.
By def-weil-pbc-proper-open-comparison, alpha and the identity then have the
same transpose, namely the unit of j! ⊣ j⁻¹. The adjunction bijection in
lem-weil-pbc-extension-by-zero-adjunction proves the assertion. -/
theorem properOpenComparison_id (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T X : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenComparison Λ (𝟙 T) j j (Category.comp_id j) K ≫
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) T).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K) =
      𝟙 ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K) := by
  sorry

end AlgebraicGeometry.Etale
