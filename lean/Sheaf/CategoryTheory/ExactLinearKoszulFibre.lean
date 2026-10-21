/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.SignedKoszulCompletionModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Exact linear functors and the signed Koszul completion fibre

Source: Stacks Project, algebraization.tex, Tag 0A0E, and the final paragraph of the
blueprint proof lem-cbc-completed-extension-zero-comparison, refined by the explicit
signed calculation of the DAG (blueprint: lem-cbc-exact-linear-koszul-fiber).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v uH vH z wR wS

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The canonical signed Koszul comparison, together with its localization and unit equations.
All maps are specified by their finite, countable, and binary projections. This structure
packages the conclusions; it adds no hypothesis or choice of an unspecified cone map.
Source: Stacks Tag 0A0E and the signed-model refinement in the blueprint proof of
lem-cbc-completed-extension-zero-comparison (blueprint: lem-cbc-exact-linear-koszul-fiber). -/
structure SignedKoszulFibreComparison
    {ER : Type u} [Category.{uH} ER] [Abelian ER]
    [HasFiniteBiproducts ER] [HasBinaryBiproducts ER]
    {ES : Type v} [Category.{vH} ES] [Abelian ES]
    [HasFiniteBiproducts ES] [HasBinaryBiproducts ES]
    [HasDerivedCategory.{wR} ER] [HasDerivedCategory.{wS} ES]
    {A : Type z} [CommRing A]
    {σR : ∀ {X Y : ER}, A → (X ⟶ Y) → (X ⟶ Y)}
    {σS : ∀ {X Y : ES}, A → (X ⟶ Y) → (X ⟶ Y)}
    {r : ℕ} {a : Fin r → A}
    {TR : ℕ → CochainComplex ER ℤ ⥤ CochainComplex ER ℤ}
    {TS : ℕ → CochainComplex ES ℤ ⥤ CochainComplex ES ℤ}
    (F : ER ⥤ ES) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (MR : SignedKoszulCompletionModel A ER σR a TR)
    (MS : SignedKoszulCompletionModel A ES σS a TS) where
  /-- The finite-coordinate comparison. -/
  alpha : ∀ m : ℕ,
      TR m ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ TS m
  /-- The countable-product comparison. -/
  beta : MR.product ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ MS.product
  /-- The signed-fibre comparison. -/
  h : MR.fibre ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ MS.fibre
  /-- The induced source completion functor. -/
  HR : DerivedCategory ER ⥤ DerivedCategory ER
  /-- The induced target completion functor. -/
  HS : DerivedCategory ES ⥤ DerivedCategory ES
  /-- Its source localization factorization. -/
  eR : DerivedCategory.Q ⋙ HR ≅ MR.fibre ⋙ DerivedCategory.Q
  /-- Its target localization factorization. -/
  eS : DerivedCategory.Q ⋙ HS ≅ MS.fibre ⋙ DerivedCategory.Q
  /-- The localized source unit. -/
  etaR : 𝟭 (DerivedCategory ER) ⟶ HR
  /-- The localized target unit. -/
  etaS : 𝟭 (DerivedCategory ES) ⟶ HS
  /-- The descended comparison. -/
  hd : HR ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ HS
  /-- Every finite projection is the image of the specified tensor projection. -/
  alpha_coordinates : ∀ (m : ℕ) (K : CochainComplex ER ℤ) (q : ℤ) (I : Finset (Fin r)),
    ((alpha m).hom.app K).f q ≫
        (MS.coordinates m ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biproduct.π _ I =
      F.map ((MR.coordinates m K q).hom ≫ biproduct.π _ I)
  /-- Every tower projection is the image projection followed by alpha. -/
  beta_projection : ∀ (m : ℕ) (K : CochainComplex ER ℤ),
    beta.hom.app K ≫ (MS.projection m).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F.mapHomologicalComplex (.up ℤ)).map ((MR.projection m).app K) ≫
        (alpha m).hom.app K
  /-- The first fibre projection is beta after the canonical binary comparison. -/
  h_fst : ∀ (K : CochainComplex ER ℤ) (q : ℤ),
    (h.hom.app K).f q ≫
        (MS.fibreCoordinates ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biprod.fst =
      F.map ((MR.fibreCoordinates K q).hom ≫ biprod.fst) ≫
        (beta.hom.app K).f q
  /-- The second fibre projection is beta in degree q-1. -/
  h_snd : ∀ (K : CochainComplex ER ℤ) (q : ℤ),
    (h.hom.app K).f q ≫
        (MS.fibreCoordinates ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biprod.snd =
      F.map ((MR.fibreCoordinates K q).hom ≫ biprod.snd) ≫
        (beta.hom.app K).f (q - 1)
  /-- The strict chain comparison carries the specified unit to the specified unit. -/
  unit_compatibility : ∀ K : CochainComplex ER ℤ,
    (F.mapHomologicalComplex (.up ℤ)).map (MR.unit.app K) ≫ h.hom.app K =
      MS.unit.app ((F.mapHomologicalComplex (.up ℤ)).obj K)
  /-- The source derived unit is the localization of the chain unit. -/
  etaR_factor : ∀ K : CochainComplex ER ℤ,
    etaR.app (DerivedCategory.Q.obj K) ≫ eR.hom.app K =
      DerivedCategory.Q.map (MR.unit.app K)
  /-- The target derived unit is the localization of the chain unit. -/
  etaS_factor : ∀ K : CochainComplex ES ℤ,
    etaS.app (DerivedCategory.Q.obj K) ≫ eS.hom.app K =
      DerivedCategory.Q.map (MS.unit.app K)
  /-- The derived comparison is the localization of the chain comparison. -/
  derived_factor : ∀ K : CochainComplex ER ℤ,
    F.mapDerivedCategory.map (eR.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app (MR.fibre.obj K) ≫
          DerivedCategory.Q.map (h.hom.app K) =
      hd.hom.app (DerivedCategory.Q.obj K) ≫
        HS.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          eS.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)
  /-- The descended comparison carries the source unit to the target unit. -/
  derived_unit : ∀ X : DerivedCategory ER,
    F.mapDerivedCategory.map (etaR.app X) ≫ hd.hom.app X =
      etaS.app (F.mapDerivedCategory.obj X)
  /-- Invertibility of the source derived unit implies that of the target unit. -/
  preserves_unit_isIso : ∀ X : DerivedCategory ER,
    IsIso (etaR.app X) → IsIso (etaS.app (F.mapDerivedCategory.obj X))

/-- The preceding comparison specialized to the actual sheaf Koszul tensors and their
pure-tensor-normalized coordinates; all conclusion fields are inherited transparently.
Source: Stacks Tag 0A0E (blueprint: lem-cbc-exact-linear-koszul-fiber). -/
abbrev ExactLinearSignedKoszulFibreComparison
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    {J : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf L CommRingCat.{v})
    {A : Type z} [CommRing A]
    (ρR : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (ρS : A →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{wR} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{v} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {r : ℕ} {a : Fin r → A}
    (MR : RingedSignedKoszulCompletionModel R ρR a)
    (MS : RingedSignedKoszulCompletionModel S ρS a) :=
  letI := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  letI := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{v}
    ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
  SignedKoszulFibreComparison F MR.model MS.model

/-- Exact A-linear functors preserving the canonical countable products commute with the
explicit signed Koszul fibre and its coaugmentation, on complexes and after localization.
The finite-coordinate, product-projection and two fibre-projection equations specify the
canonical comparison. Both model types are inhabited, and the comparison applies to every
model with these specified coordinates. Exponent m+1 indexes exactly all positive exponents.

Source: Stacks Tag 0A0E and the agent-written refinement of the blueprint proof
lem-cbc-completed-extension-zero-comparison (blueprint: lem-cbc-exact-linear-koszul-fiber).

Proof plan:
1. Expand the ordered total tensor into summands K^(q+|I|). The pure-tensor unitors give
   the normalization in the model. The differential has entries d_K and
   (-1)^(q+|I|) (-1)^(number of earlier indices) a_i^(m+1). The transition on I is
   multiplication by the product of its scalars. This also constructs both models.
2. Additivity preserves finite biproduct inclusions and projections, because their matrix
   composites and the sum of inclusion-projection composites are preserved. A-linearity
   preserves each scalar differential and transition entry. This gives alpha, natural in K,
   compatible with transitions and with the empty-coordinate inclusions.
3. Compose the assumed canonical countable-product comparison with the product of alpha.
   Projection to m gives the equation for beta below; projection also proves its chain
   equation, naturality, and compatibility with the shift and the diagonal unit.
4. The binary-biproduct comparison followed by beta in degrees q and q-1 gives h. Its
   block differential is (d,0;1-s,-d), so it is a chain isomorphism. Its unit equality follows
   in the first coordinate from the empty-subset inclusions, and in the second from F(0)=0.
5. By lem-sbc-koszul-fibre-linear-descent, exact countable products and the bounded finite
   free Koszul factors imply that both signed models preserve quasi-isomorphisms on all
   unbounded complexes. Exact F descends termwise by
   lem-sf-exact-functor-derived-triangulated, using F.mapDerivedCategory.
6. Localize h and the unit equality by lem-weil-pbc-localization-universal-property.
   The displayed factorization equation identifies the derived comparison with the same
   chain comparison. The inverse of the final unit is the inverse comparison followed by the
   image of the
   inverse source unit. For r=0 there is just the empty coordinate,
   all transitions are identities, and the same product-diagonal argument applies. No
   scalar is inverted, so zero scalars, units, zero objects and the empty site are allowed. -/
theorem exists_exactLinear_signedKoszulFibre
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    {J : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf L CommRingCat.{v})
    {A : Type z} [CommRing A]
    (ρR : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (ρS : A →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{wR} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    [HasCountableProducts (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasCountableProducts (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    [CountableAB4Star (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [CountableAB4Star (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{v} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hlinear : ∀ {M N : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (b : A) (f : M ⟶ N),
      F.map (ringedKoszulCoefficientSMul R ρR b f) =
        ringedKoszulCoefficientSMul S ρS b (F.map f))
    (hproduct : ∀ M : ℕ → ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      IsIso (piComparison F M))
    (r : ℕ) (a : Fin r → A) :
    Nonempty (RingedSignedKoszulCompletionModel R ρR a) ∧
    Nonempty (RingedSignedKoszulCompletionModel S ρS a) ∧
    ∀ (MR : RingedSignedKoszulCompletionModel R ρR a)
      (MS : RingedSignedKoszulCompletionModel S ρS a),
    Nonempty (ExactLinearSignedKoszulFibreComparison R S ρR ρS F MR MS) := by
  sorry

end CategoryTheory
