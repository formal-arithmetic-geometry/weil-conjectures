/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Category.Grp.AB

/-! # Product-preserving functors on ringed sites and derived inverse limits

Source: Stacks Project, Injectives, Tag 08U1, lemma-RF-commutes-with-Rlim
(blueprint: lem-sfb-ringed-site-product-derived-limit).

The helper definitions instantiate the recorded right derived functor on the small
ringed site and transport its shift comparison along the unique unit-compatible
comparison with the existing monomorphic-resolution implementation.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w w' uA vA uB vB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The arbitrary-quasi-isomorphism resolution witness supplied by the existing
small-ringed-site resolution construction. No resolution hypothesis is imposed.
Source: Stacks Project, Injectives, Theorem 079P, used in Tag 08U1
(blueprint: lem-sfb-ringed-site-product-derived-limit). -/
noncomputable abbrev ringedSiteProductResolutionWitness
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max c v r}) :
    ∀ K : CochainComplex (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) ℤ,
      ∃ (I : CochainComplex (ringedSiteModules.{max c v r, max c v r, v, c}
        ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) ℤ)
        (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s :=
  letI := siteModuleKInjectiveResolutions.{c, v, r} J O
  fun K ↦ (Abelian.HasKInjectiveResolutions.exists_isKInjective K).elim
    (fun I hI ↦ hI.elim (fun hI hs ↦ hs.elim
      (fun s hs ↦ ⟨I, s, hI, hs.2⟩)))

namespace Functor

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
  (h : ∀ K : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

/-- The unique comparison preserving the derived units, used to transport the shift
structure, rather than choosing an arbitrary natural isomorphism.
Source: Stacks Project, Derived Categories, Tags 070K and 070Y; Injectives, Tag 08U1
(blueprint: lem-sfb-ringed-site-product-derived-limit). -/
noncomputable def quasiIsoResolutionProductRFComparison :
    F.rightDerivedFunctorOfQuasiIsoResolutions h ≅ F.rightDerivedFunctor :=
  letI := Functor.IsRightDerivedFunctor.isLeftKanExtension F.rightDerivedFunctor
    F.rightDerivedFunctorUnit (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  Classical.choose (F.rightDerivedFunctorOfQuasiIsoResolutions_unique h
    F.rightDerivedFunctor F.rightDerivedFunctorUnit
    (fun G ↦ (F.rightDerivedFunctor.homEquivOfIsLeftKanExtension
      F.rightDerivedFunctorUnit G).bijective))

/-- Canonical integer-shift comparison transported by the unique comparison of
right-derived pairs. The underlying functor remains the dependency's recorded functor.
Source: Stacks Project, Injectives, Tag 08U1, exactness of RF
(blueprint: lem-sfb-ringed-site-product-derived-limit). -/
@[instance_reducible]
noncomputable def quasiIsoResolutionProductRFCommShift :
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).CommShift ℤ :=
  Functor.CommShift.ofIso (F.quasiIsoResolutionProductRFComparison h).symm ℤ

end Functor

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  (O : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (ringedSiteModules.{max c v r, max c v r, v, c}
    ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))]
  [HasDerivedCategory.{w'} AddCommGrpCat.{max c v r}]
  (F : ringedSiteModules.{max c v r, max c v r, v, c}
    ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O) ⥤
      AddCommGrpCat.{max c v r}) [F.Additive]

/-- The recorded unbounded right derived functor, instantiated with the existing
small-site resolution witness. This is an abbreviation, not another construction.
Source: Stacks Project, Injectives, Tag 08U1
(blueprint: lem-sfb-ringed-site-product-derived-limit). -/
noncomputable abbrev ringedSiteProductRF :=
  F.rightDerivedFunctorOfQuasiIsoResolutions (ringedSiteProductResolutionWitness.{c, v, r} J O)

/-- Its canonical shift isomorphism at an arbitrary integer, with the resolution
instance supplied internally by the ringed-site theorem.
Source: Stacks Project, Injectives, Tag 08U1
(blueprint: lem-sfb-ringed-site-product-derived-limit). -/
noncomputable def ringedSiteProductRFShift (n : ℤ) :
    shiftFunctor _ n ⋙ ringedSiteProductRF.{c, v, r, w, w'} J O F ≅
      ringedSiteProductRF.{c, v, r, w, w'} J O F ⋙ shiftFunctor _ n :=
  letI := siteModuleKInjectiveResolutions.{c, v, r} J O
  (F.quasiIsoResolutionProductRFCommShift
    (ringedSiteProductResolutionWitness.{c, v, r} J O)).commShiftIso n

/-- An additive functor on module sheaves preserving countable products sends every
specified derived-limit triangle to a derived-limit triangle of the image tower,
with the canonical product projections and the canonical shifted connecting map.
Source: Stacks Project, Injectives, Tag 08U1, lemma-RF-commutes-with-Rlim
(blueprint: lem-sfb-ringed-site-product-derived-limit).

Proof:
1. Module-sheaf products are computed sectionwise: coordinatewise restrictions and
   scalar multiplication preserve the sheaf condition, by unique gluing in each factor
   (def-weil-sheaf-of-modules-category). The small-ringed-site resolution theorem
   prop-pur-kinjective-resolutions-exist supplies K-injective representatives I_n of K_n.
2. Their degreewise product I is K-injective and its localization is the product of
   their localizations, by lem-pc-ringed-space-product-kinjective. The product universal
   property gives the unique comparison with the specified product of the K_n.
3. Countable-product preservation identifies F(I) with the degreewise product of
   F(I_n); the differential equation follows after every projection by functoriality.
   Abelian groups have exact products (lem-pc-abelian-groups-exact-products), so
   lem-weil-derived-limit-products-core computes the target product by this complex.
   Transport its cone along the derived units, invertible on I and I_n, and along the
   representative isomorphisms. Naturality of def-sfb-right-derived-functor's unit
   identifies the transported legs with RF applied to the source projections.
4. The source and Ab have K-injective resolutions; for Ab one may use the singleton
   site with constant ring Z. Thus lem-pc-right-derived-functor-triangulated supplies
   exactness and the shift comparison. The unit-compatible uniqueness comparison
   transports this comparison to the recorded arbitrary-resolution derived functor.
5. Apply RF to the distinguished triangle and transport both product vertices along e
   (def-weil-triangulated-category). On projection n its middle arrow is
   pi_n - RF(f_n) pi_(n+1), so it is the target 1-s by uniqueness of maps into products.
   Its last arrow is e.inv followed by RF(delta) and the shift comparison. This is
   precisely def-weil-derived-limit. Composing the product equations with RF(p)
   gives the stated projections from RF(L). -/
theorem ringedSite_product_preserving_derivedLimit
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (K : ℕ → DerivedCategory (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)))
    [HasProduct K]
    (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
    (L : DerivedCategory (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)))
    (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle f L p δ) :
    ∃ (hP : HasProduct (fun n : ℕ ↦ (ringedSiteProductRF.{c, v, r, w, w'} J O F).obj (K n)))
      (e : (ringedSiteProductRF.{c, v, r, w, w'} J O F).obj (∏ᶜ K) ≅
        @piObj _ _ _ _ hP),
      (∀ n : ℕ, e.hom ≫ @Pi.π _ _ _ _ hP n =
        (ringedSiteProductRF.{c, v, r, w, w'} J O F).map (Pi.π K n)) ∧
      @IsDerivedLimitTriangle _ _ _ _ _ _ _ _ hP
        (fun n : ℕ ↦ (ringedSiteProductRF.{c, v, r, w, w'} J O F).map (f n))
        ((ringedSiteProductRF.{c, v, r, w, w'} J O F).obj L)
        ((ringedSiteProductRF.{c, v, r, w, w'} J O F).map p ≫ e.hom)
        (e.inv ≫ (ringedSiteProductRF.{c, v, r, w, w'} J O F).map δ ≫
          (ringedSiteProductRFShift.{c, v, r, w, w'} J O F (1 : ℤ)).hom.app L) ∧
      (∀ n : ℕ, (ringedSiteProductRF.{c, v, r, w, w'} J O F).map p ≫ e.hom ≫ @Pi.π _ _ _ _ hP n =
        (ringedSiteProductRF.{c, v, r, w, w'} J O F).map (p ≫ Pi.π K n)) := by
  sorry

end CategoryTheory
