/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement

/-! # Localization transports a coefficient isomorphism

Source: Stacks Project, Tags 0996 and 099E, and the localization universal property.
(blueprint: lem-zl-ringed-localization-iso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe r c h
open CategoryTheory Opposite
namespace CategoryTheory

/-- A ring-sheaf isomorphism preserving the chosen section induces a normalized
isomorphism of the sheafified localizations.
Source: Stacks Project, Tags 0996 and 099E.
(blueprint: lem-zl-ringed-localization-iso)

Proof. On each object use the ring equivalence of localizations induced by the
coefficient isomorphism. The powers submonoids correspond because the sections
correspond. Naturality follows from uniqueness of a ring map from a localization:
both composites agree on integral numerators. Sheafify this natural isomorphism.
The same numerator computation, followed by naturality of sheafification's unit,
gives the asserted equation of coefficient maps. The proof also applies to zero
rings and empty objects. -/
theorem ringedLocalization_iso
    {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    [HasSheafify J Ab.{r}] [J.WEqualsLocallyBijective Ab.{r}]
    [HasSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S : Sheaf J CommRingCat.{r}} (e : R ≅ S)
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (t : (S.obj ⋙ forget CommRingCat).sections)
    (hst : ∀ U, e.hom.hom.app U (s.val U) = t.val U) :
    ∃ q : ringedLocalizationRingOfUniverses R s ≅ ringedLocalizationRingOfUniverses S t,
      ringedLocalizationRingUnitOfUniverses R s ≫ q.hom =
        e.hom ≫ ringedLocalizationRingUnitOfUniverses S t := by
  let a (U : Cᵒᵖ) : R.obj.obj U ≃+* S.obj.obj U :=
    Iso.commRingCatIsoToRingEquiv ((sheafToPresheaf J CommRingCat).mapIso e |>.app U)
  have ha (U : Cᵒᵖ) : (Submonoid.powers (s.val U)).map (a U).toMonoidHom =
      Submonoid.powers (t.val U) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (hst U)
  let b (U : Cᵒᵖ) := IsLocalization.ringEquivOfRingEquiv
    (ringedSectionLocalizationCarrierOfUniverses R s U)
    (ringedSectionLocalizationCarrierOfUniverses S t U) (a U) (ha U)
  let ep : ringedLocalizationRingPresheafOfUniverses R s ≅
      ringedLocalizationRingPresheafOfUniverses S t :=
    NatIso.ofComponents (fun U ↦ (b U).toCommRingCatIso) (by
      intro U V f
      apply CommRingCat.hom_ext
      change (b V).toRingHom.comp (ringedSectionLocalizationMapOfUniverses R s f) =
        (ringedSectionLocalizationMapOfUniverses S t f).comp (b U).toRingHom
      apply IsLocalization.ringHom_ext (R := R.obj.obj U)
        (Submonoid.powers (s.val U))
      ext x
      simp only [RingHom.comp_apply]
      change b V (ringedSectionLocalizationMapOfUniverses R s f
          (algebraMap (R.obj.obj U) _ x)) =
        ringedSectionLocalizationMapOfUniverses S t f
          (b U (algebraMap (R.obj.obj U) _ x))
      simp only [ringedSectionLocalizationMapOfUniverses, IsLocalization.Away.lift_eq,
        RingHom.comp_apply, b, IsLocalization.ringEquivOfRingEquiv_eq]
      exact congrArg (algebraMap _ _) (ConcreteCategory.congr_hom
        (e.hom.hom.naturality f) x))
  let q := (presheafToSheaf J CommRingCat).mapIso ep
  refine ⟨q, ?_⟩
  apply Sheaf.hom_ext
  change (ringedLocalizationRingPresheafUnitOfUniverses R s ≫
    toSheafify J _) ≫ ((presheafToSheaf J CommRingCat).map ep.hom).hom = _
  rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc]
  have hw : ringedLocalizationRingPresheafUnitOfUniverses R s ≫ ep.hom =
      e.hom.hom ≫ ringedLocalizationRingPresheafUnitOfUniverses S t := by
    ext U x
    change b U (algebraMap (R.obj.obj U) _ x) =
      algebraMap (S.obj.obj U) _ (e.hom.hom.app U x)
    exact IsLocalization.ringEquivOfRingEquiv_eq
      (R := R.obj.obj U) (P := S.obj.obj U) (ha U) x
  rw [hw]
  rfl

end CategoryTheory
