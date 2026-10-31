/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedProperScalarNormalization
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedOpenScalarNormalization

/-! # Fixed-module normalization of the recorded intrinsic coefficient arrow

Source: Stacks Project, Tags 00YV, 03D3 and 0GL6, and Step 3 of
lem-sp-transported-compact-scalar-site-square. This is a comparison of the two
pro-etale presentations only; no etale input or boundedness is involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] transportedRecordedReductionDirectImageComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  sfIntrinsicModuleEquivalence scalarPresentation directImagePresentation
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  directImageScalarComparison reductionOpenScalarIso OpenScalarSite.scalarOpen
  supportPresentation FiniteCompactScalar.openRealizationIso
attribute [local implicit_reducible] sfIntrinsicDerivedEquivalence
  Equivalence.mapDerivedCategory sfIntrinsicExtensionByZero
  proEtaleConstantRingMap scalarExtensionFunctor

private theorem supportPresentation_hom_app
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (supportPresentation A c).hom.app K =
      (directImageConstantPush A c.g).map
          ((FiniteCompactScalar.openRealizationIso A c.i).hom.app K) ≫
        (directImagePresentation A c.g).hom.app
          ((openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K) := by
  unfold supportPresentation FiniteCompactScalar.openRealizationIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  rfl

private theorem paste_scalar_factors
    {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (e₀ : A₀ ⥤ C₀) (e₁ : A₁ ⥤ C₁) (e₂ : A₂ ⥤ C₂)
    (f₀ : B₀ ⥤ D₀) (f₁ : B₁ ⥤ D₁) (f₂ : B₂ ⥤ D₂)
    (j : A₀ ⥤ A₁) (p : A₁ ⥤ A₂) (k : B₀ ⥤ B₁) (q : B₁ ⥤ B₂)
    (J : C₀ ⥤ C₁) (P : C₁ ⥤ C₂) (K : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂)
    (s₀ : A₀ ⥤ B₀) (s₁ : A₁ ⥤ B₁) (s₂ : A₂ ⥤ B₂)
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    (a : e₀ ⋙ J ≅ j ⋙ e₁) (b : e₁ ⋙ P ≅ p ⋙ e₂)
    (c : f₀ ⋙ K ≅ k ⋙ f₁) (d : f₁ ⋙ Q ≅ q ⋙ f₂)
    (r₀ : e₀ ⋙ S₀ ≅ s₀ ⋙ f₀) (r₁ : e₁ ⋙ S₁ ≅ s₁ ⋙ f₁)
    (r₂ : e₂ ⋙ S₂ ≅ s₂ ⋙ f₂)
    (α : J ⋙ S₁ ⟶ S₀ ⋙ K) (β : j ⋙ s₁ ⟶ s₀ ⋙ k)
    (γ : P ⋙ S₂ ⟶ S₁ ⋙ Q) (δ : p ⋙ s₂ ⟶ s₁ ⋙ q)
    (ho : ∀ M, α.app (e₀.obj M) ≫ K.map (r₀.hom.app M) ≫
      c.hom.app (s₀.obj M) =
      S₁.map (a.hom.app M) ≫ r₁.hom.app (j.obj M) ≫ f₁.map (β.app M))
    (hp : ∀ N, γ.app (e₁.obj N) ≫ Q.map (r₁.hom.app N) ≫
      d.hom.app (s₁.obj N) =
      S₂.map (b.hom.app N) ≫ r₂.hom.app (p.obj N) ≫ f₂.map (δ.app N))
    (M : A₀) :
    γ.app (J.obj (e₀.obj M)) ≫ Q.map (α.app (e₀.obj M)) ≫
        Q.map (K.map (r₀.hom.app M)) ≫ Q.map (c.hom.app (s₀.obj M)) ≫
        d.hom.app (k.obj (s₀.obj M)) =
      S₂.map (P.map (a.hom.app M)) ≫ S₂.map (b.hom.app (j.obj M)) ≫
        r₂.hom.app (p.obj (j.obj M)) ≫ f₂.map (δ.app (j.obj M)) ≫
        f₂.map (q.map (β.app M)) := by
  rw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc, ho]
  simp only [Functor.map_comp, Category.assoc]
  have hγ := γ.naturality (a.hom.app M)
  have hd := d.hom.naturality (β.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hγ hd
  rw [hd, ← reassoc_of% hγ, reassoc_of% hp]

set_option maxHeartbeats 600000 in
-- The pasted square elaborates several derived presentation and adjunction types.
/-- The recorded intrinsic proper/open scalar arrow, after the prescribed realization
transport, is the fixed-module proper scalar mate followed by the image of the open
scalar comparison. This identifies an arrow on the entire pro-etale derived category.

Source: Stacks Project, more-etale.tex, Tag 0GL6 (proper/open coefficient comparison),
and Step 3 of lem-sp-transported-compact-scalar-site-square; the normalization argument
through the specified realization is agent-written.
(blueprint: lem-sp-recorded-compact-scalar-fixed-normalization).

Proof: apply the fully faithful realization functor at Y. Its image of the left
side is the defining conjugate of reductionDirectImageComparison. Expand that arrow
as the proper scalar mate followed by proper image of reductionOpenScalarIso.
Expand supportPresentation as the exact open realization comparison followed by
right-adjoint uniqueness and the K-injective-normalized direct-image realization.
Naturality moves the open realization comparison through the proper scalar mate.
Transpose the resulting proper square under the B-geometric adjunction. The
unit-preserving pullback coordinate change in directImagePresentation identifies
its counit with the fixed-module geometric counit. The section-identity scalar
restriction comparison defining scalarPresentation preserves the scalar units, so
the scalar/pullback mates have the same transpose in these coordinates. This proves
the proper-factor equality. For the open factor use the two open adjunctions:
reductionOpenModel is their left-adjoint uniqueness comparison, and
reductionOpenScalarIso is conjugation of the composite-left-adjoint uniqueness map.
Transpose along the open adjunction and then the scalar adjunction. Both paths are
the same sectionwise restriction comparison, since the realization unit cancels in
the definition of supportPresentation. Injectivity of these Hom bijections proves
the open-factor equality. Paste the two equalities and cancel the realization
unit/counit pairs. Faithfulness descends equality of the fixed-module maps; naturality
and extensionality give the equality of natural transformations. These arguments use
only adjunction identities, so zero coefficient rings, empty schemes, identity maps,
and unbounded inputs require no exceptions. No coefficient mate is inverted. -/
theorem recordedCompactScalar_fixed_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    transportedRecordedReductionDirectImageComparison φ c
        (reductionDirectImageComparison φ c.i c.g) =
      whiskerLeft
          (openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory
          (mateEquiv
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g)
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.g)
            (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso (uliftRingHom φ) c.g).hom)).natTrans ≫
        whiskerRight (OpenScalarSite.scalarOpen (uliftRingHom φ) c.i).hom
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.g).rightDerivedFunctor := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} c.Z.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let EA (T : Scheme.{u}) := (sfIntrinsicDerivedEquivalence T A).functor
  let EB (T : Scheme.{u}) := (sfIntrinsicDerivedEquivalence T B).functor
  let JA := (openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory
  let JB := (openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.i).mapDerivedCategory
  let PA := (lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).rightDerivedFunctor
  let PB := (lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.g).rightDerivedFunctor
  let IA := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  let IB := (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
  let RA := directImageConstantPush A c.g
  let RB := directImageConstantPush B c.g
  let γ := (mateEquiv
    (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g)
    (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.g)
    (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso (uliftRingHom φ) c.g).hom)).natTrans
  let σ := (OpenScalarSite.scalarOpen (uliftRingHom φ) c.i).hom
  let fixedMap := whiskerLeft JA γ ≫ whiskerRight σ PB
  let W := (whiskeringRight
    (DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (proEtaleDerivedCategory Y B)).obj (EB Y)
  let FF : W.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful (EB Y)).whiskeringRight
    (DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
  apply FF.map_injective
  unfold transportedRecordedReductionDirectImageComparison
  change W.map (FF.preimage _) = W.map fixedMap
  rw [FF.map_preimage]
  ext M
  change (scalarPresentation φ Y).inv.app ((JA ⋙ PA).obj M) ≫
      (scalarExtensionFunctor φ Y).map ((supportPresentation A c).inv.app M) ≫
      (reductionDirectImageComparison φ c.i c.g).app ((EA X).obj M) ≫
      RB.map (IB.map ((scalarPresentation φ X).hom.app M)) ≫
      (supportPresentation B c).hom.app ((liftedScalarExtension φ X).obj M) =
    (EB Y).map (fixedMap.app M)
  apply (cancel_epi
    ((scalarExtensionFunctor φ Y).map ((supportPresentation A c).hom.app M) ≫
      (scalarPresentation φ Y).hom.app ((JA ⋙ PA).obj M))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [(scalarExtensionFunctor φ Y).map_id, Category.id_comp]
  have h := paste_scalar_factors
    (EA X) (EA c.Z) (EA Y) (EB X) (EB c.Z) (EB Y)
    JA PA JB PB IA RA IB RB
    (liftedScalarExtension φ X) (liftedScalarExtension φ c.Z) (liftedScalarExtension φ Y)
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor φ c.Z) (scalarExtensionFunctor φ Y)
    (FiniteCompactScalar.openRealizationIso A c.i) (directImagePresentation A c.g)
    (FiniteCompactScalar.openRealizationIso B c.i) (directImagePresentation B c.g)
    (scalarPresentation φ X) (scalarPresentation φ c.Z) (scalarPresentation φ Y)
    (reductionOpenScalarIso φ c.i).hom σ (directImageScalarComparison φ c.g) γ
    (recordedOpenScalar_fixed_normalization φ c.i)
    (recordedProperScalar_fixed_normalization φ c.g) M
  rw [supportPresentation_hom_app, supportPresentation_hom_app]
  simpa only [reductionDirectImageComparison, fixedMap, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.map_comp, Category.assoc,
    IA, IB, RA, RB, JA, JB, PA, PB, EA, EB, Functor.comp_obj] using h

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
