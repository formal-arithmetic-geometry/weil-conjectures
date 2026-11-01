/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomIsomorphismEtale
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomSiteSquare
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteIsomorphismData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomNaturality
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteEvaluation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! Normalized internal-Hom stage comparison on the pro-etale site. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
  AlgebraicGeometry.ProEtale.pbcComparisonReduction
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.instMonoidalCategory_weilConjectures
  _root_.DerivedCategory.commShift₂CurriedTensor

private theorem boundedConstructible_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K : Cat A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun q hq ↦ hz q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun q hq ↦ hz q (.inr hq)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q (hq.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q hq

private theorem ctf_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K : Cat A X) :
    Ctf A X K ↔
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, _, ht⟩
    exact ⟨(boundedConstructible_iff_source A X K).1 hc, a, b,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht⟩
  · rintro ⟨hc, a, b, ht⟩
    exact ⟨(boundedConstructible_iff_source A X K).2 hc, min a b, b, min_le_right _ _,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
        (ht.mono (min_le_left _ _) le_rfl)⟩

private theorem ctf_origin
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Sites.D true A X) (hK : Sites.Ctf true A X K) :
    ∃ K' : Cat A X, Ctf A X K' ∧ Nonempty ((Sites.nu A X).obj K' ≅ K) := by
  obtain ⟨⟨K', hbc, ⟨e⟩⟩, a, b, ht⟩ := hK
  have ht' := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
    ((ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b).prop_of_iso
      e.symm ht)
  exact ⟨K', (ctf_iff_source A X K').2 ⟨hbc, a, b, ht'⟩, ⟨e⟩⟩

-- Generic in `pro`, so the kernel never unfolds the Bool-cased site functors (158 s before).
private theorem homMap_isIso_transport (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (μ : Sites.TensorComparison pro φ X) {K M K' M' : Sites.D pro A X}
    (f : K' ⟶ K) (g : M ⟶ M') [IsIso f] [IsIso g]
    [IsIso (Sites.homMap pro φ X μ K M)] :
    IsIso (Sites.homMap pro φ X μ K' M') := by
  have hn := scalar_tensor_hom_comparison_naturality
    (Sites.tensor pro A X) (Sites.hom pro A X)
    (Sites.tensor pro B X) (Sites.hom pro B X)
    (Sites.adj pro A X) (Sites.adj pro B X)
    (normalized_stage_site_evaluation_dinaturality pro A X)
    (normalized_stage_site_evaluation_dinaturality pro B X)
    (Sites.scalar pro φ X) μ K M K' M' f g
  change (Sites.scalar pro φ X).map
      ((Functor.uncurry.obj (Sites.hom pro A X)).map
        (Prod.mkHom f.op g)) ≫ Sites.homMap pro φ X μ K' M' =
      Sites.homMap pro φ X μ K M ≫
      (Functor.uncurry.obj (Sites.hom pro B X)).map
        (Prod.mkHom ((Sites.scalar pro φ X).map f).op
          ((Sites.scalar pro φ X).map g)) at hn
  have hpair : IsIso (Prod.mkHom f.op g) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have hpairS : IsIso (Prod.mkHom ((Sites.scalar pro φ X).map f).op
      ((Sites.scalar pro φ X).map g)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have htransport : IsIso ((Sites.scalar pro φ X).map
      ((Functor.uncurry.obj (Sites.hom pro A X)).map
        (Prod.mkHom f.op g)) ≫ Sites.homMap pro φ X μ K' M') := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((Sites.scalar pro φ X).map
      ((Functor.uncurry.obj (Sites.hom pro A X)).map (Prod.mkHom f.op g))) _

set_option maxHeartbeats 2000000 in
-- The site square and its cancellations elaborate the published derived tensor-Hom functors.
/-- Pro-etale finite-stage internal-Hom comparison on ctf objects.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
(blueprint: lem-sf-normalized-stage-hom-isomorphism-proetale).

Proof: Choose ordinary etale ctf origins for the two pro-etale inputs. The comparison reflects the
Tor intervals, so their origins satisfy the finite-Tor condition required by the ordinary theorem.

Apply the ordinary normalized stage Hom comparison to these origins. Scalar calculus preserves
their ctf domains under the coefficient arrow. The normalized derived site Hom comparison and
scalar/site comparisons on these objects are isomorphisms.

Untranspose the coefficient/site square. The tensor site square and scalar representative
normalization identify both sides with scalar extension of the ordinary evaluation counit, so
injectivity of the tensor-Hom adjunction proves the square. Mate pasting and the ordinary
isomorphism with the site isomorphisms imply that the pro-etale comparison on the origins is
invertible. Naturality transfers this conclusion along the origin isomorphisms to the stipulated
inputs. -/
theorem normalized_stage_hom_isomorphism_proetale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    {s t : Stage l E} (a : Arrow s t)
    (μ : Sites.TensorComparison true a.ringMap X)
    (hμ : Sites.NormalizedTensor true a.ringMap X μ)
    (K M : Sites.D true s.ring X)
    (hK : Sites.Ctf true s.ring X K) (hM : Sites.Ctf true s.ring X M) :
    IsIso (Sites.homMap true a.ringMap X μ K M) := by
  obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := ctf_origin s.ring X K hK
  obtain ⟨M₀, hM₀, ⟨eM⟩⟩ := ctf_origin s.ring X M hM
  let μet : Sites.TensorComparison false a.ringMap X :=
    Etale.ExceptionalCoefficients.tensorIso a.ringMap X
  have hμet : Sites.NormalizedTensor false a.ringMap X μet := HEq.rfl
  have hscalar := (finite_ring_scalar_direct_foundations D a.ringMap X X (𝟙 X)).1
  have hSK : Ctf t.ring X ((Sites.scalar false a.ringMap X).obj K₀) :=
    hscalar false K₀ hK₀
  have hSM : Ctf t.ring X ((Sites.scalar false a.ringMap X).obj M₀) :=
    hscalar false M₀ hM₀
  have hsiteS := normalized_stage_site_isomorphism_data D l hl E X s K₀ M₀ hK₀ hM₀
  have hsiteT := normalized_stage_site_isomorphism_data D l hl E X t _ _ hSK hSM
  have het := normalized_stage_hom_isomorphism_etale D l hl E X a μet hμet K₀ M₀ hK₀ hM₀
  obtain ⟨cK, dK, hcdK, htK⟩ := hK₀.2
  obtain ⟨cM, dM, hcdM, htM⟩ := hM₀.2
  let c := min cK cM
  let d := max dK dM
  have hcd : c ≤ d := (min_le_left _ _).trans (hcdK.trans (le_max_left _ _))
  have htK' : Etale.DerivedCategory.hasTorAmplitudeIn s.ring X c d K₀ :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      ((Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 htK).mono
        (min_le_left _ _) (le_max_left _ _))
  have htM' : Etale.DerivedCategory.hasTorAmplitudeIn s.ring X c d M₀ :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      ((Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 htM).mono
        (min_le_right _ _) (le_max_right _ _))
  have hsq := normalized_stage_hom_site_square D l hl E s t a X
    (X ↘ Spec (.of D.k)) μet hμet μ hμ K₀ M₀ hK₀.1 hM₀.1 c d hcd htK' htM'
  have hleft : IsIso ((Sites.scalar true a.ringMap X).map
      (Sites.siteHom s.ring X K₀ M₀)) := inferInstance
  have hright : IsIso (homAction (Sites.hom true t.ring X)
      ((Sites.scalarSite a.ringMap X).inv.app K₀)
      ((Sites.scalarSite a.ringMap X).hom.app M₀)) := by
    dsimp only [homAction]
    infer_instance
  have hwhole : IsIso ((Sites.scalar true a.ringMap X).map
      (Sites.siteHom s.ring X K₀ M₀) ≫
      Sites.homMap true a.ringMap X μ
        ((Sites.nu s.ring X).obj K₀) ((Sites.nu s.ring X).obj M₀) ≫
      homAction (Sites.hom true t.ring X)
        ((Sites.scalarSite a.ringMap X).inv.app K₀)
        ((Sites.scalarSite a.ringMap X).hom.app M₀)) := by
    rw [hsq]
    infer_instance
  have htail : IsIso (Sites.homMap true a.ringMap X μ
      ((Sites.nu s.ring X).obj K₀) ((Sites.nu s.ring X).obj M₀) ≫
      homAction (Sites.hom true t.ring X)
        ((Sites.scalarSite a.ringMap X).inv.app K₀)
        ((Sites.scalarSite a.ringMap X).hom.app M₀)) :=
    IsIso.of_isIso_comp_left
      ((Sites.scalar true a.ringMap X).map (Sites.siteHom s.ring X K₀ M₀)) _
  have horigin : IsIso (Sites.homMap true a.ringMap X μ
      ((Sites.nu s.ring X).obj K₀) ((Sites.nu s.ring X).obj M₀)) :=
    IsIso.of_isIso_comp_right _
      (homAction (Sites.hom true t.ring X)
        ((Sites.scalarSite a.ringMap X).inv.app K₀)
        ((Sites.scalarSite a.ringMap X).hom.app M₀))
  exact homMap_isIso_transport true a.ringMap X μ eK.inv eM.hom

end WeilConjectures.FiniteFreeCoefficients
