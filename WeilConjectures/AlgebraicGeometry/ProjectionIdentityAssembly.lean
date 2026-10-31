/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ConstructibleProjectionMates
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionCoherenceLaws
import WeilConjectures.AlgebraicGeometry.ProjectionIdentityPullbackUnits
import WeilConjectures.AlgebraicGeometry.ProjectionIdentityProperCounit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Assembly of the normalized identity projection

Source: current blueprint prop-sf-pf-coherence, identity and proper-case clauses.
The four proved stage lemmas share the categorical normalization and cancellation
calculations, and use only the underlying operation datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private theorem finiteIdentity_fullyFaithful (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) :
    (S.finite.pull (𝟙 X)).Full ∧ (S.finite.pull (𝟙 X)).Faithful := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
  let e₀ := Functor.mapDerivedCategoryNatIso (sfIntrinsicPullbackId A X.obj.left) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let e : S.finite.pull (𝟙 X) ≅ 𝟭 _ := Functor.fullyFaithfulCancelRight I
    (S.finitePullback (𝟙 X) ≪≫ Functor.isoWhiskerLeft I e₀ ≪≫
      Functor.rightUnitor I ≪≫ (Functor.leftUnitor I).symm)
  exact ⟨Functor.Full.of_iso e.symm, Functor.Faithful.of_iso e.symm⟩

private theorem identityUnit_unique {A : Type*} [Category A]
    (F : A ⥤ A) {H : A ⥤ A} (c : H ≅ F ⋙ F)
    (t : ∀ M : A, H.obj M ⟶ F.obj M)
    (e e' : F ≅ 𝟭 A)
    (h : ∀ M, c.hom.app M ≫ e.hom.app (F.obj M) = t M)
    (h' : ∀ M, c.hom.app M ≫ e'.hom.app (F.obj M) = t M) : e' = e := by
  have he (M : A) : e'.hom.app (F.obj M) = e.hom.app (F.obj M) :=
    (cancel_epi (c.hom.app M)).1 ((h' M).trans (h M).symm)
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hn := e'.hom.naturality (e.hom.app M)
  have hm := e.hom.naturality (e.hom.app M)
  simp only [Functor.id_map, Functor.id_obj] at hn hm
  rw [he] at hn
  exact (cancel_epi (F.map (e.hom.app M))).1 (hn.trans hm.symm)

private theorem normalizedIdentityUnit {A : Type*} [Category A]
    (F : A ⥤ A) [F.Full] [F.Faithful] (c : F ≅ F ⋙ F) :
    ∃ e : F ≅ 𝟭 A, ∀ M, c.hom.app M ≫ e.hom.app (F.obj M) = 𝟙 (F.obj M) := by
  let e := Functor.fullyFaithfulCancelRight F
    (c.symm ≪≫ (Functor.leftUnitor F).symm)
  have hm (M : A) : F.map (e.hom.app M) = c.inv.app M := by
    simp only [e, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Category.comp_id]
  have hn (M : A) : e.hom.app (F.obj M) = F.map (e.hom.app M) := by
    apply (cancel_mono (e.hom.app M)).1
    simpa only [Functor.id_map, Functor.id_obj] using
      (e.hom.naturality (e.hom.app M)).symm
  refine ⟨e, fun M ↦ ?_⟩
  rw [hn, hm]
  exact c.hom_inv_id_app M

private theorem normalizedIdentityUnitTransport {A : Type*} [Category A]
    (F : A ⥤ A) [F.Full] [F.Faithful] {H : A ⥤ A}
    (c : H ≅ F ⋙ F) (t : H ≅ F) :
    ∃ e : F ≅ 𝟭 A, ∀ M, c.hom.app M ≫ e.hom.app (F.obj M) = t.hom.app M := by
  obtain ⟨e, he⟩ := normalizedIdentityUnit F (t.symm ≪≫ c)
  refine ⟨e, fun M ↦ ?_⟩
  apply (cancel_epi (t.inv.app M)).1
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app] using he M

private theorem normalizedIdentityUnitProperty {A : Type*} [Category A]
    (F : A ⥤ A) [F.Full] [F.Faithful] {H : A ⥤ A}
    (c : H ≅ F ⋙ F) (h : H = F) (P : (F ≅ 𝟭 A) → Prop)
    (hP : ∀ e, (∀ M, c.hom.app M ≫ e.hom.app (F.obj M) =
      eqToHom (congrArg (fun G : A ⥤ A ↦ G.obj M) h)) → P e) :
    ∃! e : F ≅ 𝟭 A,
      (∀ M, c.hom.app M ≫ e.hom.app (F.obj M) =
        eqToHom (congrArg (fun G : A ⥤ A ↦ G.obj M) h)) ∧ P e := by
  obtain ⟨e, he⟩ := normalizedIdentityUnitTransport F c (eqToIso h)
  simp only [eqToIso.hom, eqToHom_app] at he
  refine ⟨e, ⟨he, hP e he⟩, ?_⟩
  intro e' he'
  exact identityUnit_unique F c _ e e' he he'.1

private theorem identityProjection_of_proper
    {A B : Type*} [Category A] [Category B] (T : A ⥤ B ⥤ A)
    (F G : A ⥤ A) (e : F ≅ G) (d : G ≅ 𝟭 A)
    (K : A) (L P : B) (t : P ⟶ L)
    (p : (T.obj (F.obj K)).obj L ⟶ F.obj ((T.obj K).obj P))
    (q : (T.obj (G.obj K)).obj L ⟶ G.obj ((T.obj K).obj P))
    (h : (T.map (e.hom.app K)).app L ≫ q = p ≫ e.hom.app ((T.obj K).obj P))
    (hq : q ≫ d.hom.app ((T.obj K).obj P) ≫ (T.obj K).map t =
      (T.map (d.hom.app K)).app L) :
    p ≫ (e ≪≫ d).hom.app ((T.obj K).obj P) ≫ (T.obj K).map t =
      (T.map ((e ≪≫ d).hom.app K)).app L := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h, hq]

/-- Normalized identity projection at the finite coefficient stage.
Source: current blueprint prop-sf-pf-coherence, identity and proper-case clauses
(blueprint: lem-sf-projection-identity-assembly).
Proof: construct the normalized unit by full-faithful cancellation. Its naturality
and the inverse compositor give its normalization, and cancellation gives uniqueness.
Apply the proper counit identity and transport it along the proper identification
using the existing proper-coincidence law and tensor functoriality. -/
theorem projectionIdentity_finite (S : SixFunctorOperationDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      ∃! e : S.finite.pull (𝟙 X) ≅ 𝟭 (sixFunctorFiniteCategory D C E n hn X),
        (∀ M : sixFunctorFiniteCategory D C E n hn X,
          (S.finite.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
              e.hom.app ((S.finite.pull (𝟙 X)).obj M) =
            eqToHom (congrArg (fun f ↦ (S.finite.pull f).obj M)
              (Category.id_comp (𝟙 X)))) ∧
        ∀ (c : Compactification (𝟙 X : X ⟶ X).hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
          (L : finiteTorConstructibleCategory C.l E n hn X.obj.left),
          CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations (𝟙 X) c K L ≫
            ((S.finite.properIdentification (𝟙 X) c ≪≫
              ((S.finite.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
                Adjunction.id)).hom.app
              (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations
          X).obj K).obj ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations
          (𝟙 X)).obj L)) ≫
            ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
          K).map ((ObjectProperty.isoMk
              (finiteTorConstructible C.l E n hn X.obj.left)
              (X := (CompactSupportFiniteProjection.torPull
                S.toSixFunctorFiniteOperations (𝟙 X)).obj L) (Y := L)
              ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
                (e.app ⟨L.obj, L.property.1⟩)))).hom =
          ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).map
            (((S.finite.properIdentification (𝟙 X) c ≪≫
              ((S.finite.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
                Adjunction.id)).hom.app K)).app L) := by
  have pf := (projectionIdentity_properCounit S).1
  have laws := compactSupportProjection_coherenceLaws S
  intro X
  let : IsProper (𝟙 X : X ⟶ X).hom.left := by
    change IsProper (𝟙 X.obj.left)
    infer_instance
  let := (finiteIdentity_fullyFaithful S X).1
  let := (finiteIdentity_fullyFaithful S X).2
  refine normalizedIdentityUnitProperty (S.finite.pull (𝟙 X))
    (S.finite.pullComposition (𝟙 X) (𝟙 X))
    (congrArg (fun f ↦ S.finite.pull f) (Category.id_comp (𝟙 X))) _ ?_
  intro e he c K L
  exact identityProjection_of_proper
    (CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X)
    (S.finite.support (𝟙 X) c) (S.finite.direct (𝟙 X))
    (S.finite.properIdentification (𝟙 X) c)
    (((S.finite.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq Adjunction.id)
    K L ((CompactSupportFiniteProjection.torPull
      S.toSixFunctorFiniteOperations (𝟙 X)).obj L)
    ((ObjectProperty.isoMk
            (finiteTorConstructible C.l E n hn X.obj.left)
            (X := (CompactSupportFiniteProjection.torPull
              S.toSixFunctorFiniteOperations (𝟙 X)).obj L) (Y := L)
            ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
              (e.app ⟨L.obj, L.property.1⟩)))).hom
    (CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations (𝟙 X) c K L)
    (CompactSupportFiniteProjection.properComponent S.toSixFunctorFiniteOperations (𝟙 X) K L)
    (laws.1.proper (𝟙 X) c K L) (pf X e he K L)

/-- Normalized identity projection at the integral coefficient stage.
Source: current blueprint prop-sf-pf-coherence, identity and proper-case clauses
(blueprint: lem-sf-projection-identity-assembly).
Proof: construct the normalized unit by full-faithful cancellation. Its naturality
and the inverse compositor give its normalization, and cancellation gives uniqueness.
Apply the proper counit identity and transport it along the proper identification
using the existing proper-coincidence law and tensor functoriality. -/
theorem projectionIdentity_integral (S : SixFunctorOperationDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      ∃! e : S.higher.integral.pull (𝟙 X) ≅ 𝟭 (sfIntegralConstructibleCategory C.l E X.obj.left),
        (∀ M : sfIntegralConstructibleCategory C.l E X.obj.left,
          (S.higher.integral.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
              e.hom.app ((S.higher.integral.pull (𝟙 X)).obj M) =
            eqToHom (congrArg (fun f ↦ (S.higher.integral.pull f).obj M)
              (Category.id_comp (𝟙 X)))) ∧
        ∀ (c : Compactification (𝟙 X : X ⟶ X).hom.left) (K : sfIntegralConstructibleCategory C.l E
          X.obj.left)
          (L : sfIntegralConstructibleCategory C.l E X.obj.left),
          S.integralFiniteTorDomain X L →
          compactSupportProjectionComponent S.higher.integralExchange (𝟙 X) c K L ≫
            ((S.higher.integral.properIdentification (𝟙 X) c ≪≫
              ((S.higher.integral.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
                Adjunction.id)).hom.app
              (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull (𝟙 X)).obj L)) ≫
            ((S.higher.integralTensor X).obj K).map (e.app L).hom =
          ((S.higher.integralTensor X).map
            (((S.higher.integral.properIdentification (𝟙 X) c ≪≫
              ((S.higher.integral.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
                Adjunction.id)).hom.app K)).app L) := by
  have ui := (projectionIdentity_pullbackUnits S).1
  have pi := (projectionIdentity_properCounit S).2.1
  have laws := compactSupportProjection_coherenceLaws S
  intro X
  let : IsProper (𝟙 X : X ⟶ X).hom.left := by
    change IsProper (𝟙 X.obj.left)
    infer_instance
  let := (ui X).1
  let := (ui X).2
  refine normalizedIdentityUnitProperty (S.higher.integral.pull (𝟙 X))
    (S.higher.integral.pullComposition (𝟙 X) (𝟙 X))
    (congrArg (fun f ↦ S.higher.integral.pull f) (Category.id_comp (𝟙 X))) _ ?_
  intro e he c K L hL
  exact identityProjection_of_proper (S.higher.integralTensor X)
    (S.higher.integral.support (𝟙 X) c) (S.higher.integral.direct (𝟙 X))
    (S.higher.integral.properIdentification (𝟙 X) c)
    (((S.higher.integral.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
      Adjunction.id)
    K L ((S.higher.integral.pull (𝟙 X)).obj L) (e.app L).hom
    (compactSupportProjectionComponent S.higher.integralExchange (𝟙 X) c K L)
    (compactSupportProperProjection S.higher.integralExchange (𝟙 X) K L)
    (laws.2.1.proper (𝟙 X) c K L hL) (pi X e he K L hL)

/-- Normalized identity projection at the rational coefficient stage.
Source: current blueprint prop-sf-pf-coherence, identity and proper-case clauses
(blueprint: lem-sf-projection-identity-assembly).
Proof: construct the normalized unit by full-faithful cancellation. Its naturality
and the inverse compositor give its normalization, and cancellation gives uniqueness.
Apply the proper counit identity and transport it along the proper identification
using the existing proper-coincidence law and tensor functoriality. -/
theorem projectionIdentity_rational (S : SixFunctorOperationDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      ∃! e : S.higher.rational.pull (𝟙 X) ≅ 𝟭 (sfRationalConstructibleCategory C.l E X.obj.left),
        (∀ M : sfRationalConstructibleCategory C.l E X.obj.left,
          (S.higher.rational.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
              e.hom.app ((S.higher.rational.pull (𝟙 X)).obj M) =
            eqToHom (congrArg (fun f ↦ (S.higher.rational.pull f).obj M)
              (Category.id_comp (𝟙 X)))) ∧
        ∀ (c : Compactification (𝟙 X : X ⟶ X).hom.left) (K : sfRationalConstructibleCategory C.l E
          X.obj.left)
          (L : sfRationalConstructibleCategory C.l E X.obj.left),
          compactSupportProjectionComponent S.higher.rationalExchange (𝟙 X) c K L ≫
            ((S.higher.rational.properIdentification (𝟙 X) c ≪≫
              ((S.higher.rational.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
                Adjunction.id)).hom.app
              (((S.higher.rationalTensor X).obj K).obj ((S.higher.rational.pull (𝟙 X)).obj L)) ≫
            ((S.higher.rationalTensor X).obj K).map (e.app L).hom =
          ((S.higher.rationalTensor X).map
            (((S.higher.rational.properIdentification (𝟙 X) c ≪≫
              ((S.higher.rational.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
                Adjunction.id)).hom.app K)).app L) := by
  have ur := (projectionIdentity_pullbackUnits S).2.1
  have pr := (projectionIdentity_properCounit S).2.2.1
  have laws := compactSupportProjection_coherenceLaws S
  intro X
  let : IsProper (𝟙 X : X ⟶ X).hom.left := by
    change IsProper (𝟙 X.obj.left)
    infer_instance
  let := (ur X).1
  let := (ur X).2
  refine normalizedIdentityUnitProperty (S.higher.rational.pull (𝟙 X))
    (S.higher.rational.pullComposition (𝟙 X) (𝟙 X))
    (congrArg (fun f ↦ S.higher.rational.pull f) (Category.id_comp (𝟙 X))) _ ?_
  intro e he c K L
  exact identityProjection_of_proper (S.higher.rationalTensor X)
    (S.higher.rational.support (𝟙 X) c) (S.higher.rational.direct (𝟙 X))
    (S.higher.rational.properIdentification (𝟙 X) c)
    (((S.higher.rational.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
      Adjunction.id)
    K L ((S.higher.rational.pull (𝟙 X)).obj L) (e.app L).hom
    (compactSupportProjectionComponent S.higher.rationalExchange (𝟙 X) c K L)
    (compactSupportProperProjection S.higher.rationalExchange (𝟙 X) K L)
    (laws.2.2.1.proper (𝟙 X) c K L trivial) (pr X e he K L)

/-- Normalized identity projection at the common coefficient stage.
Source: current blueprint prop-sf-pf-coherence, identity and proper-case clauses
(blueprint: lem-sf-projection-identity-assembly).
Proof: construct the normalized unit by full-faithful cancellation. Its naturality
and the inverse compositor give its normalization, and cancellation gives uniqueness.
Apply the proper counit identity and transport it along the proper identification
using the existing proper-coincidence law and tensor functoriality. -/
theorem projectionIdentity_common (S : SixFunctorOperationDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      ∃! e : S.closure.commonStage.pull (𝟙 X) ≅ 𝟭
          (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left),
        (∀ M : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left,
          (S.closure.commonStage.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
              e.hom.app ((S.closure.commonStage.pull (𝟙 X)).obj M) =
            eqToHom (congrArg (fun f ↦ (S.closure.commonStage.pull f).obj M)
              (Category.id_comp (𝟙 X)))) ∧
        ∀ (c : Compactification (𝟙 X : X ⟶ X).hom.left) (K :
          generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
          (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left),
          compactSupportProjectionComponent S.closure.commonStageExchange (𝟙 X) c K L ≫
            ((S.closure.commonStage.properIdentification (𝟙 X) c ≪≫
              ((S.closure.commonStage.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
                Adjunction.id)).hom.app
              (((S.closure.commonStageTensor X).obj K).obj ((S.closure.commonStage.pull (𝟙
          X)).obj L)) ≫
            ((S.closure.commonStageTensor X).obj K).map (e.app L).hom =
          ((S.closure.commonStageTensor X).map
            (((S.closure.commonStage.properIdentification (𝟙 X) c ≪≫
              ((S.closure.commonStage.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
                Adjunction.id)).hom.app K)).app L) := by
  have uc := (projectionIdentity_pullbackUnits S).2.2
  have pc := (projectionIdentity_properCounit S).2.2.2
  have laws := compactSupportProjection_coherenceLaws S
  intro X
  let : IsProper (𝟙 X : X ⟶ X).hom.left := by
    change IsProper (𝟙 X.obj.left)
    infer_instance
  let := (uc X).1
  let := (uc X).2
  refine normalizedIdentityUnitProperty (S.closure.commonStage.pull (𝟙 X))
    (S.closure.commonStage.pullComposition (𝟙 X) (𝟙 X))
    (congrArg (fun f ↦ S.closure.commonStage.pull f) (Category.id_comp (𝟙 X))) _ ?_
  intro e he c K L
  exact identityProjection_of_proper (S.closure.commonStageTensor X)
    (S.closure.commonStage.support (𝟙 X) c) (S.closure.commonStage.direct (𝟙 X))
    (S.closure.commonStage.properIdentification (𝟙 X) c)
    (((S.closure.commonStage.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
      Adjunction.id)
    K L ((S.closure.commonStage.pull (𝟙 X)).obj L) (e.app L).hom
    (compactSupportProjectionComponent S.closure.commonStageExchange (𝟙 X) c K L)
    (compactSupportProperProjection S.closure.commonStageExchange (𝟙 X) K L)
    (laws.2.2.2.1.proper (𝟙 X) c K L trivial) (pc X e he K L)

end WeilConjectures
