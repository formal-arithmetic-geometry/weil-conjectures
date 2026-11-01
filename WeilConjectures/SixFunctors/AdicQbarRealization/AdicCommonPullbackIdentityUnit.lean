/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import all WeilConjectures.PoincareDuality.PodCoefficientDescent.PodReindexingHomCoefficientDescent
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportFiniteStage

/-! # Identity unit for the specified common-stage pullback compositor

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.rationalDerivedPullback WeilConjectures.commonStageDerivedPullback

universe u w u₁ u₂ v₁ v₂
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

private theorem idempotent_unit {C : Type*} [Category C]
    (F : C ⥤ C) [F.Full] [F.Faithful] (c : F ≅ F ⋙ F) :
    ∃ e : F ≅ 𝟭 C, ∀ M, c.hom.app M ≫ e.hom.app (F.obj M) = 𝟙 (F.obj M) := by
  let e : F ≅ 𝟭 C := Functor.fullyFaithfulCancelRight F
    (c.symm ≪≫ (Functor.leftUnitor F).symm)
  have he (M : C) : F.map (e.hom.app M) = c.inv.app M := by
    simp [e]
  have hcomm (M : C) : e.hom.app (F.obj M) = F.map (e.hom.app M) := by
    apply (cancel_mono (e.hom.app M)).1
    exact (e.hom.naturality (e.hom.app M)).symm
  exact ⟨e, fun M ↦ by rw [hcomm, he]; exact c.hom_inv_id_app M⟩

private theorem stage_fullyFaithful
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    {B : I → Type u₂} [∀ i, Category.{v₂} (B i)]
    {S : StageSystem C} {R : StageSystem B} (G : S.Morphism R)
    [∀ i, (G.Φ i).Full] [∀ i, (G.Φ i).Faithful] :
    G.functor.Full ∧ G.functor.Faithful := by
  open StageSystem.PairCategory in
  constructor
  · constructor
    intro P Q f
    induction f using hom_induction with
    | h n hP hQ a =>
      refine ⟨mkHom n hP hQ ((G.Φ n).preimage
        ((G.β hP).inv.app P.obj ≫ a ≫ (G.β hQ).hom.app Q.obj)), ?_⟩
      rw [G.functor_map_mkHom]
      congr 1
      simp only [StageSystem.Morphism.mapAt, Functor.map_preimage, Category.assoc,
        Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
      exact Category.comp_id a
  · constructor
    intro P Q f g hfg
    obtain ⟨n, _, hP, hQ, hP', hQ', a, b, rfl, rfl⟩ :=
      exists_common_stage f g P.stage
    rw [G.functor_map_mkHom, G.functor_map_mkHom] at hfg
    obtain ⟨p, hn, hn', hp⟩ := (mkHom_eq_mkHom_iff' _ _).1 hfg
    rw [G.tr_mapAt, G.tr_mapAt] at hp
    have hab : S.tr hn a = S.tr hn' b := by
      apply (G.Φ p).map_injective
      simpa only [StageSystem.Morphism.mapAt, cancel_epi, cancel_mono] using hp
    exact (mkHom_eq_mkHom_iff' _ _).2 ⟨p, hn, hn', hab⟩

private theorem common_identity_fullyFaithful (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    (commonStageDerivedPullback l (PadicAlgCl l) (𝟙 X)).Full ∧
      (commonStageDerivedPullback l (PadicAlgCl l) (𝟙 X)).Faithful := by
  classical
  have hX (x : X) : IsUnit (l : X.presheaf.stalk x) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using (Invertible.ne_zero (l : X.residueField x))
  have hstage (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
        (𝟙 X)).IsEquivalence := by
    obtain ⟨S⟩ := isomorphismFieldTransportFiniteStage l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) (𝟙 X) hX hX
    exact S.rationalEquivalence
  let := hstage
  obtain ⟨hcoh, hG⟩ := commonStagePullbackNormalizedDescent l (PadicAlgCl l) (𝟙 X)
  rw [hG]
  exact stage_fullyFaithful _

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

private theorem transport_natIso {C B : Type*} [Category C] [Category B]
    {F G F' G' : C ⥤ B} (hF : F = F') (hG : G = G') (c : F ≅ G) :
    ∃ d : F' ≅ G', ∀ M, HEq (d.hom.app M) (c.hom.app M) := by
  subst F'
  subst G'
  exact ⟨c, fun _ ↦ HEq.rfl⟩

private theorem specified_identity_compositor (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    ∃ c : commonStageDerivedPullback l (PadicAlgCl l) (𝟙 X) ≅
        commonStageDerivedPullback l (PadicAlgCl l) (𝟙 X) ⋙
          commonStageDerivedPullback l (PadicAlgCl l) (𝟙 X),
      ∀ M, HEq (c.hom.app M)
        (pullbackTensorCommonComposition l (PadicAlgCl l) (𝟙 X) (𝟙 X) M).hom := by
  have hcopy (g : X ⟶ X) [IsIso g] :
      PodCoefficientDescent.commonPullback l (PadicAlgCl l) g =
        commonStageDerivedPullback l (PadicAlgCl l) g := by
    exact PodCoefficientDescent.commonPullback_eq l (PadicAlgCl l) g
  obtain ⟨c, hc, _⟩ := PodCoefficientDescent.common_compositor_existsUnique l
    (PadicAlgCl l) (𝟙 X) (𝟙 X)
  have hs : PodCoefficientDescent.commonPullback l (PadicAlgCl l) (𝟙 X ≫ 𝟙 X) =
      commonStageDerivedPullback l (PadicAlgCl l) (𝟙 X) :=
    (hcopy (𝟙 X ≫ 𝟙 X)).trans (by rw [Category.id_comp])
  have ht : PodCoefficientDescent.commonPullback l (PadicAlgCl l) (𝟙 X) ⋙
        PodCoefficientDescent.commonPullback l (PadicAlgCl l) (𝟙 X) =
      commonStageDerivedPullback l (PadicAlgCl l) (𝟙 X) ⋙
        commonStageDerivedPullback l (PadicAlgCl l) (𝟙 X) :=
    congrArg (fun F : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ⥤
        generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ↦ F ⋙ F)
      (hcopy (𝟙 X))
  obtain ⟨d, hd⟩ := transport_natIso hs ht c
  exact ⟨d, fun M ↦ (hd M).trans (hc M)⟩

/-- The identity pullback unit cancels the specified twice-identity compositor.
Source: BS Remark 6.8.15; Stacks 07A4 and 0941; the source-identity part of
lem-sf-adic-reindexing-core (blueprint: lem-sf-adic-common-pullback-identity-unit).

Proof: Finite-stage isomorphism transport makes each rational identity pullback
fully faithful. The normalized stage-system descent has the same property: lift a
representative by fullness after conjugating by the transition comparisons; an equality
of images holds at a larger stage, where faithfulness reflects it. This argument uses
only residue-field invertibility, so it also covers empty schemes without requiring
l to differ from the characteristic of the base field.

The existing common compositor theorem makes the specified twice-identity components
into a natural isomorphism c : F ≅ F ⋙ F, for the actual identity pullback F. Its literal
object copies equal the original functors. Fully faithful cancellation on the right
lifts c inverse to e : F ≅ Id, with F(e_M) = c_M inverse. Naturality of e at its own
invertible component gives e_(FM) = F(e_M). Thus c_M followed by e_(FM) is the identity.
The compositor component specification gives exactly the required HEq. -/
theorem exists_common_pullback_identity_unit (D : FiniteFieldDatum.{u})
    (T : GeometricSpace D)
    [∀ x : T.base.left, Invertible (l : T.base.left.residueField x)] :
    ∃ e : commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left) ≅ 𝟭 _,
    ∀ M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left,
      HEq
        ((pullbackTensorCommonComposition l (PadicAlgCl l) (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
          e.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
        (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M)) := by
  let F := commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)
  obtain ⟨hfull, hfaithful⟩ := common_identity_fullyFaithful l T.base.left
  let : F.Full := hfull
  let : F.Faithful := hfaithful
  obtain ⟨c, hc⟩ := specified_identity_compositor l T.base.left
  obtain ⟨e, he⟩ := idempotent_unit F c
  refine ⟨e, fun M ↦ ?_⟩
  have hm : c.hom.app M =
      (pullbackTensorCommonComposition l (PadicAlgCl l)
        (𝟙 T.base.left) (𝟙 T.base.left) M).hom := eq_of_heq (hc M)
  rw [← hm]
  exact heq_of_eq (he M)

end WeilConjectures.AdicQbarRealization
