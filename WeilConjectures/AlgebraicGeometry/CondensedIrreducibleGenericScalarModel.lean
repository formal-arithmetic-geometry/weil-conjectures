/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedGenericScalarModelData

import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedGeometricFieldPerfectModel
import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedContractibleCornerLisseLift
import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedGenericFiberCornerFullyFaithful
import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedSliceSectionComparison

/-! # Generic scalar models on prescribed w-contractible affine covers

Source: HRS Theorem 4.13, diagram (4.4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.MonoidalCategory CondensedGenericScalarModel

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem corner_scalar_comparison
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (T : Scheme.{u}) [IsAffine T] (c : ComponentDerivedSquare.Corner Λ T) :
    ∃ ordinary : ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
        (affineComponentSpace T)).mapMod Λ.X ⋙ c.modules Λ T ≅
      (upperStarFromPoint T).mapMod Λ.X,
      ∀ N, (ordinary.hom.app N).hom = c.beta.hom.app N.X := by
  let F := (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
    (affineComponentSpace T)
  have hcoeff : c.coefficient.inv.hom ≫ c.beta.hom.app Λ.X = 𝟙 _ := by
    rw [← c.coefficient_eq]
    exact congrArg Mon.Hom.hom c.coefficient.inv_hom_id
  let ordinary : F.mapMod Λ.X ⋙ c.modules Λ T ≅
      (upperStarFromPoint T).mapMod Λ.X :=
    NatIso.ofComponents (fun N ↦ Mod.isoMk (c.beta.app N.X) (by
      have h := Mod.act_hom
        ((Functor.mapModCompIso F c.inverse c.beta.hom Λ.X).hom.app N)
      change Mod.act ((c.inverse.mapMod (F.obj Λ.X)).obj ((F.mapMod Λ.X).obj N)).X ≫
        c.beta.hom.app N.X =
        c.inverse.obj (F.obj Λ.X) ◁ c.beta.hom.app N.X ≫
          (c.beta.hom.app Λ.X ▷ _ ≫ Mod.act
            (((upperStarFromPoint T).mapMod Λ.X).obj N).X) at h
      change (c.coefficient.inv.hom ▷ _ ≫ Mod.act
          ((c.inverse.mapMod (F.obj Λ.X)).obj ((F.mapMod Λ.X).obj N)).X) ≫
        c.beta.hom.app N.X = _
      rw [Category.assoc, h]
      erw [← whisker_exchange_assoc]
      erw [← comp_whiskerRight_assoc, hcoeff, id_whiskerRight, Category.id_comp]
      rfl))
      (fun f ↦ Mod.hom_ext _ _ (c.beta.hom.naturality f.hom))
  exact ⟨ordinary, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A dualizable complex on a nonempty irreducible affine scheme has a perfect geometric
generic scalar model; every such model trivializes it on every prescribed affine faithfully
flat ind-etale cover with w-contractible source, with component descent along every section.

Source: HRS Theorem 4.13, irreducible case, diagram (4.4) and the following paragraph;
Lemma 4.1 and Proposition 4.3(3)
(blueprint: lem-zl-condensed-irreducible-generic-scalar-model).

Proof for stage 3, following the four DAG steps.
1. Pullback to eta preserves dualizability by lem-zl-condensed-lisse-proetale-locality.
   Use lem-weil-pbc-geometric-field-proetale-evaluation and the one-point profinite case
   of lem-zl-condensed-wcontractible-lisse-evaluation to obtain the perfect P and alpha.
2. Fix any such P and alpha and any prescribed cover f. The generic-fibre component
   section theorem lem-zl-generic-fiber-components-section gives a continuous splitting
   of r, the component square and the coefficient-compatible equivalence on the fibre.
3. Pullback preserves dualizability. Component evaluation gives M and beta. Apply
   lem-zl-component-derived-pullback-square to the first projection of the fibre.
   The composition comparisons of lem-sfb-ringed-derived-monoidal-comparisons identify
   its two restrictions of K. Pull beta and alpha back and use the scalar comparisons.
   Full faithfulness on the generic fibre descends this composite to delta; its defining
   equality is generic_induced in CoverModel.
4. For any section s, composition with r is the identity and composition with the
   structure map to the point is the structure map. The identity and composition
   comparisons of lem-sfb-ringed-derived-monoidal-comparisons therefore identify
   s* r* M with M and s* L(P) with L(P). Pulling delta back gives gamma and the sections
   equality. Applying component inverse image and beta gives model with the same P.
   Neither reducedness nor coefficient flatness enters any step. -/
theorem condensed_irreducible_generic_scalar_model
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IsAffine X] [Nonempty X] [IrreducibleSpace X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ X)
    (hη : ∀ x : Spec (.of Ω), η x = genericPoint X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (hK : Nonempty (HasRightDual K)) :
    (∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
      DerivedCategory.IsPerfectRingComplex P ∧
      Nonempty ((CondensedRing.upperStar Λ.X η).mapDerivedCategory.obj K ≅
        (condensedScalarRealization Λ.X (Spec (.of Ω))).obj P)) ∧
    (∀ (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X))),
      DerivedCategory.IsPerfectRingComplex P →
      ∀ (α : (CondensedRing.upperStar Λ.X η).mapDerivedCategory.obj K ≅
          (condensedScalarRealization Λ.X (Spec (.of Ω))).obj P)
        (U : Scheme.{u}) [IsAffine U] (f : U ⟶ X),
        f.appTop.hom.FaithfullyFlat → RingHom.IndEtaleAcrossUniverses f.appTop.hom →
        IsWContractibleRing Γ(U, ⊤) →
        Nonempty (CondensedGenericScalarModel.CoverModel Λ f Ω η K P α)) := by
  classical
  constructor
  · exact geometric_field_perfect_model Λ Ω _
      (condensed_derivedPullback_preserves_dualizable Λ η K hK)
  · intro P _ α U _ f hff hind hw
    let := hw
    obtain ⟨system⟩ := ComponentDerivedSquare.component_derived_pullback_square Λ
    let cU := system.corner U
    let cV := system.corner (pullback f η)
    let restriction := system.slice (pullback.fst f η)
    let square := system.square (pullback.fst f η)
    obtain ⟨scalarU, hscalarU⟩ := corner_scalar_comparison Λ U cU
    obtain ⟨scalarV, hscalarV⟩ := corner_scalar_comparison Λ (pullback f η) cV
    obtain ⟨scalarH, hscalarH⟩ := scheme_scalar_comparison Λ (pullback.snd f η)
    obtain ⟨M, hM, ⟨β⟩⟩ := contractible_corner_lisse_lift Λ U cU _
      (condensed_derivedPullback_preserves_dualizable Λ f K hK)
    obtain ⟨fullyFaithful⟩ := generic_fiber_corner_fully_faithful Λ f Ω η hind cV
    let d := (square.theta Λ).symm.app M ≪≫
      (CondensedRing.upperStar Λ.X (pullback.fst f η)).mapDerivedCategory.mapIso β ≪≫
      genericRestriction Λ f Ω η K ≪≫
      (CondensedRing.upperStar Λ.X (pullback.snd f η)).mapDerivedCategory.mapIso α ≪≫
      (schemeScalarComparison Λ (pullback.snd f η) scalarH).app P ≪≫
      ((cornerScalarComparison Λ (pullback f η) cV scalarV).app P).symm
    let δ := fullyFaithful.preimageIso d
    have hδ : (cV.derived Λ (pullback f η)).mapIso δ = d :=
      fullyFaithful.isoEquiv.apply_symm_apply d
    have hsplitting : ∃ s : affineComponentSpace U ⟶
        affineComponentSpace (pullback f η),
        s ≫ affineComponentMap (pullback.fst f η) = 𝟙 _ := by
      let : Flat f := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mpr hff |>.1
      have hr : Function.Surjective
          (pullback.fst f η).continuous.connectedComponentsMap := by
        intro c
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
        obtain ⟨y, hyx, hy⟩ := Flat.generalizingMap f (genericPoint_specializes (f x))
        let z : Spec (.of Ω) := IsLocalRing.closedPoint Ω
        obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback y z
          (hy.trans (hη z).symm)
        refine ⟨ConnectedComponents.mk v, ?_⟩
        rw [Continuous.connectedComponentsMap_mk, hv]
        exact hyx.connectedComponents_mk_eq
      let e : U ≃ₜ PrimeSpectrum Γ(U, ⊤) :=
        TopCat.homeoOfIso (Scheme.forgetToTop.mapIso U.isoSpec)
      let ec : ConnectedComponents U ≃ₜ
          ConnectedComponents (PrimeSpectrum Γ(U, ⊤)) :=
        e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (fun y ↦ by
          rw [show e ⁻¹' {y} = {e.symm y} by
            ext x
            exact (Equiv.eq_symm_apply e.toEquiv).symm]
          exact isConnected_singleton)
      let : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum Γ(U, ⊤))) :=
        IsWContractibleRing.extremallyDisconnected_connectedComponents
      let : ExtremallyDisconnected (affineComponentSpace U) :=
        extremallyDisconnected_of_homeo ec.symm
      obtain ⟨s, hs, he⟩ :=
        (CompactT2.ExtremallyDisconnected.projective (A := affineComponentSpace U))
          continuous_id (pullback.fst f η).continuous.connectedComponentsMap_continuous hr
      refine ⟨ConcreteCategory.ofHom ⟨s, hs⟩, ?_⟩
      ext x
      exact congrFun he x
    have hsections : ∀ s : affineComponentSpace U ⟶
        affineComponentSpace (pullback f η),
        s ≫ affineComponentMap (pullback.fst f η) = 𝟙 _ →
        ∃ (c : SectionComparison Λ (affineComponentMap (pullback.fst f η)) s restriction)
          (γ : M ≅
            (CondensedRing.profiniteScalarRealization Λ.X (affineComponentSpace U)).obj P),
          (c.inverse.derived Λ).mapIso δ ≪≫ (c.scalarDerived Λ).app P =
            (c.identityDerived Λ).app M ≪≫ γ := by
      intro s hs
      obtain ⟨c⟩ := slice_section_comparison Λ _ s hs restriction
      let γ := ((c.identityDerived Λ).app M).symm ≪≫
        (c.inverse.derived Λ).mapIso δ ≪≫ (c.scalarDerived Λ).app P
      exact ⟨c, γ, by simp [γ]⟩
    obtain ⟨s, hs⟩ := hsplitting
    obtain ⟨_, γ, _⟩ := hsections s hs
    refine ⟨{
      cornerU := cU
      cornerV := cV
      restriction := restriction
      square := square
      scalarV := scalarV
      scalarV_underlying := hscalarV
      scalarH := scalarH
      scalarH_underlying := hscalarH
      M := M
      dualizable := hM
      beta := β
      delta := δ
      generic_induced := ?_
      splitting := ⟨s, hs⟩
      sections := hsections
      model := β.symm ≪≫ (cU.derived Λ U).mapIso γ ≪≫
        (cornerScalarComparison Λ U cU scalarU).app P }⟩
    rw [hδ]
    simp only [d, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end AlgebraicGeometry.ProEtale
