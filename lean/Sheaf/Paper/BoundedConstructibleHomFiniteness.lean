/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.Analysis.Normed.Field.TransferInstance

/-!
# Internal Hom finiteness for finite coefficient extensions in the scheme universe

Source: Weil conjectures blueprint, main-20261015,
`sec-six-functors-basics/sk-def-sfb-dc-restricted-functors/lem-sfb-dc-hom-preserves.md`;
the node's reviewed Bhatt--Scholze proof, steps 1--8 (blueprint: lem-sfb-dc-hom-preserves).

The published finiteness class only constructs continuous coefficients from fields in
`Type 0`. This statement uses the already published universe-generalized continuous
coefficient ring for any finite normed extension in the scheme universe. The integral
coefficient ring is the closed unit ball, explicitly characterized by `hO`.
The algebraic-closure case is the imported existing
`isMonoidalClosed_boundedConstructible`, using its `algebraicClosure` coefficient instance.
No coefficient ring, derived internal Hom or constructibility notion is redefined.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma small_model (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (E₀ : Type) (_ : NormedField E₀) (_ : NormedAlgebra ℚ_[ℓ] E₀)
      (_ : FiniteDimensional ℚ_[ℓ] E₀), ∃ e : E₀ ≃+* E,
      (∀ x, ‖e x‖ = ‖x‖) ∧ Continuous e ∧ Continuous e.symm := by
  have : Small.{0} E := Module.Finite.small ℚ_[ℓ] E
  let e := (equivShrink E).symm
  let : NormedField (Shrink.{0} E) := e.normedField
  let : Algebra ℚ_[ℓ] (Shrink.{0} E) := e.algebra ℚ_[ℓ]
  let : NormedAlgebra ℚ_[ℓ] (Shrink.{0} E) :=
    { toAlgebra := e.algebra ℚ_[ℓ]
      norm_smul_le c x := by
        change ‖e (e.symm (c • e x))‖ ≤ ‖c‖ * ‖e x‖
        rw [e.apply_symm_apply]
        exact norm_smul_le c _ }
  have : FiniteDimensional ℚ_[ℓ] (Shrink.{0} E) :=
    (e.algEquiv ℚ_[ℓ]).toLinearEquiv.symm.finiteDimensional
  refine ⟨Shrink.{0} E, inferInstance, inferInstance, inferInstance, e.ringEquiv,
    fun x ↦ rfl, ?_, ?_⟩
  · exact (show Isometry e from fun x y ↦ rfl).continuous
  · exact (show Isometry e.symm from fun x y ↦ by
      change edist (e (e.symm x)) (e (e.symm y)) = edist x y
      simp).continuous

private noncomputable def coefficientIso (T : Type) (V : Type u)
    [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
    [TopologicalSpace V] [Ring V] [IsTopologicalRing V]
    (e : T ≃+* V) (hc : Continuous e) (hc' : Continuous e.symm) :
    Profinite.continuousMapRingSheaf.{u} T ≅
      Profinite.continuousCoefficientRingSheaf V where
  hom := ⟨{
    app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.compLeftContinuous S.unop hc).comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := by ext; rfl }⟩
  inv := ⟨{
    app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.compLeftContinuous S.unop hc').comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := by ext; rfl }⟩
  hom_inv_id := by
    ext S x
    exact congrArg ULift.up (ContinuousMap.ext (fun a ↦ e.symm_apply_apply (x.down a)))
  inv_hom_id := by
    ext S x
    exact congrArg ULift.up (ContinuousMap.ext (fun a ↦ e.apply_symm_apply (x.down a)))

section CoefficientTransport
variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

private lemma cons_comap
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsConstructibleModuleObject S M) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj M) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun a ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (s.immersion a)
  exact lfp_of_iso (lfp_comap (F.map φ) (hs a))
    ((F.mapModComapIso φ).app M).symm

private lemma bc_comap
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)}
    (h : boundedConstructible S K) :
    boundedConstructible R ((Mod.comap φ).mapDerivedCategory.obj K) := by
  refine ⟨Functor.bounded_mapDerivedCategory_obj _ h.1, fun n ↦ ?_⟩
  exact constructible_of_iso R
    (((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K)
    (cons_comap φ (h.2 n))

private lemma bc_of_comap
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)}
    (h : boundedConstructible R ((Mod.comap φ).mapDerivedCategory.obj K)) :
    boundedConstructible S K := by
  refine ⟨Functor.bounded_of_bounded_mapDerivedCategory_obj _ h.1, fun n ↦ ?_⟩
  have hc := cons_comap (inv φ)
    (constructible_of_iso R
      (((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K).symm (h.2 n))
  exact constructible_of_iso S
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app
      ((DerivedCategory.homologyFunctor _ n).obj K)).symm hc

set_option maxHeartbeats 800000 in
-- Derive the strong monoidal comparison through the exact module equivalence.
private lemma closure_transport (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    (h : (boundedConstructible R).IsMonoidalClosed) :
    (boundedConstructible S).IsMonoidalClosed := by
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R := Mod.comap φ
  have : F.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso φ).functor.IsEquivalence
  have : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  let : F.leftDerivedFunctor.Monoidal := Functor.residueDerivedMonoidal F
  let : F.mapDerivedCategory.Monoidal :=
    Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory
  let e := F.mapDerivedCategory.asEquivalence
  have : (boundedConstructible R).IsMonoidalClosed := h
  refine ⟨fun K L hK hL ↦ ?_⟩
  apply bc_of_comap φ
  let adj := e.toAdjunction
  let adj' : tensorLeft K ⊣
      e.functor ⋙ ihom (e.functor.obj K) ⋙ e.inverse :=
    (adj.comp ((ihom.adjunction (e.functor.obj K)).comp e.symm.toAdjunction)).ofNatIsoLeft
      (Iso.compInverseIso (H := e) (Functor.Monoidal.commTensorLeft F.mapDerivedCategory K))
  let i := ((ihom.adjunction K).rightAdjointUniq adj').app L
  let j := e.functor.mapIso i ≪≫
    e.counitIso.app ((ihom (e.functor.obj K)).obj (e.functor.obj L))
  have hb := (boundedConstructible R).prop_ihom (bc_comap φ hK) (bc_comap φ hL)
  refine ⟨?_, fun n ↦ ?_⟩
  · exact (DerivedCategory.TStructure.t.bounded).prop_of_iso j.symm hb.1
  · exact constructible_of_iso R
      ((DerivedCategory.homologyFunctor _ n).mapIso j.symm) (hb.2 n)
end CoefficientTransport

private lemma closure_of_continuousRingEquiv (T : Type) (V : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace V] [CommRing V] [IsTopologicalRing V]
    (e : T ≃+* V) (hc : Continuous e) (hc' : Continuous e.symm) (X : Scheme.{u})
    (h : (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj T) X)).IsMonoidalClosed) :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj V) X)).IsMonoidalClosed := by
  let i := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (coefficientIso T V e hc hc')
  have : IsMonHom i.hom := Sheaf.isMonHom_sheafCompose_map
    (coherentTopology Profinite.{u}) (coefficientIso T V e hc hc').hom
  let φ := (upperStarFromPoint X).map i.hom
  have : IsMonHom φ := inferInstance
  exact closure_transport φ h

/-- The rational and integral finite-extension cases of internal Hom finiteness, without
restricting the coefficient carrier to Type 0. The subring `O` is exactly the ring of integers,
by `hO`. A `NormedAlgebra` structure supplies the topology of the extending absolute value.
`ObjectProperty.IsMonoidalClosed` means solely that internal Hom carries two objects with
the given property to an object with that property; it imposes no tensor closure condition.

Source: the node's reviewed proof from Bhatt--Scholze, Sections 3.4, 6.7 and 6.8,
steps 1--8 (blueprint: lem-sfb-dc-hom-preserves).

Proof: a finite-dimensional algebra over the Type 0 field `ℚ_[ℓ]` is small, by
`Module.Finite.small`. Transport its norm, field and algebra structures to `Shrink E`.
The resulting ring equivalence is an isometry in both directions. Pull back `O` along
this equivalence; its membership condition is exactly the closed-unit-ball condition.
Postcomposition induces isomorphisms of the rational and integral condensed ring sheaves.
Pull these isomorphisms to `X`. Restriction of scalars along a ring isomorphism preserves
and reflects finite local presentations on each stratum, hence bounded constructibility.
Its exact derived equivalence is strong monoidal, so uniqueness of right adjoints identifies
the two internal Homs. Apply the existing Type 0 `isMonoidalClosed_boundedConstructible`
instance and transport both conclusions back along these equivalences.
-/
lemma boundedConstructibleHom_finiteExtension
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X.left)).IsMonoidalClosed ∧
    (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj O) X.left)).IsMonoidalClosed := by
  obtain ⟨E₀, hfield, halgebra, hfinite, e, hnorm, hc, hc'⟩ := small_model ℓ E
  let := hfield
  let := halgebra
  let := hfinite
  let O₀ := O.comap e.toRingHom
  have hO₀ : ∀ x : E₀, x ∈ O₀ ↔ ‖x‖ ≤ 1 := by
    intro x
    change e x ∈ O ↔ ‖x‖ ≤ 1
    rw [hO, hnorm]
  let eO : O₀ ≃+* O :=
    { toFun := fun x ↦ ⟨e x, x.property⟩
      invFun := fun y ↦ ⟨e.symm y, by
        change e (e.symm (y : E)) ∈ O
        simpa only [e.apply_symm_apply] using y.property⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hcO : Continuous eO := (hc.comp continuous_subtype_val).subtype_mk _
  have hcO' : Continuous eO.symm := (hc'.comp continuous_subtype_val).subtype_mk _
  have : IsEllAdicFinitenessCoefficient ℓ (Profinite.continuousMapRingObj O₀) :=
    .unitBall E₀ O₀ hO₀
  exact ⟨closure_of_continuousRingEquiv E₀ E e hc hc' X.left (by infer_instance),
    closure_of_continuousRingEquiv O₀ O eO hcO hcO' X.left (by infer_instance)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
