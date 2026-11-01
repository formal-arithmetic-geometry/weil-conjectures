/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.ProperCoordinates.IntegralProperProjectionCoefficientData
import WeilConjectures.SixFunctors.IntegralProjectionReduction.SystemIdentityOpenEvaluation
import WeilConjectures.SixFunctors.Integral.IntegralReductionJointFaithfulness
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralSupportAdjunctFiniteCoordinates
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionPullEvaluation
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralSupportReductionNormalization

/-! # Identity-open normalization of the support comparison

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open CategoryTheory.Functor
namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization
open FixProjectionCompactification.Coordinates
open ProperCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

attribute [local implicit_reducible] integralCoefficientSheaf
  scalarReductionSourceDerived scalarReductionTargetDerived integralTowerHasDerivedCategory
  coefficientFiniteHasDerived reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  sfAmbientCompactSupportCandidate sfIntrinsicCompactSupport sixFunctorFinitePullback
  sixFunctorFiniteSupport sixFunctorIntegralReduction coefficientFiniteDerivedExtension
  scalarReductionDerivedExtension

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  SheafOfModules.instAbelian coefficientSequenceLimit
  ProperCoordinates.openIdentity FixProjectionCompactification.Coordinates.supportReduction
  FixProjectionCompactification.Coordinates.supportValue
  FixProjectionCompactification.Coordinates.reconstruction

/-- A commuting square of left-adjoint comparisons gives the right-adjoint square. -/
private theorem evaluated_mate
    {A B N M U V : Type*} [Category A] [Category B] [Category N] [Category M]
    [Category U] [Category V]
    {F : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G)
    {P : N ⥤ M} {Q : M ⥤ N} (b : P ⊣ Q)
    {L : U ⥤ V} {R : V ⥤ U} (c : L ⊣ R)
    {I : A ⥤ N} {J : B ⥤ M} {r : A ⥤ U} {s : B ⥤ V}
    {v : N ⥤ U} {w : M ⥤ V}
    (p : F ⋙ J ≅ I ⋙ P) (rho : I ⋙ v ≅ r) (sigma : J ⋙ w ≅ s)
    (eL : F ⋙ s ≅ r ⋙ L) (eR : G ⋙ r ≅ s ⋙ R)
    (ec : ∀ y : B, L.map (eR.hom.app y) ≫ c.counit.app (s.obj y) =
      eL.inv.app (G.obj y) ≫ s.map (a.counit.app y))
    (tL : P ⋙ w ≅ v ⋙ L) (tR : Q ⋙ v ≅ w ⋙ R)
    (tc : ∀ y : M, L.map (tR.hom.app y) ≫ c.counit.app (w.obj y) =
      tL.inv.app (Q.obj y) ≫ w.map (b.counit.app y))
    (h : ∀ x : A, w.map (p.hom.app x) ≫ tL.hom.app (I.obj x) ≫
        L.map (rho.hom.app x) = sigma.hom.app (F.obj x) ≫ eL.hom.app x)
    (y : B) :
    v.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ p.inv)).natTrans.app y) ≫
        tR.hom.app (J.obj y) ≫ R.map (sigma.hom.app y) =
      rho.hom.app (G.obj y) ≫ eR.hom.app y := by
  have hi (x : A) :
      tL.inv.app (I.obj x) ≫ w.map (p.inv.app x) ≫ sigma.hom.app (F.obj x) =
        L.map (rho.hom.app x) ≫ eL.inv.app x := by
    apply (cancel_epi (w.map (p.hom.app x) ≫ tL.hom.app (I.obj x))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    erw [← w.map_comp_assoc, p.hom_inv_id_app, w.map_id, Category.id_comp]
    erw [reassoc_of% (h x), Iso.hom_inv_id_app, Category.comp_id]
  apply (c.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hc := c.counit.naturality (sigma.hom.app y)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hc
  erw [hc]
  erw [← Category.assoc (L.map (tR.hom.app (J.obj y))), tc (J.obj y)]
  simp only [Category.assoc]
  have ht := tL.inv.naturality
    ((mateEquiv a b (TwoSquare.mk _ _ _ _ p.inv)).natTrans.app y)
  simp only [Functor.comp_map, Functor.comp_obj] at ht
  erw [reassoc_of% ht]
  erw [← w.map_comp_assoc, mateEquiv_counit]
  erw [w.map_comp, Category.assoc]
  have hn := sigma.hom.naturality (a.counit.app y)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [hn]
  erw [reassoc_of% (hi (G.obj y)), ← ec]

/-- The counit equation is preserved by pasting coefficient comparisons. -/
private theorem paste_counit
    {A B U V U' V' : Type*} [Category A] [Category B] [Category U] [Category V]
    [Category U'] [Category V']
    {F : A ⥤ B} {G : B ⥤ A} {L : U ⥤ V} {R : V ⥤ U}
    {L' : U' ⥤ V'} {R' : V' ⥤ U'}
    {a : F ⊣ G} {b : L ⊣ R} {c : L' ⊣ R'}
    {r : A ⥤ U} {s : B ⥤ V} {v : U ⥤ U'} {w : V ⥤ V'}
    (e : SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison a b r s)
    (t : SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison b c v w)
    (y : B) :
    L'.map (v.map (e.right.hom.app y) ≫ t.right.hom.app (s.obj y)) ≫
        c.counit.app (w.obj (s.obj y)) =
      t.left.inv.app (r.obj (G.obj y)) ≫ w.map (e.left.inv.app (G.obj y)) ≫
        w.map (s.map (a.counit.app y)) := by
  erw [L'.map_comp, Category.assoc, t.counit]
  have hn := t.left.inv.naturality (e.right.hom.app y)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [← Category.assoc, hn]
  simp only [Category.assoc]
  erw [← w.map_comp, e.counit, w.map_comp]

/-- Fullness and faithfulness of reduction on the complete constructible subcategory. -/
private def reduction_fullyFaithful
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D) :
    (reduce (C := C) (E := E) X).FullyFaithful := by
  let A := calculus C.l E X.obj.left
  let I := (sfIntegralConstructible C.l E X.obj.left).ι
  have hu (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
      (reconstruction D C E X.obj.left K).inv = A.adjunction.unit.app K.obj := by
    simp only [reconstruction, Iso.symm_inv, asIso_hom, A]
  have hr (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
      A.reduction.map (reconstruction D C E X.obj.left K).hom =
        A.adjunction.counit.app (A.reduction.obj K.obj) := by
    apply (cancel_epi (A.reduction.map (reconstruction D C E X.obj.left K).inv)).mp
    erw [← A.reduction.map_comp, Iso.inv_hom_id, A.reduction.map_id, hu]
    exact (A.adjunction.left_triangle_components K.obj).symm
  refine
    { preimage := fun {K L} f ↦ ObjectProperty.homMk
        ((reconstruction D C E X.obj.left K).inv ≫
          (coefficientSequenceLimit C.l E X.obj.left).map f ≫
          (reconstruction D C E X.obj.left L).hom)
      map_preimage := ?_
      preimage_map := ?_ }
  · intro K L f
    change A.reduction.map (_ ≫ _ ≫ _) = f
    erw [A.reduction.map_comp, A.reduction.map_comp, hr]
    have hn := A.adjunction.counit.naturality f
    change A.reduction.map ((coefficientSequenceLimit C.l E X.obj.left).map f) ≫
      A.adjunction.counit.app (A.reduction.obj L.obj) =
        A.adjunction.counit.app (A.reduction.obj K.obj) ≫ f at hn
    erw [hn]
    erw [← Category.assoc, hu, A.adjunction.left_triangle_components K.obj, Category.id_comp]
  · intro K L f
    apply I.map_injective
    change _ ≫ _ ≫ _ = f.hom
    erw [hu]
    change A.adjunction.unit.app K.obj ≫
      (A.reduction ⋙ coefficientSequenceLimit C.l E X.obj.left).map f.hom ≫ _ = f.hom
    erw [← Category.assoc, ← A.adjunction.unit.naturality f.hom]
    simp only [Functor.id_map, Category.assoc]
    erw [← hu, Iso.inv_hom_id, Category.comp_id]

/-- Evaluation detects maps between reduced constructible objects, by reconstruction. -/
private theorem reduced_maps_ext
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (X : SixFunctorSpace D)
    {K L : sfIntegralConstructibleCategory C.l E X.obj.left}
    (a b : (reduce X).obj K ⟶ (reduce X).obj L)
    (h : ∀ m : ℕ, (evaluation (C := C) (E := E) m X).map a =
      (evaluation (C := C) (E := E) m X).map b) : a = b := by
  let FF := reduction_fullyFaithful (C := C) (E := E) X
  have hab : FF.preimage a = FF.preimage b := by
    apply integral_reductions_jointly_faithful d X
    intro m
    apply (finiteInclusion (C := C) (E := E) m X).map_injective
    apply (cancel_epi (reductionEvaluation d m X K).hom).mp
    have ha := ((calculus C.l E X.obj.left).reductionEvaluation m).hom.naturality
      (FF.preimage a).hom
    have hb := ((calculus C.l E X.obj.left).reductionEvaluation m).hom.naturality
      (FF.preimage b).hom
    change (evaluation (C := C) (E := E) m X).map ((reduce X).map (FF.preimage a)) ≫
      (reductionEvaluation d m X L).hom = _ at ha
    change (evaluation (C := C) (E := E) m X).map ((reduce X).map (FF.preimage b)) ≫
      (reductionEvaluation d m X L).hom = _ at hb
    erw [FF.map_preimage] at ha hb
    exact ha.symm.trans ((congrArg
      (fun v ↦ v ≫ (reductionEvaluation d m X L).hom) (h m)).trans hb)
  exact (FF.map_preimage a).symm.trans
    ((congrArg (fun v ↦ (reduce X).map v) hab).trans (FF.map_preimage b))

/-- The evaluation comparison on proper image respects identity-open cancellation. -/
private theorem proper_identity_evaluation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (m : ℕ) (M : System C.l E X) :
    (coefficientSequenceDerivedEvaluation C.l E Y m).map
        ((Operations.push C.l E o f).map ((openIdentity o z X).hom.app M)) ≫
      ((o.evaluation f).evaluation m).hom.app M =
    (supportEvaluation C.l E o (.ofIsProper f) m).hom.app M ≫
      (@sixFunctorProperCandidateIso (Padic.coefficientExtensionRing C.l E (m + 1)) _
        (Padic.finite_coefficientExtensionRing C.l E (m + 1)
          (Nat.le_add_left 1 m)) X Y f _).hom.app
            ((coefficientSequenceDerivedEvaluation C.l E X m).obj M) := by
  have hn := ((o.evaluation f).evaluation m).hom.naturality
    ((openIdentity o z X).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  erw [hn]
  erw [systemIdentityOpenEvaluation o z X m M]
  simp only [supportEvaluation, sixFunctorProperCandidateIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Functor.map_comp, Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
    Category.assoc,
    Compactification.ofIsProper]

set_option maxHeartbeats 2000000 in
-- Transporting the derived adjunctions checks several dependent functor squares.
/-- Evaluation of the direct mate is the datum's finite direct comparison. -/
private theorem direct_evaluation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (m : ℕ)
    (hl : IsUnit (C.l : D.k)) (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (evaluation (C := C) (E := E) m Y).map ((direct d.higher hl o z f).app K) ≫
        ((o.evaluation f.hom.left).evaluation m).hom.app ((reduce X).obj K) ≫
        (proEtaleConstantDerivedDirectImage f.hom.left
          (Padic.coefficientExtensionRing C.l E (m + 1))).map
          (reductionEvaluation d m X K).hom =
      (reductionEvaluation d m Y ((d.higher.integral.direct f).obj K)).hom ≫
        (finiteInclusion (C := C) (E := E) m Y).map
          (((d.integralNormalization.reduction m).directAdjunction f).right.hom.app K) ≫
        ((stage d m).finiteDirectImage f).hom.app ((reduction d m X).obj K) := by
  let F := stage d m
  let beta := (d.integralNormalization.reduction m).directAdjunction f
  let IX := finiteInclusion (C := C) (E := E) m X
  let IY := finiteInclusion (C := C) (E := E) m Y
  let RX := reduction d m X
  let RY := reduction d m Y
  let rhoX : reduce X ⋙ evaluation (C := C) (E := E) m X ≅ RX ⋙ IX :=
    Functor.isoWhiskerLeft (sfIntegralConstructible C.l E X.obj.left).ι
      ((calculus C.l E X.obj.left).reductionEvaluation m)
  let rhoY : reduce Y ⋙ evaluation (C := C) (E := E) m Y ≅ RY ⋙ IY :=
    Functor.isoWhiskerLeft (sfIntegralConstructible C.l E Y.obj.left).ι
      ((calculus C.l E Y.obj.left).reductionEvaluation m)
  obtain ⟨gamma, hgL, hgR⟩ := F.finiteDirectAdjunctionNormalization f
  let eL := Functor.isoWhiskerRight beta.left IX ≪≫
    Functor.isoWhiskerLeft RY gamma.left
  let eR := Functor.isoWhiskerRight beta.right IY ≪≫
    Functor.isoWhiskerLeft RX gamma.right
  have ec (M : sfIntegralConstructibleCategory C.l E X.obj.left) :
      (finiteDerivedPullback C.l E m f.hom.left).map (eR.hom.app M) ≫
          (finiteAdj C.l E f.hom.left m).counit.app ((RX ⋙ IX).obj M) =
        eL.inv.app ((d.higher.integral.direct f).obj M) ≫
          (RX ⋙ IX).map ((d.higher.integral.pullDirectAdjunction f).counit.app M) := by
    simpa only [eL, eR, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
      Category.assoc, finiteAdj, finiteDerivedPullback, sfIntrinsicDerivedPullback,
      IX, IY, RX, RY, finiteInclusion, reduction, Functor.comp_obj,
      integralCoefficientSheaf, scalarReductionTarget, normalizedDVRModules,
      normalizedDVRDerived, proEtaleDerivedCategory, proEtaleRingModules,
      proEtaleConstantRing]
      using paste_counit beta gamma M
  have hp (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
      (evaluation (C := C) (E := E) m X).map
          ((pullComparison d.higher hl o z f).hom.app L) ≫
        (pullbackTensorDerivedEvaluation C.l E f.hom.left m).hom.app ((reduce Y).obj L) ≫
        (finiteDerivedPullback C.l E m f.hom.left).map (rhoY.hom.app L) =
      rhoX.hom.app ((d.higher.integral.pull f).obj L) ≫ eL.hom.app L := by
    have h := integralProjectionPullEvaluation d m hl o z f L
    have h' := congrArg (fun v ↦ v ≫ (F.finitePullback f).hom.app (RY.obj L)) h
    erw [pullComparison_hom_app]
    simp only [eL, hgL, F, RY, RX, IX, rhoX, rhoY, evaluatedPull,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_app, beta, pullIso,
      reductionEvaluation, reduce, Functor.comp_obj, ObjectProperty.ι_obj,
      integralCoefficientSheaf, scalarReductionTarget, normalizedDVRModules,
      normalizedDVRDerived, proEtaleDerivedCategory,
      ObjectProperty.ι_map, ObjectProperty.isoMk_hom, ObjectProperty.homMk] at h' ⊢
    erw [Category.comp_id] at h'
    exact h'
  have tc (M : System C.l E X.obj.left) :
      (finiteDerivedPullback C.l E m f.hom.left).map
          (((o.evaluation f.hom.left).evaluation m).hom.app M) ≫
        (finiteAdj C.l E f.hom.left m).counit.app ((evaluation m X).obj M) =
      (pullbackTensorDerivedEvaluation C.l E f.hom.left m).inv.app
          ((o.direct f.hom.left).direct.obj M) ≫
        (evaluation m X).map ((o.direct f.hom.left).adj.counit.app M) := by
    apply (cancel_epi ((pullbackTensorDerivedEvaluation C.l E f.hom.left m).hom.app
      ((o.direct f.hom.left).direct.obj M))).mp
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
      (o.evaluation f.hom.left).counit m M
  have h := evaluated_mate (d.higher.integral.pullDirectAdjunction f)
    (o.direct f.hom.left).adj (finiteAdj C.l E f.hom.left m)
    (pullComparison d.higher hl o z f) rhoY rhoX eL eR ec
    (pullbackTensorDerivedEvaluation C.l E f.hom.left m)
    ((o.evaluation f.hom.left).evaluation m)
    tc hp K
  simpa only [direct, eR, hgR, F, RX, IY, IX, rhoX, rhoY, reductionEvaluation, beta,
    Iso.app_hom, Functor.comp_obj, ObjectProperty.ι_obj,
    integralCoefficientSheaf, scalarReductionTarget, normalizedDVRModules,
    normalizedDVRDerived, proEtaleDerivedCategory,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using h

set_option maxHeartbeats 2000000 in
-- Finite-coordinate pasting must elaborate the dependent normalization comparisons.
/-- At the identity-open compactification, the one-input support comparison and
the direct-image mate agree after the canonical identity-open cancellation. There
is no tensor or projection map in this statement.

Source: fix-prop-projection-formula.proof.md, proper counit normalization in successive
reductions; finiteProperNormalization and the coefficient properIdentity equation.
(blueprint: lem-sf-integral-proper-support-reduction-identity).

Proof: compare the actual properIdentity with the proper comparison constructed
from the identity-open support value. At every finite quotient, supportProjection
and directProjection identify their endpoint maps with the specified Roos
projections. Apply the coefficient comparison's properIdentity equation, and then
finiteProperNormalization. Both resulting maps are the finite direct image of the
identity-open unit comparison. The bounded constructible integral reduction
faithfulness theorem identifies the original integral maps. In supportValue,
substitute this equality and expand the proper/limit comparison as the right-adjoint
conjugate of reductionPull. The identity-open reduction is its open-adjunction mate.
Transpose supportValue inverse under reduction/limit. Naturality moves its actual
reconstruction counit past the identity-open unit, and the triangle identity cancels
that unit with inverse reconstruction. The remaining map is precisely the mate of
pullComparison inverse, which defines direct. The canonical bridge's identity open
is normalized by the same unit, so the remaining cancellation is openIdentity.
This is an equality of whole-system maps, obtained by adjunction, not by assuming
that finite evaluation is faithful. No choice of a new comparison occurs. -/
theorem integralProperSupportReductionIdentity
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    {n : ℕ} {hn : 1 ≤ n} (d : SixFunctorOperationDatum D C E n hn)
    (hl : IsUnit (C.l : D.k)) (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    supportReduction D C E d.higher hl o z f (.ofIsProper f.hom.left) K ≫
        (Operations.push C.l E o f.hom.left).map
          ((openIdentity o z X.obj.left).hom.app ((reduce X).obj K)) =
      (reduce Y).map ((d.higher.integral.properIdentity f).hom.app K) ≫
        (direct d.higher hl o z f).app K := by
  -- Cancel an invertible comparison to compare maps between reduced integral objects.
  -- Finite evaluation is used only there, through reconstruction and joint faithfulness.
  let S := d.higher.integral
  let c : Compactification f.hom.left := .ofIsProper f.hom.left
  let M := (reduce X).obj K
  let q := (Operations.push C.l E o f.hom.left).map
    ((openIdentity o z X.obj.left).hom.app M)
  let s := supportReduction D C E d.higher hl o z f c K
  have hs : IsIso s :=
    (FixProjectionCompactification.integralSupportReductionNormalization
      D C E n hn d hl o z f).1 c K
  have hq : IsIso q := by dsimp only [q]; infer_instance
  let t := (reduce Y).map ((S.properIdentity f).hom.app K) ≫
    (direct d.higher hl o z f).app K
  change s ≫ q = t
  apply (cancel_mono (inv q ≫ inv s)).mp
  apply reduced_maps_ext d Y
  intro m
  suffices he : (evaluation (C := C) (E := E) m Y).map (s ≫ q) =
      (evaluation (C := C) (E := E) m Y).map t by
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun v ↦ v ≫ (evaluation (C := C) (E := E) m Y).map (inv q ≫ inv s)) he
  let F := stage d m
  let beta := d.integralNormalization.reduction m
  let I := finiteInclusion (C := C) (E := E) m Y
  let Kn := (reduction d m X).obj K
  let P := proEtaleConstantDerivedDirectImage f.hom.left
    (Padic.coefficientExtensionRing C.l E (m + 1))
  let bd := ((o.evaluation f.hom.left).evaluation m).app M ≪≫
    P.mapIso (reductionEvaluation d m X K)
  let bs := (supportEvaluation C.l E o c m).app M ≪≫
    (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).mapIso
      (reductionEvaluation d m X K)
  let j := (@sixFunctorProperCandidateIso
    (Padic.coefficientExtensionRing C.l E (m + 1)) _
    (Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m))
    X.obj.left Y.obj.left f.hom.left _).app Kn.obj
  have hq' : (evaluation (C := C) (E := E) m Y).map q ≫ bd.hom =
      bs.hom ≫ j.hom := by
    have h := proper_identity_evaluation o z f.hom.left m M
    have hn := (@sixFunctorProperCandidateIso
      (Padic.coefficientExtensionRing C.l E (m + 1)) _
      (Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m))
      X.obj.left Y.obj.left f.hom.left _).hom.naturality (reductionEvaluation d m X K).hom
    dsimp only [bd, bs, j, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    dsimp only [P]
    dsimp only [M, reduce, Functor.comp_obj, ObjectProperty.ι_obj] at hn ⊢
    erw [← Category.assoc, h, Category.assoc, ← hn]
    simp only [c, M, Kn, Functor.comp_obj, ObjectProperty.ι_obj,
      sixFunctorFiniteSupport, sfIntrinsicCompactSupport, sfAmbientCompactSupportCandidate,
      Category.assoc]
  have hs' := FixProjectionCompactification.integralSupportAdjunctFiniteCoordinates
    D C E n hn d hl o z f c K m
  have hd := direct_evaluation d m hl o z f K
  have hf := congrArg Iso.hom (F.finiteProperNormalization f Kn)
  have hc := congrArg (fun v ↦ I.map v) (beta.properIdentity f K)
  apply (cancel_mono bd.hom).mp
  simp only [Functor.map_comp, Category.assoc]
  erw [hq']
  have ht : (evaluation (C := C) (E := E) m Y).map t ≫ bd.hom =
      (evaluation (C := C) (E := E) m Y).map
          ((reduce Y).map ((S.properIdentity f).hom.app K)) ≫
        (evaluation (C := C) (E := E) m Y).map
          ((direct d.higher hl o z f).app K) ≫ bd.hom := by
    simp only [t, Functor.map_comp, Category.assoc]
  erw [ht]
  have hs'' : (evaluation (C := C) (E := E) m Y).map s ≫ bs.hom =
      (reductionEvaluation d m Y ((S.support f c).obj K)).hom ≫
        I.map ((beta.supportAdjunction f c).left.hom.app K) ≫
        (F.finiteSupport f c).hom.app Kn := hs'
  have hd' : (evaluation (C := C) (E := E) m Y).map
        ((direct d.higher hl o z f).app K) ≫ bd.hom =
      (reductionEvaluation d m Y ((S.direct f).obj K)).hom ≫
        I.map ((beta.directAdjunction f).right.hom.app K) ≫
        (F.finiteDirectImage f).hom.app Kn := hd
  erw [← Category.assoc, hs'', Category.assoc, Category.assoc, hd']
  have hn := ((calculus C.l E Y.obj.left).reductionEvaluation m).hom.naturality
    ((S.properIdentity f).hom.app K).hom
  change (evaluation (C := C) (E := E) m Y).map
      ((reduce Y).map ((S.properIdentity f).hom.app K)) ≫
      (reductionEvaluation d m Y ((S.direct f).obj K)).hom =
    (reductionEvaluation d m Y ((S.support f c).obj K)).hom ≫
      I.map ((reduction d m Y).map ((S.properIdentity f).hom.app K)) at hn
  erw [reassoc_of% hn]
  have hf' : I.map ((F.finite.properIdentity f).hom.app Kn) ≫
        (F.finiteDirectImage f).hom.app Kn = (F.finiteSupport f c).hom.app Kn ≫ j.hom := hf
  simp only [Functor.map_comp] at hc
  erw [reassoc_of% hc, hf']

end WeilConjectures.IntegralProjectionReduction
