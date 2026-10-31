/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Encoding.IntegralPresentationEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Transition compatibility for normalized integral comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionDerivedExtension scalarReductionExtension scalarReductionCounit
  normalizedDVRResCompletedComp normalizedDVRKFlatComparison
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Unit-normalized comparisons preserve adjoint quotient transitions. -/
private theorem adjointTransitionComparison
    {C A B C' A' B' : Type*}
    [Category C] [Category A] [Category B]
    [Category C'] [Category A'] [Category B']
    {L : C ⥤ A} {U : A ⥤ C} {N : C ⥤ B} {W : B ⥤ C}
    {L' : C' ⥤ A'} {R : A' ⥤ C'} {N' : C' ⥤ B'} {S : B' ⥤ C'}
    (al : L ⊣ U) (an : N ⊣ W) (ar : L' ⊣ R) (as' : N' ⊣ S)
    (V : B ⥤ A) (T : B' ⥤ A') (F : C ⥤ C') (G : A ⥤ A') (H : B ⥤ B')
    (a : U ⋙ F ≅ G ⋙ R) (b : W ⋙ F ≅ H ⋙ S)
    (e : V ⋙ G ≅ H ⋙ T) (c : V ⋙ U ≅ W) (d : T ⋙ R ≅ S)
    (hsq : ∀ Z, F.map (c.hom.app Z) ≫ b.hom.app Z =
      a.hom.app (V.obj Z) ≫ R.map (e.hom.app Z) ≫ d.hom.app (H.obj Z))
    (K : C) (bm : L'.obj (F.obj K) ≅ G.obj (L.obj K))
    (bn : N'.obj (F.obj K) ≅ H.obj (N.obj K))
    (hm : ar.unit.app (F.obj K) ≫ R.map bm.hom ≫ a.inv.app (L.obj K) =
      F.map (al.unit.app K))
    (hn : as'.unit.app (F.obj K) ≫ S.map bn.hom ≫ b.inv.app (N.obj K) =
      F.map (an.unit.app K))
    (v : L.obj K ⟶ V.obj (N.obj K))
    (hv : al.unit.app K ≫ U.map v ≫ c.hom.app (N.obj K) = an.unit.app K) :
    R.map ((ar.homEquiv (F.obj K) (T.obj (N'.obj (F.obj K)))).symm
        (as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)))) ≫
        d.hom.app (N'.obj (F.obj K)) ≫ S.map bn.hom ≫ b.inv.app (N.obj K) =
      R.map bm.hom ≫ a.inv.app (L.obj K) ≫
        F.map (U.map v ≫ c.hom.app (N.obj K)) := by
  have hm' : ar.unit.app (F.obj K) ≫ R.map bm.hom =
      F.map (al.unit.app K) ≫ a.hom.app (L.obj K) := by
    have h := congrArg (fun k ↦ k ≫ a.hom.app (L.obj K)) hm
    simp only [Category.assoc, Iso.inv_hom_id_app] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  have hn' : as'.unit.app (F.obj K) ≫ S.map bn.hom =
      F.map (an.unit.app K) ≫ b.hom.app (N.obj K) := by
    have h := congrArg (fun k ↦ k ≫ b.hom.app (N.obj K)) hn
    simp only [Category.assoc, Iso.inv_hom_id_app] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  let t := (ar.homEquiv (F.obj K) (T.obj (N'.obj (F.obj K)))).symm
    (as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)))
  have ht : bm.hom ≫ G.map v ≫ e.hom.app (N.obj K) = t ≫ T.map bn.hom := by
    apply (ar.homEquiv _ _).injective
    simp only [ar.homEquiv_unit, R.map_comp]
    have htu : ar.unit.app (F.obj K) ≫ R.map t =
        as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)) :=
      (ar.homEquiv_unit _ _ t).symm.trans ((ar.homEquiv _ _).apply_symm_apply _)
    rw [reassoc_of% htu]
    apply (cancel_mono (d.hom.app (H.obj (N.obj K)))).1
    rw [reassoc_of% hm']
    have ha := a.hom.naturality v
    dsimp only [Functor.comp_map] at ha
    simp only [Category.assoc]
    rw [← reassoc_of% ha, ← hsq]
    have hd := d.hom.naturality bn.hom
    dsimp only [Functor.comp_map] at hd
    rw [hd]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [hn', ← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, hv]
  have hc : a.inv.app (V.obj (N.obj K)) ≫ F.map (c.hom.app (N.obj K)) =
      R.map (e.hom.app (N.obj K)) ≫ d.hom.app (H.obj (N.obj K)) ≫
        b.inv.app (N.obj K) := by
    have h := congrArg
      (fun k ↦ a.inv.app (V.obj (N.obj K)) ≫ k ≫ b.inv.app (N.obj K))
      (hsq (N.obj K))
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  have ha := a.inv.naturality v
  dsimp only [Functor.comp_map] at ha
  change R.map t ≫ d.hom.app (N'.obj (F.obj K)) ≫ S.map bn.hom ≫
      b.inv.app (N.obj K) = _
  rw [F.map_comp]
  rw [← reassoc_of% ha]
  rw [hc, ← R.map_comp_assoc, ← R.map_comp_assoc]
  simp only [Category.assoc]
  rw [ht, R.map_comp]
  have hd := d.hom.naturality bn.hom
  dsimp only [Functor.comp_map] at hd
  rw [Category.assoc, reassoc_of% hd]

/-- Locally surjective scalar restriction is full on sheaf modules. -/
private theorem restrictionFull
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat} (f : R ⟶ S)
    [Presheaf.IsLocallySurjective J f.hom] :
    (SheafOfModules.restrictScalars f).Full where
  map_surjective {M N} g := by
    let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (J := J) (M₁ := M.val) f.hom N.isSheaf
    refine ⟨⟨e.symm g.val⟩, ?_⟩
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply g.val

/-- The completed coefficient projections have full ordinary restriction. -/
private theorem scalarRestrictionFull (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E X n).Full := by
  let f := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)
  let : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) f.hom :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (projection_surjective l E X _ (uniformizer_normalized l E X n))
  exact restrictionFull f

private def testDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

private theorem existsTestDatum (l : ℕ) : ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  by_cases h : l = 2
  · exact ⟨testDatum 3 (by decide), by simp [testDatum, h]⟩
  · exact ⟨testDatum 2 (by decide), h⟩

/-- The restricted adjoint of the smaller reduction unit. -/
private def adjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (T : B ⥤ A) (d : T ⋙ Rm ≅ Rn) :
    Lm ⋙ Rm ⟶ Ln ⋙ Rn where
  app M := Rm.map ((am.homEquiv M (T.obj (Ln.obj M))).symm
      (an.unit.app M ≫ d.inv.app (Ln.obj M))) ≫ d.hom.app (Ln.obj M)
  naturality {M N} f := by
    have h : Lm.map f ≫
        (am.homEquiv N (T.obj (Ln.obj N))).symm
          (an.unit.app N ≫ d.inv.app (Ln.obj N)) =
        (am.homEquiv M (T.obj (Ln.obj M))).symm
          (an.unit.app M ≫ d.inv.app (Ln.obj M)) ≫ T.map (Ln.map f) := by
      apply (am.homEquiv _ _).injective
      rw [am.homEquiv_naturality_left, Equiv.apply_symm_apply,
        am.homEquiv_naturality_right, Equiv.apply_symm_apply]
      dsimp only [Functor.comp_obj, Functor.comp_map]
      have hu := an.unit.naturality f
      dsimp only [Functor.id_map, Functor.comp_map] at hu
      rw [reassoc_of% hu]
      simpa only [Category.assoc, Functor.comp_map] using
        congrArg (fun k ↦ an.unit.app M ≫ k) (d.inv.naturality (Ln.map f))
    dsimp only [Functor.comp_map]
    rw [← Rm.map_comp_assoc, h, Rm.map_comp, Category.assoc]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun k ↦ Rm.map ((am.homEquiv M (T.obj (Ln.obj M))).symm
        (an.unit.app M ≫ d.inv.app (Ln.obj M))) ≫ k)
      (d.hom.naturality (Ln.map f))

private theorem normalizeRepresentativeTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (T : B ⥤ A) (d : T ⋙ Rm ≅ Rn)
    (P V W : C) (cm : Rm.obj (Lm.obj P) ⟶ V) (cn : Rn.obj (Ln.obj P) ⟶ W)
    (f : V ⟶ W)
    (h : Rm.map ((am.homEquiv P (T.obj (Ln.obj P))).symm
        (an.unit.app P ≫ d.inv.app (Ln.obj P))) ≫ d.hom.app (Ln.obj P) ≫
        Rn.map (Ln.map (Iso.refl P).inv) ≫ cn =
      Rm.map (Lm.map (Iso.refl P).inv) ≫ cm ≫ f) :
    (adjointTransition am an T d).app P ≫ cn = cm ≫ f := by
  simpa [adjointTransition] using h

attribute [local irreducible] Functor.mapDerivedCategory

private theorem sectionTransitionAdjoint
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    sfDerivedReductionTransition l E X n =
      adjointTransition
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
        (normalizedDVRRes.{u, u} l E X n.le_succ)
        (normalizedDVRResCompletedComp.{0, u, u} l E X D hl n.le_succ) := by
  apply (sfDerivedReductionTransition_existsUnique l E X n).unique
    (sfDerivedReductionTransition_existsUnique l E X n).exists.choose_spec
  intro P hP
  have h := normalizedDVR_kflat_transition.{0, u, u} l E X D hl P hP
    (DerivedCategory.Q.obj P) (Iso.refl _) n
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (normalizedDVRKFlatUnit.{0, u, u} l E X D hl (n + 1) P hP)
    (normalizedDVRKFlatUnit.{0, u, u} l E X D hl n P hP)
  have h' := normalizeRepresentativeTransition
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (normalizedDVRRes.{u, u} l E X n.le_succ)
    (normalizedDVRResCompletedComp.{0, u, u} l E X D hl n.le_succ)
    (DerivedCategory.Q.obj P) _ _
    (normalizedDVRKFlatComparison.{u, u} l E X (n + 1) P)
    (normalizedDVRKFlatComparison.{u, u} l E X n P)
    (DerivedCategory.Q.map (integralTowerTransition l E X D hl P n)) h
  have hf := congrArg (fun f ↦ DerivedCategory.Q.map f)
    (transition_eq l E X D hl P n)
  simpa only [normalizedDVRKFlatComparison, sfReductionRepresentativeComparison] using
    h'.trans (congrArg
      (fun f ↦ normalizedDVRKFlatComparison.{u, u} l E X (n + 1) P ≫ f) hf)

section RestrictionCompositor
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

/-- Ordinary restriction compositor coming from the limit projection equation. -/
private noncomputable def normalizedDVRTransitionRestriction
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    normalizedDVRModuleRes l E X n.le_succ ⋙
      scalarReductionRestriction.{u, u} l E X (n + 1) ≅
        scalarReductionRestriction.{u, u} l E X n := by
  let e₀ := normalizedDVRRestrictionCompIso
    (completedIntegralCoefficientProjection l E X D hl (n + 1))
    (normalizedDVRQuotient l E X n.le_succ)
  let he : completedIntegralCoefficientProjection l E X D hl (n + 1) ≫
      normalizedDVRQuotient l E X n.le_succ =
        completedIntegralCoefficientProjection l E X D hl n := by
    exact limit.w (integralCoefficientSheafSystem l E X) (homOfLE n.le_succ).op
  exact e₀ ≪≫ eqToIso (congrArg
    (fun f : completedIntegralCoefficientSheaf l E X D hl ⟶
        integralCoefficientSheaf l E X n ↦ SheafOfModules.restrictScalars.{u + 1} f) he)

/-- Localization of the ordinary compositor is the specified tower compositor. -/
private theorem normalizedDVRTransitionRestriction_comp
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    (Functor.mapDerivedCategoryCompIso
      (normalizedDVRModuleRes l E X n.le_succ)
      (scalarReductionRestriction.{u, u} l E X (n + 1))).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (normalizedDVRTransitionRestriction l E X D hl n) =
      normalizedDVRResCompletedComp l E X D hl n.le_succ := by
  unfold normalizedDVRResCompletedComp
  rfl
end RestrictionCompositor

end AlgebraicGeometry.ProEtale.IntegralPresentation
