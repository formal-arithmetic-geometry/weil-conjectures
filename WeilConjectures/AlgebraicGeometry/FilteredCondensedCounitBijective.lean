/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FilteredCondensedRepresentingPairData
import all WeilConjectures.AlgebraicGeometry.FilteredCondensedCounitFiniteFormula
import WeilConjectures.AlgebraicGeometry.SplitCoefficientDerivedFaithfulSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
attribute [local instance 2000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Mod.hasFunctorialFlatResolution
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

@[local instance]
private theorem extension_additive (T : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) :
    (constructibleToPadicAlgCl T l E).Additive := by
  have : IsCommMonObj (padicSubfieldRingObj T l E) :=
    isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) T
  have : IsCommMonObj (padicAlgClRingObj T l) :=
    isCommMonObj_condensedRingObj (Profinite.padicAlgClRingObj l) T
  have hi : derivedExtendScalarsToPadicAlgCl T l E ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T l E)).mapDerivedCategory :=
    Functor.leftDerivedFunctorIsoMapDerivedCategory _
  have : (derivedExtendScalarsToPadicAlgCl T l E).Additive :=
    Functor.additive_of_iso hi.symm
  unfold constructibleToPadicAlgCl
  infer_instance

private theorem finite_extension_injective (T : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) :
    ∀ {A B : PadicSubfieldConstructible T l E},
      Function.Injective ((constructibleToPadicAlgCl T l E).map (X := A) (Y := B)) := by
  intro A B a b hab
  have : (derivedExtendScalarsToPadicAlgCl T l E).Faithful :=
    faithful_leftDerivedExtendScalarsToPadicAlgCl T l E
  apply (boundedConstructible (padicSubfieldRingObj T l E)).ι.map_injective
  apply (derivedExtendScalarsToPadicAlgCl T l E).map_injective
  exact congrArg (·.hom) hab

attribute [local irreducible] constructibleExtendScalars constructibleToPadicAlgCl
  CondensedRing.boundedConstructibleLowerShriekOfCompactification
  CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification

set_option maxHeartbeats 2000000 in
-- Converting finite scalar representatives and their zero maps requires extra reduction.
private theorem counit_kernel_zero {s : ScalarComparisons l k c}
    (hs : s.IsCanonical l k c) {E : PadicAlgCl.FiniteIntermediateField l}
    (d : Pair l k c s E) (hd : d.IsCompatible l k c)
    (C : PadicAlgClConstructible X.left l) (u : C ⟶ d.omegaM l k c)
    (hu : (omegaSupport l k c).map u ≫ d.omegaCounit l k c = 0) : u = 0 := by
  obtain ⟨F, CF, ⟨e⟩⟩ := constructibleCocone_essSurjObj X.left l C
  dsimp only [constructibleCocone] at e
  obtain ⟨H, hF, hE, a, ha⟩ :=
    constructibleCocone_homSurj X.left l F E CF d.M (e.hom ≫ u)
  dsimp only [constructibleCocone] at a ha
  change e.hom ≫ u = (constructibleToPadicAlgClCompIso X.left l hF).inv.app CF ≫
    (constructibleToPadicAlgCl X.left l H).map a ≫
      (constructibleToPadicAlgClCompIso X.left l hE).hom.app d.M at ha
  let eH := (constructibleToPadicAlgClCompIso X.left l hF).app CF ≪≫ e
  have hu' : u = eH.inv ≫ (constructibleToPadicAlgCl X.left l H).map a ≫
      (constructibleToPadicAlgClCompIso X.left l hE).hom.app d.M := by
    apply (cancel_epi e.hom).1
    simpa only [eH, Iso.trans_inv, Iso.app_inv, Category.assoc, Iso.hom_inv_id_assoc] using ha
  have hz : (omegaSupport l k c).map
      ((constructibleToPadicAlgCl X.left l H).map a ≫
        (constructibleToPadicAlgClCompIso X.left l hE).hom.app d.M) ≫
      d.omegaCounit l k c = 0 := by
    have hrep : (constructibleToPadicAlgCl X.left l H).map a ≫
        (constructibleToPadicAlgClCompIso X.left l hE).hom.app d.M = eH.hom ≫ u := by
      rw [hu']
      simp only [Iso.hom_inv_id_assoc]
    rw [hrep, Functor.map_comp, Category.assoc, hu, comp_zero]
  rw [counit_finite_formula l k c hs d hd H hE _ a] at hz
  have hz' : (constructibleToPadicAlgCl Y.left l H).map
      (d.beta H hE _ a) = 0 := by
    apply (cancel_epi ((s.omega H).inv.app _)).1
    apply (cancel_mono ((constructibleToPadicAlgClCompIso Y.left l hE).hom.app d.L)).1
    simpa only [Category.assoc, comp_zero, zero_comp] using hz
  have hb : d.beta H hE _ a = 0 := by
    apply finite_extension_injective l Y.left H
    simpa only [Functor.map_zero] using hz'
  have hb0 : d.beta H hE ((constructibleExtendScalars X.left l hF).obj CF) 0 = 0 := by
    rw [hd H hE ((constructibleExtendScalars X.left l hF).obj CF) 0]
    simp only [Functor.map_zero, zero_comp]
  have ha0 : a = 0 := (d.beta H hE _).injective (hb.trans hb0.symm)
  rw [hu', ha0]
  simp only [Functor.map_zero, comp_zero, zero_comp]

private theorem inverse_chain {A : Type*} [Category A] {a b c d e : A}
    (p : a ≅ b) (q : b ≅ c) (r : c ≅ d) (s : a ≅ e) (t : e ≅ d)
    (h : p.hom ≫ q.hom ≫ r.hom = s.hom ≫ t.hom) :
    r.inv ≫ q.inv = t.inv ≫ s.inv ≫ p.hom := by
  calc
    r.inv ≫ q.inv = t.inv ≫ s.inv ≫ (s.hom ≫ t.hom) ≫ r.inv ≫ q.inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = t.inv ≫ s.inv ≫ (p.hom ≫ q.hom ≫ r.hom) ≫ r.inv ≫ q.inv := by rw [h]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

set_option maxHeartbeats 2000000 in
-- The scalar-comparison calculation converts several nested derived functor wrappers.
private theorem counit_surjective {s : ScalarComparisons l k c}
    (hs : s.IsCanonical l k c) {E : PadicAlgCl.FiniteIntermediateField l}
    (d : Pair l k c s E) (hd : d.IsCompatible l k c)
    (C : PadicAlgClConstructible X.left l) :
    Function.Surjective (fun u : C ⟶ d.omegaM l k c ↦
      (omegaSupport l k c).map u ≫ d.omegaCounit l k c) := by
  intro v
  obtain ⟨F, CF, ⟨e⟩⟩ := constructibleCocone_essSurjObj X.left l C
  dsimp only [constructibleCocone] at e
  let vF := (s.omega F).hom.app CF ≫ (omegaSupport l k c).map e.hom ≫ v
  obtain ⟨H, hF, hE, b, hb⟩ := constructibleCocone_homSurj Y.left l F E
    ((finiteSupport l k c F).obj CF) d.L vF
  dsimp only [constructibleCocone] at b hb
  change vF =
    (constructibleToPadicAlgClCompIso Y.left l hF).inv.app _ ≫
      (constructibleToPadicAlgCl Y.left l H).map b ≫
        (constructibleToPadicAlgClCompIso Y.left l hE).hom.app d.L at hb
  let CH := (constructibleExtendScalars X.left l hF).obj CF
  let b' := (s.finite hF).inv.app CF ≫ b
  let a := (d.beta H hE CH).symm b'
  have ha : d.beta H hE CH a = b' := (d.beta H hE CH).apply_symm_apply b'
  let u := e.inv ≫ (constructibleToPadicAlgClCompIso X.left l hF).inv.app CF ≫
    (constructibleToPadicAlgCl X.left l H).map a ≫
      (constructibleToPadicAlgClCompIso X.left l hE).hom.app d.M
  refine ⟨u, ?_⟩
  have hcoh : (omegaSupport l k c).map
        ((constructibleToPadicAlgClCompIso X.left l hF).inv.app CF) ≫
      (s.omega H).inv.app CH =
    (s.omega F).inv.app CF ≫
      (constructibleToPadicAlgClCompIso Y.left l hF).inv.app
        ((finiteSupport l k c F).obj CF) ≫
      (constructibleToPadicAlgCl Y.left l H).map ((s.finite hF).hom.app CF) :=
    inverse_chain
      ((constructibleToPadicAlgCl Y.left l H).mapIso ((s.finite hF).app CF))
      ((s.omega H).app CH)
      ((omegaSupport l k c).mapIso ((constructibleToPadicAlgClCompIso X.left l hF).app CF))
      ((constructibleToPadicAlgClCompIso Y.left l hF).app ((finiteSupport l k c F).obj CF))
      ((s.omega F).app CF) (scalar_coherence l k c hs hF CF)
  calc
    (omegaSupport l k c).map u ≫ d.omegaCounit l k c =
      (omegaSupport l k c).map e.inv ≫
        (omegaSupport l k c).map
          ((constructibleToPadicAlgClCompIso X.left l hF).inv.app CF) ≫
        ((omegaSupport l k c).map
          ((constructibleToPadicAlgCl X.left l H).map a ≫
            (constructibleToPadicAlgClCompIso X.left l hE).hom.app d.M) ≫
          d.omegaCounit l k c) := by
      simp only [u, Functor.map_comp, Category.assoc]
    _ = (omegaSupport l k c).map e.inv ≫
        (omegaSupport l k c).map
          ((constructibleToPadicAlgClCompIso X.left l hF).inv.app CF) ≫
        ((s.omega H).inv.app CH ≫
          (constructibleToPadicAlgCl Y.left l H).map b' ≫
            (constructibleToPadicAlgClCompIso Y.left l hE).hom.app d.L) := by
      rw [counit_finite_formula l k c hs d hd H hE CH a, ha]
    _ = (omegaSupport l k c).map e.inv ≫ (s.omega F).inv.app CF ≫
        (constructibleToPadicAlgClCompIso Y.left l hF).inv.app _ ≫
          (constructibleToPadicAlgCl Y.left l H).map b ≫
            (constructibleToPadicAlgClCompIso Y.left l hE).hom.app d.L := by
      rw [reassoc_of% hcoh]
      simp only [b', Functor.map_comp, Category.assoc]
      rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      erw [(constructibleToPadicAlgCl Y.left l H).map_id, Category.id_comp]
    _ = (omegaSupport l k c).map e.inv ≫ (s.omega F).inv.app CF ≫ vF := by
      rw [hb]
    _ = v := by
      simp only [vF, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
      erw [(omegaSupport l k c).map_id, Category.id_comp]

/-- Finite representing bijections make the global extended-counit map bijective.
Source: blueprint/latest, sec-smooth-purity/sk-thm-sp-qbar, filtered Hom display
and descent of morphisms and relations; parent proof Steps 1 and 4.
(blueprint: lem-pur-filtered-condensed-counit-bijective).

Proof: finite type over a field makes X and Y Noetherian. Model the test object
at a finite field. For surjectivity, transport the target arrow through the scalar
comparison and descend it to a common finite overfield H. The inverse finite
comparison identifies its source with the support of the extended test object.
Take its inverse under the supplied beta at H, extend, and transport back along
the test-object model. The finite counit formula and scalar-comparison coherence
show that its image is the original arrow.
For injectivity, descend an arrow in the kernel to a finite stage. The finite
formula identifies its counit image with the scalar extension of its finite beta
image. Faithfulness of scalar extension gives a zero beta image. Compatibility
makes beta preserve zero, so beta injectivity gives a zero representative and
hence a zero original arrow. Apply this to the difference of two arrows, using
additivity of the support functor. All choices occur only in the proof. The same
argument covers zero objects and the empty scheme. -/
theorem counit_map_bijective {s : ScalarComparisons l k c}
    (hs : s.IsCanonical l k c) {E : PadicAlgCl.FiniteIntermediateField l}
    (d : Pair l k c s E) (hd : d.IsCompatible l k c)
    (C : PadicAlgClConstructible X.left l) :
    Function.Bijective (fun u : C ⟶ d.omegaM l k c ↦
      (omegaSupport l k c).map u ≫ d.omegaCounit l k c) := by
  refine ⟨?_, counit_surjective l k c hs d hd C⟩
  intro a b hab
  dsimp only at hab
  apply sub_eq_zero.mp
  apply counit_kernel_zero l k c hs d hd C (a - b)
  rw [Functor.map_sub, Preadditive.sub_comp, hab, sub_self]

end WeilConjectures.FilteredCondensedRepresentingPair
