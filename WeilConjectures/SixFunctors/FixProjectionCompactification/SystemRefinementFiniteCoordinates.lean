/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionCounit
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteRefinementAmbientNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteCompositorCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateCoordinates

/-! # One finite evaluation of the directed system refinement

Source: Stacks 0F7B and 0F7J; compactification independence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived

open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection
open CompactSupportFiniteProjection

attribute [local implicit_reducible] sixFunctorFiniteRealization
attribute [local irreducible] ProEtale.derivedTensor derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarComp properOpenMate

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus
  sfIntrinsicExtensionByZero coefficientSequenceLimit
  Functor.mapDerivedCategory Functor.rightDerivedFunctor DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions
  AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection.finiteComparison
  IntegralSystemRealization.RefinementProjection.systemComparison
  FiniteCoordinates.push FiniteCoordinates.shriek FiniteCoordinates.fixedPush
  FiniteCoordinates.fixedShriek FiniteCoordinates.support

private abbrev realization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (X : SixFunctorSpace D) := sixFunctorFiniteRealization D C E n hn X

private def supportRealization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    ((S.finite.support f c).obj K).obj ≅
      (realization (C := C) (E := E) (n := n) (hn := hn) Y).functor.obj
        ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
          ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (S.finiteSupport f c).app K ≪≫
    (sixFunctorFiniteSupport D C E n hn f c).mapIso
      ((realization (C := C) (E := E) (n := n) (hn := hn) X).counitIso.app K.obj).symm ≪≫
    (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) c).app
      ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)

private theorem witness_support_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ≌ B) (V : C ⥤ D) (U : B ⥤ D) (F : A ⥤ C)
    (α : R.functor ⋙ U ≅ F ⋙ V) {K : B} {H : A}
    (e : H ≅ R.inverse.obj K) {a : D} (b : a ≅ U.obj K) :
    (b ≪≫ U.mapIso (R.functor.mapIso e ≪≫ R.counitIso.app K).symm ≪≫ α.app H).hom ≫
        V.map (F.map e.hom) =
      (b ≪≫ U.mapIso (R.counitIso.app K).symm ≪≫ α.app (R.inverse.obj K)).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.map_comp, Category.assoc]
  congr 1
  have hn : U.map (R.functor.map e.hom) ≫ α.hom.app (R.inverse.obj K) =
      α.hom.app H ≫ V.map (F.map e.hom) := α.hom.naturality e.hom
  rw [← hn]
  simp only [← U.map_comp_assoc, ← R.functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem retained_origin
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (X : SixFunctorSpace D) (K : sixFunctorFiniteCategory D C E n hn X) :
    ∃ O : ProEtale.RefinementFiniteLevelOrigin C.l E n hn X.obj.left,
      Nonempty (ProEtale.refinementFiniteLevelFixedObject C.l E n hn X.obj.left O ≅
        (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj) := by
  classical
  let A := Padic.coefficientExtensionRing C.l E n
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) X
  let U := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left
  obtain ⟨a, ha⟩ := K.property.1.bddBelow
  obtain ⟨b, hb⟩ := K.property.1.bddAbove
  have hv : ∀ i : ℤ, (i < min a b ∨ b < i) →
      CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin X.obj.left A).2.2.1
    K.obj).mpr ⟨K.property.2, min a b, b, min_le_right _ _, hv⟩
  obtain ⟨c, d, _, hvan⟩ := L.property.2
  let LP : DerivedCategory.Plus
      (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
    ⟨L.obj, ⟨c, (DerivedCategory.isGE_iff L.obj c).2
      (fun i hi ↦ hvan i (Or.inl hi))⟩⟩
  let : TopologicalSpace (ULift.{u + 1} A) := ⊥
  let := discreteTopology_bot (ULift.{u + 1} A)
  let O : ProEtale.RefinementFiniteLevelOrigin C.l E n hn X.obj.left :=
    ⟨(ProEtale.finiteCoefficientComparison X.obj.left
      (ULift.{u + 1} A)).mapDerivedCategoryPlus.obj LP, ⟨LP, Iso.refl _⟩⟩
  have e : U.mapDerivedCategory.obj L.obj ≅ R.inverse.obj K.obj := by
    apply R.functor.preimageIso
    exact ((Functor.mapDerivedCategoryCompIso U
      (sfIntrinsicModuleEquivalence X.obj.left A).functor).app L.obj).symm ≪≫
        eL ≪≫ (R.counitIso.app K.obj).symm
  exact ⟨O, ⟨(ProEtale.refinementFixedWitnessIso X.obj.left
    (ULift.{u + 1} A) O).symm ≪≫ e⟩⟩

private theorem finiteComparison_naturality
    (D : FiniteFieldDatum.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : SixFunctorSpace D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c d : Compactification f.hom.left} (r : c.Refinement d)
    {K L : ProEtale.ProperOpenDerived A X.obj.left} (a : K ⟶ L) :
    (ProEtale.ProperOpenPush A d.g).map ((ProEtale.ProperOpenShriek A d.i).map a) ≫
        RefinementProjection.finiteComparison D A r L =
      RefinementProjection.finiteComparison D A r K ≫
        (ProEtale.ProperOpenPush A c.g).map ((ProEtale.ProperOpenShriek A c.i).map a) := by
  let := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let Jc := ProEtale.ProperOpenShriek A c.i
  let Jd := ProEtale.ProperOpenShriek A d.i
  let Sr := ProEtale.ProperOpenPush A r.hom
  let Sd := ProEtale.ProperOpenPush A d.g
  let β := identityNormalize Jc Jd ((ordinary D A).S (𝟙 X)) Sr
    ((ordinary D A).sId X).inv
    (ProEtale.properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
      (r.i_hom.trans (Category.id_comp _).symm))
  let κ := Functor.whiskerRight β Sd ≫
    Functor.whiskerLeft Jc
      ((conjugateIsoEquiv
        ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) d.g).comp
          (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom))
        (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (r.hom ≫ d.g))
        (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom d.g)).hom) ≫
    Functor.whiskerLeft Jc (indexIso (ProEtale.ProperOpenPush A) r.hom_g).hom
  have h := κ.naturality a
  dsimp only [κ, β, identityNormalize, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map] at h
  simp only [Category.assoc] at h
  simpa only [RefinementProjection.finiteComparison, Category.assoc] using h

private theorem reverse_iso_square
    {A : Type*} [Category A] {a b c d : A}
    (ρ : a ≅ b) (s : a ≅ c) (t : b ≅ d) (m : c ≅ d)
    (h : ρ ≪≫ t = s ≪≫ m) : ρ.inv ≫ s.hom = t.hom ≫ m.inv := by
  apply (cancel_epi ρ.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hh := congrArg (fun e ↦ e.hom ≫ m.inv) h
  simpa only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm

private theorem mapped_square_transport
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {a b : B} {c d c' d' : A}
    (q : b ⟶ a) (s : a ⟶ R.obj c) (t : b ⟶ R.obj d)
    (k : d ⟶ c) (u : c ⟶ c') (v : d ⟶ d') (k' : d' ⟶ c')
    (h : q ≫ s = t ≫ R.map k) (hn : k ≫ u = v ≫ k') :
    q ≫ (s ≫ R.map u) = (t ≫ R.map v) ≫ R.map k' := by
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← R.map_comp]
  rw [hn]

private theorem support_refinement
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn) (hl : IsUnit (C.l : D.k))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    let := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        ((S.finite.comparison f c d).inv.app K) ≫ (supportRealization S f c K).hom =
      (supportRealization S f d K).hom ≫
        RY.functor.map (RefinementProjection.finiteComparison D A r (RX.inverse.obj K.obj)) := by
  classical
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) d
  obtain ⟨O, ⟨e⟩⟩ := retained_origin X K
  let w := RX.functor.mapIso e ≪≫ RX.counitIso.app K.obj
  let Wc := sixFunctorFiniteWitnessSupport C E n hn f c (S.finite.support f c)
    (S.finiteSupport f c) K O w
  let Wd := sixFunctorFiniteWitnessSupport C E n hn f d (S.finite.support f d)
    (S.finiteSupport f d) K O w
  have hc : Wc.hom ≫ RY.functor.map (F.map e.hom) =
      (supportRealization S f c K).hom := by
    exact witness_support_transport RX RY.functor (sixFunctorFiniteSupport D C E n hn f c)
      F (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) c)
      e ((S.finiteSupport f c).app K)
  have hd : Wd.hom ≫ RY.functor.map (G.map e.hom) =
      (supportRealization S f d K).hom := by
    exact witness_support_transport RX RY.functor (sixFunctorFiniteSupport D C E n hn f d)
      G (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) d)
      e ((S.finiteSupport f d).app K)
  have h := reverse_iso_square (I.mapIso ((S.finite.comparison f c d).app K)) Wc Wd
    (RY.functor.mapIso (sixFunctorFiniteRefinementComparison C E n hn f
      hl r O))
    (S.finiteRefinementNormalization f hl c d r K O w)
  have hm : (sixFunctorFiniteRefinementComparison C E n hn f
      hl r O).inv =
      RefinementProjection.finiteComparison D A r
        (ProEtale.refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) := by
    let : TopologicalSpace A := ⊥
    let := discreteTopology_bot A
    exact refinementComparisonAtWitness_inv_eq D A r O
  dsimp only [Functor.mapIso_inv, Iso.app_inv] at h
  rw [hm] at h
  rw [← hc, ← hd]
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← RY.functor.map_comp]
  simpa only [F, G, sfFixedCompactSupport, Functor.map_comp, Functor.comp_map,
    Category.assoc] using
    congrArg (Wd.hom ≫ ·) (congrArg RY.functor.map
      (finiteComparison_naturality D A r e.hom).symm)

attribute [local irreducible] sfIntrinsicDerivedEquivalence

private theorem cancel_fixed_presentation
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {X Y : B} {x y z : A} (a : X ≅ R.functor.obj x) (b : Y ≅ R.functor.obj y)
    (p : X ⟶ Y) (q : y ≅ z) (k : x ⟶ z)
    (h : p ≫ b.hom ≫ R.functor.map q.hom = a.hom ≫ R.functor.map k) :
    R.inverse.map p ≫
        (R.inverse.map b.hom ≫ (R.unitIso.app y).inv) ≫ q.hom =
      (R.inverse.map a.hom ≫ (R.unitIso.app x).inv) ≫ k := by
  have h' := FiniteCoordinates.fixed_square R a (b ≪≫ R.functor.mapIso q) p k h
  have hn := R.unitIso.inv.naturality q.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Iso.app_inv, Category.assoc] at h' ⊢
  rw [hn] at h'
  exact h'

private theorem fixed_compositor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (c : Compositors l E o) (m : ℕ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : X ⟶ Z)
    (h : f ≫ g = t) (M : System l E X) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    let RZ := sfIntrinsicDerivedEquivalence Z (Padic.coefficientExtensionRing l E (m + 1))
    RZ.inverse.map ((coefficientSequenceDerivedEvaluation l E Z m).map
        ((c.pushComp l E f g).hom.app M ≫
          (eqToIso (congrArg (Operations.push l E o) h)).hom.app M)) ≫
      (FiniteCoordinates.fixedPush l E o m t M).hom =
    (FiniteCoordinates.fixedPush l E o m g ((Operations.push l E o f).obj M)).hom ≫
      (ProperOpenPush A g).map (FiniteCoordinates.fixedPush l E o m f M).hom ≫
      (conjugateIsoEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g)).hom.app
          (FiniteCoordinates.input l E m X M) ≫
        (indexIso (ProperOpenPush A) h).hom.app (FiniteCoordinates.input l E m X M) := by
  let RZ := sfIntrinsicDerivedEquivalence Z (Padic.coefficientExtensionRing l E (m + 1))
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
  let k := (conjugateIsoEquiv
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g)).hom.app
      (FiniteCoordinates.input l E m X M) ≫
    (indexIso (ProperOpenPush A) h).hom.app (FiniteCoordinates.input l E m X M)
  have hh := FiniteCoordinates.compositor l E o c m f g t h M
  have h' := FiniteCoordinates.fixed_square RZ
    (FiniteCoordinates.push l E o m g ((Operations.push l E o f).obj M))
    (FiniteCoordinates.push l E o m t M)
    ((coefficientSequenceDerivedEvaluation l E Z m).map
      ((c.pushComp l E f g).hom.app M ≫
        (eqToIso (congrArg (Operations.push l E o) h)).hom.app M))
    ((ProperOpenPush A g).map (FiniteCoordinates.fixedPush l E o m f M).hom ≫ k)
    (by simpa only [RZ, A, k, Functor.map_comp, Category.assoc] using hh)
  simpa only [FiniteCoordinates.fixedPush, RZ, A, k, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.symm_hom, Iso.app_hom, Category.assoc] using h'

private theorem fixed_refinement_mate
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (z : Realizations l E D o) (m : ℕ)
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (M : System l E X.obj.left) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    let RW := sfIntrinsicDerivedEquivalence d.Z (Padic.coefficientExtensionRing l E (m + 1))
    haveI := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
    haveI := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
    RW.inverse.map ((coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.shriek l E o d.i).map
          ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
            SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
              X.obj.left).inv.app M) ≫
          (z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
            (r.i_hom.trans (Category.id_comp _).symm)).app M)) ≫
      (FiniteCoordinates.fixedPush l E o m r.hom
        ((Operations.shriek l E o c.i).obj M)).hom ≫
      (ProperOpenPush A r.hom).map (FiniteCoordinates.fixedShriek l E o m c.i M).hom =
    (FiniteCoordinates.fixedShriek l E o m d.i M).hom ≫
      (ProperOpenShriek A d.i).map
        (((ordinary D A).sId X).inv.app (FiniteCoordinates.input l E m X.obj.left M)) ≫
      (properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
        (r.i_hom.trans (Category.id_comp _).symm)).app
          (FiniteCoordinates.input l E m X.obj.left M) := by
  have := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  have := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  simpa only [FiniteCoordinates.fixedPush, FiniteCoordinates.fixedShriek,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc] using
    cancel_fixed_presentation _ (FiniteCoordinates.shriek l E o m d.i M)
    (FiniteCoordinates.push l E o m r.hom ((Operations.shriek l E o c.i).obj M)) _
    ((ProperOpenPush _ r.hom).mapIso (FiniteCoordinates.fixedShriek l E o m c.i M)) _
    (FiniteCoordinates.refinementMate l E D o z m c d r M)

private theorem paste_refinement
    {C W Z : Type*} [Category C] [Category W] [Category Z]
    (S : W ⥤ Z) (R : C ⥤ W) (T : C ⥤ Z) (μ : R ⋙ S ≅ T)
    {c₁ c₂ : C} {w₁ w₂ w₃ : W} {z₁ z₂ z₃ : Z}
    (u : z₁ ⟶ z₂) (b : z₂ ⟶ z₃) (pc : z₃ ⟶ T.obj c₁)
    (pdr : z₂ ⟶ S.obj w₂) (pd : z₁ ⟶ S.obj w₁)
    (pr : w₂ ⟶ R.obj c₁) (bc : c₁ ⟶ c₂) (bd : w₁ ⟶ w₃)
    (γ : w₃ ⟶ R.obj c₂) (a : w₁ ⟶ w₂)
    (hb : b ≫ pc = pdr ≫ S.map pr ≫ μ.hom.app c₁)
    (ha : a ≫ pr ≫ R.map bc = bd ≫ γ)
    (hn : u ≫ pdr = pd ≫ S.map a) :
    (u ≫ b) ≫ pc ≫ T.map bc =
      (pd ≫ S.map bd) ≫ (S.map γ ≫ μ.hom.app c₂) := by
  have hm := μ.hom.naturality bc
  dsimp only [Functor.comp_map] at hm
  calc
    _ = u ≫ (b ≫ pc) ≫ T.map bc := by simp only [Category.assoc]
    _ = u ≫ pdr ≫ S.map pr ≫ μ.hom.app c₁ ≫ T.map bc := by
      rw [hb]; simp only [Category.assoc]
    _ = pd ≫ S.map a ≫ S.map pr ≫ S.map (R.map bc) ≫ μ.hom.app c₂ := by
      rw [← Category.assoc, hn]
      simp only [Category.assoc]
      rw [← hm]
    _ = pd ≫ S.map (a ≫ pr ≫ R.map bc) ≫ μ.hom.app c₂ := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [ha]; simp only [Functor.map_comp, Category.assoc]

private theorem realize_square
    {C B : Type*} [Category C] [Category B] (R : C ≌ B)
    {X Y : B} {c d : C} (p : X ⟶ Y)
    (a : R.inverse.obj Y ⟶ c) (b : R.inverse.obj X ⟶ d) (k : d ⟶ c)
    (h : R.inverse.map p ≫ a = b ≫ k) :
    p ≫ ((R.counitIso.app Y).inv ≫ R.functor.map a) =
      ((R.counitIso.app X).inv ≫ R.functor.map b) ≫ R.functor.map k := by
  have hn := R.counitIso.inv.naturality p
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Iso.app_inv]
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← R.functor.map_comp, h]

private theorem system_support_square
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (z : Realizations l E D o) (m : ℕ)
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (M : System l E X.obj.left) :
    let A := Padic.coefficientExtensionRing l E (m + 1)
    (coefficientSequenceDerivedEvaluation l E Y.obj.left m).map
        (RefinementProjection.systemComparison l E D o z r M) ≫
      (FiniteCoordinates.support l E o m c M).hom =
    (FiniteCoordinates.support l E o m d M).hom ≫
      (sfIntrinsicDerivedEquivalence Y.obj.left A).functor.map
        (RefinementProjection.finiteComparison D (ULift.{u + 1} A) r
          (FiniteCoordinates.input l E m X.obj.left M)) := by
  have := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  have := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let B := ULift.{u + 1} A
  let RY := sfIntrinsicDerivedEquivalence Y.obj.left A
  let RW := sfIntrinsicDerivedEquivalence d.Z A
  let evY := coefficientSequenceDerivedEvaluation l E Y.obj.left m ⋙ RY.inverse
  let evW := coefficientSequenceDerivedEvaluation l E d.Z m ⋙ RW.inverse
  let U := (Operations.shriek l E o c.i).obj M
  let V := (Operations.shriek l E o d.i).obj M
  let T := FiniteCoordinates.input l E m X.obj.left M
  let a : V ⟶ (Operations.push l E o r.hom).obj U :=
    (Operations.shriek l E o d.i).map
      ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
        SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
          X.obj.left).inv.app M) ≫
      (z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
        (r.i_hom.trans (Category.id_comp _).symm)).app M
  let b := (z.compositors.pushComp l E r.hom d.g).hom.app U ≫
    (eqToIso (congrArg (Operations.push l E o) r.hom_g)).hom.app U
  let μ : ProperOpenPush B r.hom ⋙ ProperOpenPush B d.g ≅ ProperOpenPush B c.g :=
    conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) d.g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) (r.hom ≫ d.g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) r.hom d.g) ≪≫
      indexIso (ProperOpenPush B) r.hom_g
  let bc := FiniteCoordinates.fixedShriek l E o m c.i M
  let bd := FiniteCoordinates.fixedShriek l E o m d.i M
  let pc := FiniteCoordinates.fixedPush l E o m c.g U
  let pd := FiniteCoordinates.fixedPush l E o m d.g V
  let pr := FiniteCoordinates.fixedPush l E o m r.hom U
  let pdr := FiniteCoordinates.fixedPush l E o m d.g
    ((Operations.push l E o r.hom).obj U)
  let γ := (ProperOpenShriek B d.i).map (((ordinary D B).sId X).inv.app T) ≫
    (properOpenMate B c.i (𝟙 X.obj.left) r.hom d.i
      (r.i_hom.trans (Category.id_comp _).symm)).app T
  have hb : evY.map b ≫ pc.hom =
      pdr.hom ≫ (ProperOpenPush B d.g).map pr.hom ≫ μ.hom.app _ :=
    fixed_compositor l E o z.compositors m r.hom d.g c.g r.hom_g U
  have ha : evW.map a ≫ pr.hom ≫ (ProperOpenPush B r.hom).map bc.hom =
      bd.hom ≫ γ := fixed_refinement_mate D l E o z m c d r M
  have hn : evY.map ((Operations.push l E o d.g).map a) ≫ pdr.hom =
      pd.hom ≫ (ProperOpenPush B d.g).map (evW.map a) :=
    FiniteCoordinates.fixedPush_naturality l E o m d.g a
  have hk : RefinementProjection.finiteComparison D B r T =
      (ProperOpenPush B d.g).map γ ≫ μ.hom.app
        ((ProperOpenShriek B c.i).obj T) := by
    simp only [RefinementProjection.finiteComparison, γ, μ,
      Functor.map_comp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  have hp := paste_refinement (ProperOpenPush B d.g) (ProperOpenPush B r.hom)
    (ProperOpenPush B c.g) μ (evY.map ((Operations.push l E o d.g).map a))
    (evY.map b) pc.hom pdr.hom pd.hom pr.hom bc.hom bd.hom γ (evW.map a) hb ha hn
  have hsc : RefinementProjection.systemComparison l E D o z r M =
      (Operations.push l E o d.g).map a ≫ b := by
    simp only [RefinementProjection.systemComparison, a, b, U]
  have hfixed : evY.map (RefinementProjection.systemComparison l E D o z r M) ≫
      (pc.hom ≫ (ProperOpenPush B c.g).map bc.hom) =
    (pd.hom ≫ (ProperOpenPush B d.g).map bd.hom) ≫
      RefinementProjection.finiteComparison D B r T := by
    have h₁ := congrArg (fun v ↦ evY.map v ≫ pc.hom ≫
      (ProperOpenPush B c.g).map bc.hom) hsc
    have h₂ := congrArg ((pd.hom ≫ (ProperOpenPush B d.g).map bd.hom) ≫ ·) hk.symm
    exact h₁.trans (by simpa only [Functor.map_comp, Category.assoc] using hp.trans h₂)
  have h := realize_square RY
    ((coefficientSequenceDerivedEvaluation l E Y.obj.left m).map
      (RefinementProjection.systemComparison l E D o z r M))
    (pc.hom ≫ (ProperOpenPush B c.g).map bc.hom)
    (pd.hom ≫ (ProperOpenPush B d.g).map bd.hom)
    (RefinementProjection.finiteComparison D B r T) hfixed
  simpa only [FiniteCoordinates.support_fixed_eq] using h

private theorem support_coordinate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ≌ B) (U : B ⥤ C) (F : A ⥤ D) (V : D ⥤ C)
    (α : R.functor ⋙ U ≅ F ⋙ V) {K L : B} (a : K ⟶ L) :
    U.map a ≫ U.map (R.counitIso.app L).inv ≫ α.hom.app (R.inverse.obj L) =
      (U.map (R.counitIso.app K).inv ≫ α.hom.app (R.inverse.obj K)) ≫
        V.map (F.map (R.inverse.map a)) := by
  have hn := R.counitIso.inv.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.app_inv]
  rw [← U.map_comp_assoc, hn, U.map_comp]
  simp only [Category.assoc]
  have hα := α.hom.naturality (R.inverse.map a)
  dsimp only [Functor.comp_map] at hα
  rw [hα]

private theorem finish_square
    {C : Type*} [Category C] {z w c d c' d' a b : C}
    (p : z ⟶ w) (sc : w ⟶ c) (sd : z ⟶ d) (κc : c ≅ c') (κd : d ≅ d')
    (tc : w ⟶ c') (td : z ⟶ d') (k : d' ⟶ c')
    (ac : a ≅ c) (ad : b ≅ d) (q : b ⟶ a)
    (h : p ≫ tc = td ≫ k) (hc : sc ≫ κc.hom = tc) (hd : sd ≫ κd.hom = td)
    (hf : q ≫ (ac.hom ≫ κc.hom) = (ad.hom ≫ κd.hom) ≫ k) :
    p ≫ sc = sd ≫ ad.inv ≫ q ≫ ac.hom := by
  rw [← hc, ← hd] at h
  have hk : κd.hom ≫ k = ad.inv ≫ q ≫ ac.hom ≫ κc.hom := by
    apply (cancel_epi ad.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hf.symm
  apply (cancel_mono κc.hom).mp
  calc
    _ = (sd ≫ κd.hom) ≫ k := by simpa only [Category.assoc] using h
    _ = _ := by rw [Category.assoc, hk]; simp only [Category.assoc]

/-- A single evaluation of the directed system refinement is the inverse finite
compactification comparison in the specified finite support coordinates. Only the
one evaluated input is assumed constructible; no integral object occurs.

Source: prop-sf-pf-coherence.proof.md, compactification independence; finite
proper/open mate and direct-image compositor normalization, Stacks 0F7B and 0F7J.
(blueprint: lem-sf-system-refinement-finite-coordinates).

Proof: choose a bounded etale-origin witness for the finite constructible object K,
using the finite-ring constructible-origin equivalence. Transport it along e to the
mth evaluation of M. Evaluate the actual identity direct image, proper/open mate,
and conjugate compositor defining systemComparison. The simultaneous-system
adjunction comparisons identify the first factor with the canonical finite identity
map, the middle factor with the clopen-section proper/open mate, and the last factor
with the canonical finite proper compositor. The clopen projector and all scalar
maps retain the original sections. Thus their composite is the inverse of the
finite refinementComparisonIsomorphism at the retained witness. Substitute
F.finiteRefinementNormalization and cancel the witness identifications. Naturality
of open/proper evaluation and finite support transports the resulting identity
along e, yielding the displayed equation. This computes an already constructed
system map at one level and does not infer equality of system maps. Identity
refinements, zero inputs and empty opens use the same mate calculation. -/
theorem systemRefinementFiniteCoordinates
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (F : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    (hl : IsUnit (C.l : D.k)) (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (M : System C.l E X.obj.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (e : (coefficientSequenceDerivedEvaluation C.l E X.obj.left m).obj M ≅ K.obj) :
    (coefficientSequenceDerivedEvaluation C.l E Y.obj.left m).map
        (RefinementProjection.systemComparison C.l E D o z r M) ≫
      (supportEvaluation C.l E o c m).hom.app M ≫
      (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map e.hom =
    (supportEvaluation C.l E o d m).hom.app M ≫
      (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f d).map e.hom ≫
      (F.finiteSupport f d).inv.app K ≫
      ((F.finite.comparison f c d).inv.app K).hom ≫
      (F.finiteSupport f c).hom.app K  := by
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let RX := sfIntrinsicDerivedEquivalence X.obj.left A
  let RY := sfIntrinsicDerivedEquivalence Y.obj.left A
  let ev := coefficientSequenceDerivedEvaluation C.l E Y.obj.left m
  let V := (coefficientSequenceDerivedEvaluation C.l E X.obj.left m).obj M
  let Uc := sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c
  let Ud := sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f d
  let Fc := sfFixedCompactSupport A c
  let Fd := sfFixedCompactSupport A d
  let αc := sfIntrinsicCompactSupportComparison A c
  let αd := sfIntrinsicCompactSupportComparison A d
  let κc := Uc.mapIso (RX.counitIso.app K.obj).symm ≪≫ αc.app (RX.inverse.obj K.obj)
  let κd := Ud.mapIso (RX.counitIso.app K.obj).symm ≪≫ αd.app (RX.inverse.obj K.obj)
  let sc := (supportEvaluation C.l E o c m).hom.app M ≫ Uc.map e.hom
  let sd := (supportEvaluation C.l E o d m).hom.app M ≫ Ud.map e.hom
  let q := ((F.finite.comparison f c d).inv.app K).hom
  let k := RefinementProjection.finiteComparison D (ULift.{u + 1} A) r
    (RX.inverse.obj K.obj)
  let k₀ := RefinementProjection.finiteComparison D (ULift.{u + 1} A) r
    (RX.inverse.obj V)
  let a := RX.inverse.map e.hom
  have hc : sc ≫ κc.hom = (FiniteCoordinates.support C.l E o m c M).hom ≫
      RY.functor.map (Fc.map a) := by
    have h := support_coordinate_transport RX Uc Fc RY.functor αc e.hom
    simpa only [sc, κc, A, RX, RY, Uc, Fc, αc, a, FiniteCoordinates.input,
      sixFunctorFiniteSupport, sfIntrinsicCompactSupport, sfAmbientCompactSupportCandidate,
      FiniteCoordinates.support, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
      using congrArg ((supportEvaluation C.l E o c m).hom.app M ≫ ·) h
  have hd : sd ≫ κd.hom = (FiniteCoordinates.support C.l E o m d M).hom ≫
      RY.functor.map (Fd.map a) := by
    have h := support_coordinate_transport RX Ud Fd RY.functor αd e.hom
    simpa only [sd, κd, A, RX, RY, Ud, Fd, αd, a, FiniteCoordinates.input,
      sixFunctorFiniteSupport, sfIntrinsicCompactSupport, sfAmbientCompactSupportCandidate,
      FiniteCoordinates.support, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
      using congrArg ((supportEvaluation C.l E o d m).hom.app M ≫ ·) h
  have hs := system_support_square D C.l E o z m c d r M
  have hn := (finiteComparison_naturality D (ULift.{u + 1} A) r a).symm
  have h := mapped_square_transport RY.functor
    (ev.map (RefinementProjection.systemComparison C.l E D o z r M))
    (FiniteCoordinates.support C.l E o m c M).hom
    (FiniteCoordinates.support C.l E o m d M).hom k₀
    (Fc.map a) (Fd.map a) k hs hn
  have hf := support_refinement F hl f c d r K
  have hnorm : q ≫ ((F.finiteSupport f c).hom.app K ≫ κc.hom) =
      ((F.finiteSupport f d).hom.app K ≫ κd.hom) ≫ RY.functor.map k := by
    simpa only [supportRealization, realization, sixFunctorFiniteRealization,
      A, RX, RY, Uc, Ud, αc, αd, q, k, κc, κd, ObjectProperty.ι_map,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
      Category.assoc] using hf
  have hfinal := finish_square
    (ev.map (RefinementProjection.systemComparison C.l E D o z r M)) sc sd κc κd
    ((FiniteCoordinates.support C.l E o m c M).hom ≫ RY.functor.map (Fc.map a))
    ((FiniteCoordinates.support C.l E o m d M).hom ≫ RY.functor.map (Fd.map a))
    (RY.functor.map k) ((F.finiteSupport f c).app K) ((F.finiteSupport f d).app K)
    q h hc hd hnorm
  simpa only [sc, sd, q, Iso.app_inv, Iso.app_hom, Category.assoc] using hfinal

end WeilConjectures.FixProjectionCompactification
