/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedExceptionalReconstructionData
/-! The naturality half of the condensed exceptional counit representation.
Source: actual reduction/limit counit naturality, scalar-extension functoriality and
projection naturality in the reconstruction proof.
(blueprint: lem-pur-condensed-exceptional-counit-naturality).
The proof pastes the actual Brown, site, limit, realization and projection squares.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] WeilConjectures.purCoefficientModel
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting
attribute [local irreducible] Datum.realizedCounit Datum.extendedCounit
  Datum.projectedCounit Datum.condensedCounit realization
  condensedProjection condensedScalar
variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
variable {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
  [f.IsOver (Spec (.of k))] {c : Compactification f}
  (P : Context l k X Y f c)
variable (D : CondensedERealization.Data l (Field.{u} l) k)
  (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)

private theorem inverse_square
    {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : Y ⟶ Z) [IsIso f] [IsIso g]
    (a : W ⟶ Y) (b : X ⟶ Z) (h : f ≫ b = a ≫ g) :
    inv f ≫ a = b ≫ inv g := by
  apply (cancel_mono g).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

private theorem brown_square
    {C E T : Type*} [Category C] [Category E] [Category T]
    (V : C ⥤ E) (I : E ⥤ C) (s : I ⊣ V)
    (L : E ⥤ T) (R : T ⥤ E) (B : L ⊣ R)
    {Md Me : C} {Ld Le : T} (a : Md ⟶ Me) (b : Ld ⟶ Le)
    (td : Md ⟶ I.obj (R.obj Ld)) (te : Me ⟶ I.obj (R.obj Le))
    [IsIso (s.unit.app (R.obj Ld))] [IsIso (s.unit.app (R.obj Le))]
    (h : a ≫ te = td ≫ I.map (R.map b)) :
    L.map (V.map a) ≫ (B.homEquiv _ _).symm
        (V.map te ≫ inv (s.unit.app (R.obj Le))) =
      (B.homEquiv _ _).symm (V.map td ≫ inv (s.unit.app (R.obj Ld))) ≫ b := by
  have hu := inverse_square (s.unit.app (R.obj Ld)) (s.unit.app (R.obj Le))
    (R.map b) (V.map (I.map (R.map b))) (s.unit.naturality (R.map b)).symm
  have ht : V.map a ≫ (V.map te ≫ inv (s.unit.app (R.obj Le))) =
      (V.map td ≫ inv (s.unit.app (R.obj Ld))) ≫ R.map b := by
    rw [← Category.assoc, ← V.map_comp, h, V.map_comp,
      Category.assoc, ← hu, ← Category.assoc]
  have hb := congrArg (B.homEquiv _ _).symm ht
  rw [B.homEquiv_naturality_left_symm, B.homEquiv_naturality_right_symm] at hb
  exact hb

private theorem pro_square
    {C T E : Type*} [Category C] [Category T] [Category E]
    (F : C ⥤ T) (G : T ⥤ E) (S : C ⥤ E) (J : E ⥤ T)
    (ε : J ⋙ G ⟶ 𝟭 E) (α : F ⋙ G ⟶ S)
    {Md Me : C} {Ld Le : E} (a : Md ⟶ Me) (b : Ld ⟶ Le)
    (cd : F.obj Md ⟶ J.obj Ld) (ce : F.obj Me ⟶ J.obj Le)
    [IsIso (α.app Md)] [IsIso (α.app Me)]
    (h : F.map a ≫ ce = cd ≫ J.map b) :
    S.map a ≫ (inv (α.app Me) ≫ G.map ce ≫ ε.app Le) =
      (inv (α.app Md) ≫ G.map cd ≫ ε.app Ld) ≫ b := by
  have hk := inverse_square (α.app Md) (α.app Me)
    ((F ⋙ G).map a) (S.map a) (α.naturality a).symm
  dsimp only [Functor.comp_map] at hk
  have hc := congrArg G.map h
  simp only [Functor.map_comp] at hc
  have hn := ε.naturality b
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have h1 := congrArg (fun z ↦ z ≫ G.map ce ≫ ε.app Le) hk.symm
  have h2 := congrArg (fun z ↦ inv (α.app Md) ≫ z ≫ ε.app Le) hc
  have h3 := congrArg (fun z ↦ inv (α.app Md) ≫ G.map cd ≫ z) hn
  simp only [Category.assoc] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3)

section
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
set_option maxHeartbeats 1600000 in
-- The Brown/site paste elaborates many ordinary derived-category instances.
private theorem proCounit_natural
    (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (sd : SystemIdentification l k d hd) (se : SystemIdentification l k e he)
    (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower)
    (ha : d.SystemMap l k b a sd.theta se.theta) :
    (exceptionalProSupport P.support).map a ≫
      e.proCounit l k se.theta se.originUnit se.originSupport =
    d.proCounit l k sd.theta sd.originUnit sd.originSupport ≫
      (P.target.sequence.derived.inverse.map
        ((P.reduction Y.scheme).reduction.map
          ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.map b.hom))) := by
  have := sd.originSupport
  have := se.originSupport
  have := sd.originUnit
  have := se.originUnit
  let V := P.source.derived.system.direct
  let C := P.target.derived.system.inverse
  let m := (input l k P).map b
  dsimp only [Datum.SystemMap] at ha
  have hb := brown_square V P.source.derived.system.inverse
    P.source.derived.system.adjunction P.etale.functor P.brown.right P.brown.adjunction
    a m sd.theta.hom se.theta.hom ha
  simpa only [Datum.proCounit, input, reduced, Functor.comp_obj, Functor.comp_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.ι_map, ObjectProperty.ι_obj,
    Functor.id_obj, Category.assoc, V, C, m] using
    pro_square (V ⋙ P.etale.functor) C (exceptionalProSupport P.support)
      P.target.derived.system.direct P.target.derived.system.adjunction.counit
      (exceptionalSystemOriginComparison P.comparison) a
      (P.target.sequence.derived.inverse.map
        ((P.reduction Y.scheme).reduction.map
          ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.map b.hom)))
      ((P.brown.adjunction.homEquiv _ _).symm
        (V.map sd.theta.hom ≫ inv (P.source.derived.system.adjunction.unit.app
          (P.brown.right.obj ((input l k P).obj d.L)))))
      ((P.brown.adjunction.homEquiv _ _).symm
        (V.map se.theta.hom ≫ inv (P.source.derived.system.adjunction.unit.app
          (P.brown.right.obj ((input l k P).obj e.L))))) hb

private theorem sequenceCounit_natural
    (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (sd : SystemIdentification l k d hd) (se : SystemIdentification l k e he)
    (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower)
    (ha : d.SystemMap l k b a sd.theta se.theta) :
    (systemSupport l (Field.{u} l) c).map (P.source.sequence.derived.functor.map a) ≫
      e.sequenceCounit l k se.theta se.originUnit se.originSupport =
    d.sequenceCounit l k sd.theta sd.originUnit sd.originSupport ≫
      (P.reduction Y.scheme).reduction.map
        ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.map b.hom) := by
  have hp := proCounit_natural l k P d e hd he sd se b a ha
  have hs := (supportSequence l k P).inv.naturality a
  change (systemSupport l (Field.{u} l) c).map
      (P.source.sequence.derived.functor.map a) ≫ (supportSequence l k P).inv.app e.tower =
    (supportSequence l k P).inv.app d.tower ≫
      P.target.sequence.derived.functor.map ((exceptionalProSupport P.support).map a) at hs
  have hc := congrArg P.target.sequence.derived.functor.map hp
  simp only [Functor.map_comp] at hc
  have hn := P.target.sequence.derived.counitIso.hom.naturality
    ((P.reduction Y.scheme).reduction.map
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.map b.hom))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have h1 := congrArg (fun z ↦ z ≫
    P.target.sequence.derived.functor.map
      (e.proCounit l k se.theta se.originUnit se.originSupport) ≫
    P.target.sequence.derived.counitIso.hom.app _) hs
  have h2 := congrArg (fun z ↦ (supportSequence l k P).inv.app d.tower ≫ z ≫
    P.target.sequence.derived.counitIso.hom.app _) hc
  have h3 := congrArg (fun z ↦ (supportSequence l k P).inv.app d.tower ≫
    P.target.sequence.derived.functor.map
      (d.proCounit l k sd.theta sd.originUnit sd.originSupport) ≫ z) hn
  simp only [Category.assoc] at h1 h2 h3
  simpa only [Datum.sequenceCounit, Category.assoc] using h1.trans (h2.trans h3)

end

set_option maxHeartbeats 1600000 in
-- The full coefficient-model and limit naturality paste needs additional heartbeats.
private theorem integralCounit_natural
    (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (sd : SystemIdentification l k d hd) (se : SystemIdentification l k e he)
    (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower)
    (ha : d.SystemMap l k b a sd.theta se.theta) :
    (integralSupport l (Field.{u} l) c P.reduction A.integral).map
        (Datum.LimitMap l k a hd.reconstructs he.reconstructs) ≫
      e.integralCounit l k D he.reconstructs A se.reduction se.theta
        se.originUnit se.originSupport =
    d.integralCounit l k D hd.reconstructs A sd.reduction sd.theta
        sd.originUnit sd.originSupport ≫ b := by
  have := sd.reduction
  have := se.reduction
  let MX := purCoefficientModel l (Field.{u} l) X.scheme
  let MY := purCoefficientModel l (Field.{u} l) Y.scheme
  let RX := (P.reduction X.scheme).reduction
  let RY := (P.reduction Y.scheme).reduction
  let LX := coefficientSequenceLimit l (Field.{u} l) X.scheme
  let LY := coefficientSequenceLimit l (Field.{u} l) Y.scheme
  let S := systemSupport l (Field.{u} l) c
  let v := P.source.sequence.derived.functor.map a
  let q := MY.functor.map b.hom
  let vd := RX.map (MX.counitIso.hom.app (d.limit l k)) ≫
    (P.reduction X.scheme).adjunction.counit.app
      (P.source.sequence.derived.functor.obj d.tower)
  let ve := RX.map (MX.counitIso.hom.app (e.limit l k)) ≫
    (P.reduction X.scheme).adjunction.counit.app
      (P.source.sequence.derived.functor.obj e.tower)
  have hx := MX.counitIso.hom.naturality (LX.map v)
  dsimp only [Functor.comp_map, Functor.id_map] at hx
  have hr := (P.reduction X.scheme).adjunction.counit.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at hr
  have hv : RX.map (MX.functor.map (MX.inverse.map (LX.map v))) ≫ ve = vd ≫ v := by
    have h1 := congrArg (fun z ↦ z ≫
      (P.reduction X.scheme).adjunction.counit.app
        (P.source.sequence.derived.functor.obj e.tower)) (congrArg RX.map hx)
    have h2 := congrArg (fun z ↦ RX.map (MX.counitIso.hom.app (d.limit l k)) ≫ z) hr
    simp only [Functor.map_comp, Category.assoc] at h1 h2
    simpa only [LX, RX, vd, ve, v, S, RY, q, Functor.map_comp, Category.assoc, Datum.limit]
      using h1.trans h2
  have ht := sequenceCounit_natural l k P d e hd he sd se b a ha
  have hs : S.map (RX.map (MX.functor.map (MX.inverse.map (LX.map v)))) ≫
      (S.map ve ≫ e.sequenceCounit l k se.theta se.originUnit se.originSupport) =
    (S.map vd ≫ d.sequenceCounit l k sd.theta sd.originUnit sd.originSupport) ≫
      RY.map q := by
    have h1 := congrArg (fun z ↦ z ≫
      e.sequenceCounit l k se.theta se.originUnit se.originSupport) (congrArg S.map hv)
    have h2 := congrArg (fun z ↦ S.map vd ≫ z) ht
    simp only [Functor.map_comp, Category.assoc] at h1 h2
    simpa only [v, S, RY, q, Functor.map_comp, Category.assoc] using h1.trans h2
  have hu := inverse_square
    ((P.reduction Y.scheme).adjunction.unit.app (MY.functor.obj d.L.obj))
    ((P.reduction Y.scheme).adjunction.unit.app (MY.functor.obj e.L.obj))
    q (LY.map (RY.map q)) ((P.reduction Y.scheme).adjunction.unit.naturality q).symm
  have h1 := congrArg (fun z ↦ z ≫
    inv ((P.reduction Y.scheme).adjunction.unit.app (MY.functor.obj e.L.obj)))
    (congrArg LY.map hs)
  have h2 := congrArg (fun z ↦ LY.map
    (S.map vd ≫ d.sequenceCounit l k sd.theta sd.originUnit sd.originSupport) ≫ z) hu.symm
  simp only [Functor.map_comp, Category.assoc] at h1 h2
  have hz := congrArg MY.inverse.map (h1.trans h2)
  have hn := MY.unitIso.inv.naturality b.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have h3 := congrArg (fun z ↦ z ≫ MY.unitIso.inv.app e.L.obj) hz
  have h4 := congrArg (fun z ↦ MY.inverse.map
    (LY.map (S.map vd ≫ d.sequenceCounit l k sd.theta sd.originUnit sd.originSupport) ≫
      inv ((P.reduction Y.scheme).adjunction.unit.app (MY.functor.obj d.L.obj))) ≫ z) hn
  simp only [Functor.map_comp, Category.assoc] at h3 h4
  apply ObjectProperty.hom_ext
  dsimp only [Datum.integralCounit, ObjectProperty.FullSubcategory.comp_hom]
  simpa only [Datum.LimitMap, Datum.limit, LX, LY, RX, RY, MX, MY, S, v, q, vd, ve,
    Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom, ObjectProperty.ι_map, ObjectProperty.ι_obj,
    Functor.id_obj, Datum.integral, coefficientSequenceLimit,
    integralSupport, rawSupport, strictTower,
    Functor.comp_map, ObjectProperty.lift_map, Category.assoc] using h3.trans h4

set_option allowUnsafeReducibility true in
attribute [local irreducible] CondensedRing.rightDerivedLowerShriekOfCompactification in
private theorem realizedCounit_natural
    (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (sd : SystemIdentification l k d hd) (se : SystemIdentification l k e he)
    (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower)
    (ha : d.SystemMap l k b a sd.theta se.theta) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.continuousCoefficientRingObj (Field.{u} l)) c).map
      (((D.atObject X).realization.functor.map
        ((pbcRationalization X.scheme (pbcIntegralDatum l (Field.{u} l))
          (pbcUniformizer l (Field.{u} l))).map
            (Datum.LimitMap l k a hd.reconstructs he.reconstructs))).hom) ≫
      e.realizedCounit l k D he.reconstructs A se.reduction se.theta
        se.originUnit se.originSupport =
    d.realizedCounit l k D hd.reconstructs A sd.reduction sd.theta
        sd.originUnit sd.originSupport ≫
      (((D.atObject Y).realization.functor.map
        ((pbcRationalization Y.scheme (pbcIntegralDatum l (Field.{u} l))
          (pbcUniformizer l (Field.{u} l))).map b)).hom) := by
  let QX := pbcRationalization X.scheme (pbcIntegralDatum l (Field.{u} l))
    (pbcUniformizer l (Field.{u} l))
  let QY := pbcRationalization Y.scheme (pbcIntegralDatum l (Field.{u} l))
    (pbcUniformizer l (Field.{u} l))
  let VY := (D.atObject Y).realization.functor ⋙
    (boundedConstructible (Coefficient (Field.{u} l) Y.scheme)).ι
  have ht := integralCounit_natural l k P D A d e hd he sd se b a ha
  have hn := A.realization.inv.naturality
    (QX.map (Datum.LimitMap l k a hd.reconstructs he.reconstructs))
  have hq : (rationalSupport l (Field.{u} l) c P.reduction A.integral).map
      (QX.map (Datum.LimitMap l k a hd.reconstructs he.reconstructs)) =
    QY.map ((integralSupport l (Field.{u} l) c P.reduction A.integral).map
      (Datum.LimitMap l k a hd.reconstructs he.reconstructs)) := by
    simp only [rationalSupport, QX, QY, pbcRationalization,
      ScalarLocalization.transport, ScalarLocalization.localization,
      ScalarLocalization.transportHom, LinearMap.baseChange_tmul, Functor.mapLinearMap_apply]
    rfl
  dsimp only [Functor.comp_map, ObjectProperty.ι_map] at hn
  rw [hq] at hn
  have hm := congrArg VY.map (congrArg QY.map ht)
  simp only [Functor.map_comp] at hm
  have h1 := congrArg (fun z ↦ z ≫ VY.map (QY.map
    (e.integralCounit l k D he.reconstructs A se.reduction se.theta
      se.originUnit se.originSupport))) hn
  have h2 := congrArg (fun z ↦ A.realization.inv.app
    (QX.obj (d.integral l k hd.reconstructs)) ≫ z) hm
  simp only [Category.assoc] at h1 h2
  simpa only [Datum.realizedCounit, QX, QY, VY, Functor.comp_map,
    ObjectProperty.ι_map, Category.assoc] using h1.trans h2

private theorem projected_square
    {C E V : Type*} [Category C] [Category E] [Category V]
    (F : C ⥤ E) (G : E ⥤ V) (H : C ⥤ V) (α : F ⋙ G ⟶ H)
    {Md Me : C} {Ld Le : E} (v : Md ⟶ Me) (b : Ld ⟶ Le)
    (cd : F.obj Md ⟶ Ld) (ce : F.obj Me ⟶ Le)
    [IsIso (α.app Md)] [IsIso (α.app Me)] (h : F.map v ≫ ce = cd ≫ b) :
    H.map v ≫ (inv (α.app Me) ≫ G.map ce) =
      (inv (α.app Md) ≫ G.map cd) ≫ G.map b := by
  have hn := inverse_square (α.app Md) (α.app Me)
    (G.map (F.map v)) (H.map v) (α.naturality v).symm
  have hm := congrArg G.map h
  simp only [Functor.map_comp] at hm
  rw [← Category.assoc, ← hn, Category.assoc, hm, ← Category.assoc]

private theorem inclusion_square
    {C E V : Type*} [Category C] [Category E] [Category V]
    (F : C ⥤ E) (G : E ⥤ V) (H : C ⥤ V) (α : F ⋙ G ⟶ H)
    {Md Me : C} {Ld Le : E} (v : Md ⟶ Me) (b : Ld ⟶ Le)
    (cd : H.obj Md ⟶ G.obj Ld) (ce : H.obj Me ⟶ G.obj Le)
    (h : H.map v ≫ ce = cd ≫ G.map b) :
    G.map (F.map v) ≫ (α.app Me ≫ ce) =
      (α.app Md ≫ cd) ≫ G.map b := by
  have hn := α.naturality v
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, h, ← Category.assoc]

attribute [local semireducible] realization

set_option allowUnsafeReducibility true in
attribute [local irreducible] CondensedRing.rightDerivedLowerShriekOfCompactification
  CondensedRing.boundedConstructibleLowerShriekOfCompactification
  CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Datum.LimitMap in
/-- The extended condensed counit is natural for actual compatible system maps.
Source: current blueprint sk-prop-sp-integral-adjunction, final unit/counit paragraph;
sk-prop-sp-rational and sk-thm-sp-qbar, scalar-extended unit and counit.
(blueprint: lem-pur-condensed-exceptional-counit-naturality).

Proof: invert the source-site unit naturality square and compose the supplied
Brown-system square. Apply the inverse Brown Hom equivalence and its two naturality
identities. Invert the compact-support origin square, and paste the target-site
counit square. This gives the pro-system counit square. Apply the target sequence
equivalence, its counit, and supportSequence naturality to obtain the sequence square.
Naturality of the coefficient-model counit and the reduction/limit counit gives the
source reconstruction square; applying total limit and inverting the target unit
square gives integralCounit naturality. Rationalize this equality and paste the
specified realization comparison. Apply closure scalar extension, invert the
projection naturality square, and paste the bounded inclusion comparison. Faithfulness
of the full bounded constructible inclusion gives the stated morphism equality.
-/
theorem condensed_exceptional_counit_naturality :
    ∀ (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
      (sd : SystemIdentification l k d hd) (se : SystemIdentification l k e he)
      (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower),
      d.SystemMap l k b a sd.theta se.theta →
      (CondensedRing.boundedConstructibleLowerShriekOfCompactification l (f := X.map Y f) c).map
          ((realization l k D X).map (Datum.LimitMap l k a hd.reconstructs he.reconstructs)) ≫
        e.condensedCounit l k D he.reconstructs A se.reduction se.theta
          se.originUnit se.originSupport =
      d.condensedCounit l k D hd.reconstructs A sd.reduction sd.theta
          sd.originUnit sd.originSupport ≫ (realization l k D Y).map b := by
  intro d e hd he sd se b a ha
  let QX := pbcRationalization X.scheme (pbcIntegralDatum l (Field.{u} l))
    (pbcUniformizer l (Field.{u} l))
  let QY := pbcRationalization Y.scheme (pbcIntegralDatum l (Field.{u} l))
    (pbcUniformizer l (Field.{u} l))
  let JX := (D.atObject X).realization.functor ⋙
    (boundedConstructible (Coefficient (Field.{u} l) X.scheme)).ι
  let JY := (D.atObject Y).realization.functor ⋙
    (boundedConstructible (Coefficient (Field.{u} l) Y.scheme)).ι
  let SX := omegaScalar l (Field.{u} l) (embedding l) X.scheme
  let SY := omegaScalar l (Field.{u} l) (embedding l) Y.scheme
  let v := Datum.LimitMap l k a hd.reconstructs he.reconstructs
  let m := JX.map (QX.map v)
  let n := JY.map (QY.map b)
  let pd := (condensedProjection (omegaMap l (Field.{u} l) (embedding l)) c).app
    (JX.obj (QX.obj (d.integral l k hd.reconstructs)))
  let pe := (condensedProjection (omegaMap l (Field.{u} l) (embedding l)) c).app
    (JX.obj (QX.obj (e.integral l k he.reconstructs)))
  have : IsIso pd := omegaProjection_isIso l (Field.{u} l) k (embedding l) X Y f c
    ((D.atObject X).realization.functor.obj (QX.obj (d.integral l k hd.reconstructs)))
  have : IsIso pe := omegaProjection_isIso l (Field.{u} l) k (embedding l) X Y f c
    ((D.atObject X).realization.functor.obj (QX.obj (e.integral l k he.reconstructs)))
  have ht := realizedCounit_natural l k P D A d e hd he sd se b a ha
  have ht' : (CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.padicAlgClRingObj l) c).map (SX.map m) ≫
      e.projectedCounit l k D he.reconstructs A se.reduction se.theta
        se.originUnit se.originSupport =
    d.projectedCounit l k D hd.reconstructs A sd.reduction sd.theta
      sd.originUnit sd.originSupport ≫ SY.map n := by
    simpa only [Datum.projectedCounit, Datum.extendedCounit, pd, pe, SX, SY, n, JX, JY,
      QX, QY, Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map,
      ObjectProperty.ι_map] using
      projected_square
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj (Field.{u} l)) c)
        SY (SX ⋙ CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj l) c)
        (condensedProjection (omegaMap l (Field.{u} l) (embedding l)) c) m n
        (d.realizedCounit l k D hd.reconstructs A sd.reduction sd.theta
          sd.originUnit sd.originSupport)
        (e.realizedCounit l k D he.reconstructs A se.reduction se.theta
          se.originUnit se.originSupport) ht
  let K := CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
    l (f := X.map Y f) c
  have ht'' : ((boundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj l) X.scheme)).ι ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) c).map ((realization l k D X).map v) ≫
      e.projectedCounit l k D he.reconstructs A se.reduction se.theta
        se.originUnit se.originSupport =
    d.projectedCounit l k D hd.reconstructs A sd.reduction sd.theta
      sd.originUnit sd.originSupport ≫
      ((boundedConstructible (condensedRingObj
        (Profinite.padicAlgClRingObj l) Y.scheme)).ι).map ((realization l k D Y).map b) := by
    simpa only [realization, Functor.comp_map, ObjectProperty.ι_map,
      ObjectProperty.lift_map, ObjectProperty.homMk_hom, v, m, n, JX, JY, QX, QY, SX, SY]
      using ht'
  apply ObjectProperty.hom_ext
  simpa only [Datum.condensedCounit, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom, Functor.comp_map, ObjectProperty.ι_map, v, K] using
    inclusion_square
      (CondensedRing.boundedConstructibleLowerShriekOfCompactification
        l (f := X.map Y f) c)
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y.scheme)).ι
      ((boundedConstructible (condensedRingObj
        (Profinite.padicAlgClRingObj l) X.scheme)).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj l) c) K.hom
      ((realization l k D X).map v) ((realization l k D Y).map b)
      (d.projectedCounit l k D hd.reconstructs A sd.reduction sd.theta
        sd.originUnit sd.originSupport)
      (e.projectedCounit l k D he.reconstructs A se.reduction se.theta
        se.originUnit se.originSupport) ht''

end WeilConjectures.CondensedExceptionalReconstruction
