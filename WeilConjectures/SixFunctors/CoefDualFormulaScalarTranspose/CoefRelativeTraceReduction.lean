/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefRelativeTraceRestriction
import WeilConjectures.SixFunctors.Compact.CompactSupportReductionCoherence
import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefEtaleRelativeTraceRestriction
import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefSupportRealizationRestriction

/-! # Quotient compatibility of the prescribed intrinsic finite trace -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefDualFormulaScalarTranspose

private theorem map_insert_inv_hom
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z : C} {w v : D} (a : x ⟶ y) (e : z ≅ y)
    (b : F.obj y ⟶ w) (q : w ⟶ v) :
    (F.map a ≫ b) ≫ q = F.map (a ≫ e.inv) ≫ (F.map e.hom ≫ b ≫ q) := by
  simp only [Functor.map_comp, Category.assoc, ← F.map_comp_assoc,
    Iso.inv_hom_id, F.map_id, Category.id_comp]

private theorem paste_trace_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x xr x0 : C} {s1 sr sR s0 y1 yR y0 : D}
    (eX : x0 ≅ xr) (eS : s0 ≅ sR) (eY : y0 ≅ yR)
    (p1 : F.obj x ⟶ s1) (pR : F.obj xr ⟶ sr) (d : x ⟶ xr)
    (dS : sr ⟶ sR) (dY : y1 ⟶ yR) (dSupport : s1 ⟶ sr)
    (b1 : s1 ⟶ y1) (bR : sR ⟶ yR) (b0 : s0 ⟶ y0)
    (r : F.obj x0 ⟶ s0)
    (hn : F.map d ≫ pR = p1 ≫ dSupport)
    (ht : b1 ≫ dY = dSupport ≫ dS ≫ bR)
    (hs : F.map eX.hom ≫ pR ≫ dS = r ≫ eS.hom)
    (hy : bR ≫ eY.inv = eS.inv ≫ b0) :
    (p1 ≫ b1) ≫ (dY ≫ eY.inv) = F.map (d ≫ eX.inv) ≫ r ≫ b0 := by
  have hs' := congrArg (fun v ↦ F.map eX.inv ≫ v ≫ eS.inv) hs
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
    Category.id_comp, Iso.hom_inv_id, Category.comp_id] at hs'
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht, ← reassoc_of% hn, hy, reassoc_of% hs']

private theorem reassociate_map
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {u v : D} {x y z : C} (a : u ⟶ v) (r : v ⟶ F.obj x)
    (p : x ⟶ y) (q : y ⟶ z) :
    a ≫ (r ≫ F.map p) ≫ F.map q = a ≫ r ≫ F.map (p ≫ q) := by
  simp only [Functor.map_comp, Category.assoc]

private theorem transport_trace_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F0 : A ⥤ C) (F1 : B ⥤ D) (SX : A ⥤ B) (SY : C ⥤ D)
    (e : SX ⋙ F1 ≅ F0 ⋙ SY)
    {x0 X0 : A} {x1 X1 ar : B} {y0 Y0 r0 : C} {y1 Y1 r1 br : D}
    (ox0 : x0 ≅ X0) (ox1 : x1 ≅ X1) (oy0 : y0 ≅ Y0) (oy1 : y1 ≅ Y1)
    (a1 : x1 ⟶ ar) (a2 : ar ⟶ SX.obj x0)
    (b1 : y1 ⟶ br) (b2 : br ⟶ SY.obj y0)
    (p0 : F0.obj x0 ⟶ r0) (v0 : r0 ⟶ y0)
    (p1 : F1.obj x1 ⟶ r1) (v1 : r1 ⟶ y1)
    (h : (p1 ≫ v1) ≫ (b1 ≫ b2) =
      F1.map (a1 ≫ a2) ≫ e.hom.app x0 ≫ SY.map (p0 ≫ v0)) :
    (F1.map ox1.inv ≫ p1 ≫ v1 ≫ oy1.hom) ≫
        (oy1.inv ≫ b1 ≫ b2 ≫ SY.map oy0.hom) =
      F1.map (ox1.inv ≫ a1 ≫ a2 ≫ SX.map ox0.hom) ≫ e.hom.app X0 ≫
        SY.map (F0.map ox0.inv ≫ p0 ≫ v0 ≫ oy0.hom) := by
  have hn := e.hom.naturality ox0.hom
  dsimp only [Functor.comp_map] at hn
  have h' : p1 ≫ v1 ≫ b1 ≫ b2 =
      F1.map (a1 ≫ a2) ≫ e.hom.app x0 ≫ SY.map (p0 ≫ v0) := by
    simpa only [Category.assoc] using h
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← SY.map_comp_assoc, ← F0.map_comp_assoc, Iso.hom_inv_id,
    F0.map_id, Category.id_comp]

private theorem outputTransition_eq
  (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
  (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
  coefCompactSupportNormalizedTau l E c K.obj n.le_succ =
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
        (normalizedDVRReductionTransition l E X D hl n.le_succ K.obj) ≫
      (finiteSupportRestriction l E c n.le_succ).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K.obj) := by
  rw [← coefCompactSupportInputTau_eq D l hl E X K.obj n]
  unfold coefCompactSupportInputTau finiteSupportRestriction
    coefCompactSupportNormalizedTau coefCompactSupportTau
  exact map_insert_inv_hom _ _
    ((coefCompactSupportRestrictionIso l E X n.le_succ).app _) _ _

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- Successor quotient compatibility of the specified finite relative trace.
Source: blueprint absolute structural trace and its coefficient counit squares
(blueprint: lem-coef-relative-trace-reduction).
Proof: use the structural counit squares and restriction/composition compatibility
on the etale site to obtain the etale relative trace square. Transport that square
through the intrinsic/site restriction square and the specified dualizing origins.
Naturality moves the origins past the restriction comparison and cancels their
inverse pairs, giving the displayed equality. -/
theorem finiteTrace_restriction (n : ℕ) :
  finiteTrace D l E f c (n + 1) ≫
      integralDualizingExceptionalTransition l E D Y hl n.le_succ =
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
        (integralDualizingExceptionalTransition l E D X hl n.le_succ) ≫
      (finiteSupportRestriction l E c n.le_succ).hom.app
        (integralDualizingFiniteTerm l E D X n) ≫
      (normalizedDVRRes l E Y n.le_succ).map (finiteTrace D l E f c n) := by
  let FX := sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c
  let SY := normalizedDVRRes l E Y n.le_succ
  let VX := finiteDualizingRealization l E X (n + 1)
  let V := finiteDualizingRealization l E Y (n + 1)
  let V0 := finiteDualizingRealization l E Y n
  let K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))) :=
    ⟨finiteDualizingEtaleTerm l E D X n, finiteEtaleDualizing_plus D l E X n⟩
  have hn := (finiteSupportRealization l E c (n + 1)).hom.naturality
    (ObjectProperty.homMk (X :=
      ⟨finiteDualizingEtaleTerm l E D X (n + 1),
        finiteEtaleDualizing_plus D l E X (n + 1)⟩)
      (Y := (Sheaf.restrictScalars X.smallEtaleTopology
      (finiteDualizingQuotient l E n.le_succ)).mapDerivedCategoryPlus.obj K)
      (finiteDualizingEtaleTransition l E D X n.le_succ))
  have ht := congrArg (fun v ↦ V.map v) (finiteEtaleTrace_restriction D l E f c n)
  have ht' : V.map (finiteEtaleTrace D l E f c (n + 1)) ≫
      V.map (finiteDualizingEtaleTransition l E D Y n.le_succ) =
    V.map ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c).map
        (finiteDualizingEtaleTransition l E D X n.le_succ)) ≫
      V.map (finiteEtaleSupportRestriction (finiteDualizingQuotient l E n.le_succ) c K) ≫
        V.map ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
          (finiteDualizingQuotient l E n.le_succ)).map (finiteEtaleTrace D l E f c n)) := by
    simpa only [V.map_comp] using ht
  have hs := finiteSupportRealization_restriction l E c n.le_succ K
  have hy := (finiteDualizingRealizationRestriction l E Y n.le_succ).inv.naturality
    (finiteEtaleTrace D l E f c n)
  have hreal := paste_trace_square FX
    ((finiteDualizingRealizationRestriction l E X n.le_succ).app K.obj)
    ((finiteDualizingRealizationRestriction l E Y n.le_succ).app
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).obj K.obj))
    ((finiteDualizingRealizationRestriction l E Y n.le_succ).app
      (finiteDualizingEtaleTerm l E D Y n))
    (finiteSupportOrigin D l E f c (n + 1)).hom
    ((finiteSupportRealization l E c (n + 1)).hom.app
      ((Sheaf.restrictScalars X.smallEtaleTopology
        (finiteDualizingQuotient l E n.le_succ)).mapDerivedCategoryPlus.obj K))
    (VX.map (finiteDualizingEtaleTransition l E D X n.le_succ))
    (V.map (finiteEtaleSupportRestriction (finiteDualizingQuotient l E n.le_succ) c K))
    (V.map (finiteDualizingEtaleTransition l E D Y n.le_succ))
    (V.map ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c).map
        (finiteDualizingEtaleTransition l E D X n.le_succ)))
    (V.map (finiteEtaleTrace D l E f c (n + 1)))
    (V.map ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
      (finiteDualizingQuotient l E n.le_succ)).map (finiteEtaleTrace D l E f c n)))
    (SY.map (V0.map (finiteEtaleTrace D l E f c n)))
    ((finiteSupportRestriction l E c n.le_succ).hom.app
      ((finiteDualizingRealization l E X n).obj K.obj) ≫
      SY.map (finiteSupportOrigin D l E f c n).hom)
    hn ht' (hs.trans (Category.assoc _ _ _).symm) hy
  refine transport_trace_square
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c)
    FX (normalizedDVRRes l E X n.le_succ) SY (finiteSupportRestriction l E c n.le_succ)
    (finiteDualizingOrigin l E D X n) (finiteDualizingOrigin l E D X (n + 1))
    (finiteDualizingOrigin l E D Y n) (finiteDualizingOrigin l E D Y (n + 1))
    (VX.map (finiteDualizingEtaleTransition l E D X n.le_succ))
    ((finiteDualizingRealizationRestriction l E X n.le_succ).inv.app K.obj)
    (V.map (finiteDualizingEtaleTransition l E D Y n.le_succ))
    ((finiteDualizingRealizationRestriction l E Y n.le_succ).inv.app
      (finiteDualizingEtaleTerm l E D Y n))
    (finiteSupportOrigin D l E f c n).hom (V0.map (finiteEtaleTrace D l E f c n))
    (finiteSupportOrigin D l E f c (n + 1)).hom
    (V.map (finiteEtaleTrace D l E f c (n + 1))) ?_
  exact hreal.trans (reassociate_map SY _ _ _ _)

end WeilConjectures.CoefDualFormulaScalarTranspose
