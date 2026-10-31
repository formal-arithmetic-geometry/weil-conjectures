/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension

/-! # Assembly of the closed dualizing coefficient comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md, paragraph 3, sentences 2--3
(blueprint: lem-coef-dualizing-closed-assembly).

The assertion is written under the stipulated counit-compatible structural
identifications: the Y adjunction is literally the composite of closed direct
image and affine-space compact support. Right adjoints and their adjunctions
are quantified, so the assertion applies to every counit-compatible presentation.
All left functors, scalar functors and coefficient components are the recorded
ordinary small-etale constructions, not arbitrary comparison data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem closedAssembly_counit
    {YA PA SA YB PB SB : Type*}
    [Category YA] [Category PA] [Category SA]
    [Category YB] [Category PB] [Category SB]
    {FA : PA ⥤ SA} {FB : PB ⥤ SB} {JA : YA ⥤ PA} {JB : YB ⥤ PB}
    {GA : SA ⥤ PA} {GB : SB ⥤ PB} {IA : PA ⥤ YA} {IB : PB ⥤ YB}
    (adjPA : FA ⊣ GA) (adjPB : FB ⊣ GB)
    (adjIA : JA ⊣ IA) (adjIB : JB ⊣ IB)
    (TY : YA ⥤ YB) (TP : PA ⥤ PB) (TS : SA ⥤ SB)
    (h : FA ⋙ TS ⟶ TP ⋙ FB) (oneA : SA) (oneB : SB)
    (unit : TS.obj oneA ⟶ oneB)
    (d : TP.obj (JA.obj (IA.obj (GA.obj oneA))) ⟶
      JB.obj (TY.obj (IA.obj (GA.obj oneA)))) [IsIso d]
    [IsIso (h.app (GA.obj oneA))]
    (uP : TP.obj (GA.obj oneA) ⟶ GB.obj oneB)
    (hP : FB.map uP ≫ adjPB.counit.app oneB =
      inv (h.app (GA.obj oneA)) ≫ TS.map (adjPA.counit.app oneA) ≫ unit)
    (b : TY.obj (IA.obj (GA.obj oneA)) ⟶ IB.obj (TP.obj (GA.obj oneA)))
    (hb : JB.map b ≫ adjIB.counit.app (TP.obj (GA.obj oneA)) =
      inv d ≫ TP.map (adjIA.counit.app (GA.obj oneA))) :
    (h.app (JA.obj (IA.obj (GA.obj oneA))) ≫ FB.map d) ≫
        (JB ⋙ FB).map (b ≫ IB.map uP) ≫ (adjIB.comp adjPB).counit.app oneB =
      TS.map ((adjIA.comp adjPA).counit.app oneA) ≫ unit := by
  have he := adjIB.counit.naturality uP
  dsimp only [Functor.comp_map, Functor.id_map] at he
  simp only [Functor.comp_map, Functor.map_comp, Adjunction.comp_counit_app,
    Category.assoc]
  rw [← FB.map_comp_assoc (JB.map (IB.map uP)) (adjIB.counit.app (GB.obj oneB)),
    he, FB.map_comp]
  simp only [Category.assoc]
  rw [← FB.map_comp_assoc (JB.map b) (adjIB.counit.app (TP.obj (GA.obj oneA))),
    hb, FB.map_comp]
  simp only [Category.assoc]
  rw [← FB.map_comp_assoc d (inv d), IsIso.hom_inv_id, FB.map_id, Category.id_comp]
  have hn := h.naturality (adjIA.counit.app (GA.obj oneA))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← Category.assoc (h.app (JA.obj (IA.obj (GA.obj oneA))))
    (FB.map (TP.map (adjIA.counit.app (GA.obj oneA))))]
  rw [← hn]
  simp only [Category.assoc]
  rw [hP]
  simp only [IsIso.hom_inv_id_assoc]

end WeilConjectures
