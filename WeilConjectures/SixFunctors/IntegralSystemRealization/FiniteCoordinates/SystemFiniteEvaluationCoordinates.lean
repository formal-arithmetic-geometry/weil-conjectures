/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange

/-! # Fixed-scalar coordinates for one evaluation of system operations

Source: Stacks 03DI, 07A7 and 0F7B; the finite-evaluation calculation in
prop-sf-pf-coherence.proof.md.
(blueprint: def-sf-system-finite-evaluation-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (o : Operations l E) (m : ℕ)

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor CategoryTheory.constantSheaf
  AlgebraicGeometry.Scheme.residueField coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf sfIntrinsicExtensionByZero

/-- The canonical fixed-scalar presentation of the evaluated input.
Source: Stacks 00YV (blueprint: def-sf-system-finite-evaluation-coordinates). -/
abbrev input (X : Scheme.{u}) (M : System l E X) :=
  (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj
    ((coefficientSequenceDerivedEvaluation l E X m).obj M)

/-- Direct evaluation followed by the prescribed coefficient-presentation comparison.
Source: Stacks 07A5 (blueprint: def-sf-system-finite-evaluation-coordinates). -/
def push {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E X) :
    (coefficientSequenceDerivedEvaluation l E Y m).obj ((Operations.push l E o f).obj M) ≅
      (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (m + 1))).functor.obj
        ((ProperOpenPush (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) f).obj
          (input l E m X M)) :=
  ((o.evaluation f).evaluation m).app M ≪≫
    (proEtaleConstantDerivedDirectImage f
      (Padic.coefficientExtensionRing l E (m + 1))).mapIso
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (m + 1))).counitIso.app
            ((coefficientSequenceDerivedEvaluation l E X m).obj M)).symm ≪≫
    (sfIntrinsicDerivedDirectImageComparison f
      (Padic.coefficientExtensionRing l E (m + 1))).app (input l E m X M)

/-- Naturality of the canonical direct coordinates.
Source: Stacks 07A5 (blueprint: def-sf-system-finite-evaluation-coordinates).
Proof: paste evaluation naturality, counit naturality and direct-comparison naturality. -/
theorem push_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : System l E X} (a : M ⟶ N) :
    (coefficientSequenceDerivedEvaluation l E Y m).map
        ((Operations.push l E o f).map a) ≫ (push l E o m f N).hom =
      (push l E o m f M).hom ≫
        (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (m + 1))).functor.map
            ((ProperOpenPush
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) f).map
                ((sfIntrinsicDerivedEquivalence X
                  (Padic.coefficientExtensionRing l E (m + 1))).inverse.map
                    ((coefficientSequenceDerivedEvaluation l E X m).map a))) := by
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let G := proEtaleConstantDerivedDirectImage f A
  let R := sfIntrinsicDerivedEquivalence X A
  let v := (coefficientSequenceDerivedEvaluation l E X m).map a
  dsimp only [push, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  have hn := ((o.evaluation f).evaluation m).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  have hu := R.counitIso.inv.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  rw [← G.map_comp_assoc, hu, G.map_comp]
  simp only [Category.assoc]
  have hv := (sfIntrinsicDerivedDirectImageComparison f A).hom.naturality (R.inverse.map v)
  dsimp only [Functor.comp_map] at hv
  rw [hv]

/-- Exact open evaluation followed by the canonical fixed-scalar open comparison.
Source: Stacks 03DI (blueprint: def-sf-system-finite-evaluation-coordinates). -/
def shriek {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (M : System l E X) :
    (coefficientSequenceDerivedEvaluation l E Y m).obj ((Operations.shriek l E o j).obj M) ≅
      (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (m + 1))).functor.obj
        ((ProperOpenShriek (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) j).obj
          (input l E m X M)) :=
  ((o.openEvaluation j).evaluation m).app M ≪≫
    ((sfIntrinsicExtensionByZero j
      (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory).mapIso
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (m + 1))).counitIso.app
            ((coefficientSequenceDerivedEvaluation l E X m).obj M)).symm ≪≫
    (((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (sfIntrinsicOpenExtensionComparison (Padic.coefficientExtensionRing l E (m + 1)) j)
      ≪≫ Functor.mapDerivedCategoryCompIso _ _).app (input l E m X M))

/-- Cancel the coefficient equivalence after an open evaluation.
Source: Stacks 00YV (blueprint: def-sf-system-finite-evaluation-coordinates). -/
def fixedShriek {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : System l E X) :
    input l E m Y ((Operations.shriek l E o j).obj M) ≅
      (ProperOpenShriek (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) j).obj
        (input l E m X M) :=
  (sfIntrinsicDerivedEquivalence Y
    (Padic.coefficientExtensionRing l E (m + 1))).inverse.mapIso (shriek l E o m j M) ≪≫
    (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (m + 1))).unitIso.symm.app _

/-- Cancel the coefficient equivalence after a direct evaluation.
Source: Stacks 00YV (blueprint: def-sf-system-finite-evaluation-coordinates). -/
def fixedPush {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E X) :
    input l E m Y ((Operations.push l E o f).obj M) ≅
      (ProperOpenPush (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) f).obj
        (input l E m X M) :=
  (sfIntrinsicDerivedEquivalence Y
    (Padic.coefficientExtensionRing l E (m + 1))).inverse.mapIso (push l E o m f M) ≪≫
    (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (m + 1))).unitIso.symm.app _

/-- The recorded support evaluation with its coefficient counit cancelled.
Source: Stacks 0F7J (blueprint: def-sf-system-finite-evaluation-coordinates). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : System l E X) :
    (coefficientSequenceDerivedEvaluation l E Y m).obj
        ((Operations.push l E o c.g).obj ((Operations.shriek l E o c.i).obj M)) ≅
      (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (m + 1))).functor.obj
        ((sfFixedCompactSupport (Padic.coefficientExtensionRing l E (m + 1)) c).obj
          (input l E m X M)) :=
  (supportEvaluation l E o c m).app M ≪≫
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (m + 1)) c).mapIso
      ((sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (m + 1))).counitIso.app
          ((coefficientSequenceDerivedEvaluation l E X m).obj M)).symm ≪≫
    (sfIntrinsicCompactSupportComparison
      (Padic.coefficientExtensionRing l E (m + 1)) c).app (input l E m X M)

attribute [local irreducible] push shriek fixedPush fixedShriek support

/-- An evaluated square transported through a coefficient equivalence.
Source: Stacks 00YV (blueprint: def-sf-system-finite-evaluation-coordinates).
Proof: apply the inverse functor to the square and use naturality of the inverse unit. -/
theorem fixed_square
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {X Y : B} {x y : A} (a : X ≅ R.functor.obj x) (b : Y ≅ R.functor.obj y)
    (p : X ⟶ Y) (k : x ⟶ y) (h : p ≫ b.hom = a.hom ≫ R.functor.map k) :
    R.inverse.map p ≫ (R.inverse.map b.hom ≫ (R.unitIso.app y).inv) =
      (R.inverse.map a.hom ≫ (R.unitIso.app x).inv) ≫ k := by
  rw [← Category.assoc, ← R.inverse.map_comp, h, R.inverse.map_comp]
  simpa only [Category.assoc, Functor.comp_map, Functor.id_map, Iso.app_inv] using
    congrArg (R.inverse.map a.hom ≫ ·) (R.unitIso.inv.naturality k)

/-- Naturality after cancellation of the coefficient equivalence.
Source: Stacks 00YV (blueprint: def-sf-system-finite-evaluation-coordinates).
Proof: apply fixed_square to push_naturality. -/
theorem fixedPush_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : System l E X} (a : M ⟶ N) :
    (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (m + 1))).inverse.map
        ((coefficientSequenceDerivedEvaluation l E Y m).map
          ((Operations.push l E o f).map a)) ≫ (fixedPush l E o m f N).hom =
      (fixedPush l E o m f M).hom ≫
        (ProperOpenPush
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) f).map
            ((sfIntrinsicDerivedEquivalence X
              (Padic.coefficientExtensionRing l E (m + 1))).inverse.map
                ((coefficientSequenceDerivedEvaluation l E X m).map a)) := by
  simpa only [fixedPush, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv] using
    fixed_square _ (push l E o m f M) (push l E o m f N) _ _
      (push_naturality l E o m f a)

private theorem presentation_cancel
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {X : B} {Y : A} (a : X ⟶ R.functor.obj Y) :
    (R.counitIso.app X).inv ≫
        R.functor.map (R.inverse.map a ≫ (R.unitIso.app Y).inv) = a := by
  have hn := R.counitIso.inv.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.app_inv]
  rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc,
    R.counitIso_functor_comp]
  exact Category.comp_id a

private theorem paste_coordinate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ≌ B) (G : B ⥤ C) (F : A ⥤ D) (V : D ⥤ C)
    (ν : R.functor ⋙ G ≅ F ⋙ V) {X : B} {Y : A} (a : X ⟶ R.functor.obj Y) :
    G.map a ≫ ν.hom.app Y =
      G.map (R.counitIso.app X).inv ≫ ν.hom.app (R.inverse.obj X) ≫
        V.map (F.map (R.inverse.map a ≫ (R.unitIso.app Y).inv)) := by
  let b := R.inverse.map a ≫ (R.unitIso.app Y).inv
  have hn := ν.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]
  rw [presentation_cancel]
  rfl

/-- The two canonical operation coordinates paste to the support coordinate.
Source: Stacks 0F7J (blueprint: def-sf-system-finite-evaluation-coordinates).
Proof: expand the two operation evaluations. Naturality of the direct-image
comparison moves the open comparison to the input; the coefficient equivalence's
unit-counit identity cancels its intermediate presentation. -/
theorem support_eq {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : System l E X) :
    (support l E o m c M).hom =
      (push l E o m c.g ((Operations.shriek l E o c.i).obj M)).hom ≫
        (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (m + 1))).functor.map
            ((ProperOpenPush
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) c.g).map
                (fixedShriek l E o m c.i M).hom) := by
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let R := sfIntrinsicDerivedEquivalence c.Z A
  let G := proEtaleConstantDerivedDirectImage c.g A
  let F := ProperOpenPush (ULift.{u + 1} A) c.g
  let V := (sfIntrinsicDerivedEquivalence Y A).functor
  let ν := sfIntrinsicDerivedDirectImageComparison c.g A
  let T := input l E m X M
  let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  let J' := ProperOpenShriek (ULift.{u + 1} A) c.i
  let RX := sfIntrinsicDerivedEquivalence X A
  let ι : RX.functor ⋙ J ≅ J' ⋙ R.functor := by
    dsimp only [RX, R, J, J']
    exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A c.i) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  have hα : (sfIntrinsicCompactSupportComparison A c).hom.app T =
      G.map (ι.hom.app T) ≫ ν.hom.app (J'.obj T) := by
    change 𝟙 _ ≫ G.map (ι.hom.app T) ≫ 𝟙 _ ≫ ν.hom.app (J'.obj T) ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  have hs : (supportEvaluation l E o c m).hom.app M =
      ((o.evaluation c.g).evaluation m).hom.app _ ≫
        G.map (((o.openEvaluation c.i).evaluation m).hom.app M) := by
    change 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  have h := congrArg (((o.evaluation c.g).evaluation m).hom.app
    ((Operations.shriek l E o c.i).obj M) ≫ ·)
      (paste_coordinate R G F V ν (shriek l E o m c.i M).hom)
  simp only [support, push, fixedShriek, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, hs]
  rw [show (sfIntrinsicCompactSupportComparison _ c).hom.app (input l E m X M) =
    G.map (ι.hom.app T) ≫ ν.hom.app (J'.obj T) from hα]
  simp only [Category.assoc]
  change _ ≫ G.map (((o.openEvaluation c.i).evaluation m).hom.app M) ≫
    G.map (J.map (RX.counitIso.app _).inv) ≫
      (G.map (ι.hom.app T) ≫ ν.hom.app _) = _
  change _ = _ ≫ G.map (R.counitIso.app _).inv ≫ ν.hom.app _ ≫
    V.map (F.map (R.inverse.map (shriek l E o m c.i M).hom ≫
      (R.unitIso.app _).inv))
  simpa only [shriek, push, ι, J, J', RX, T, A, id, Functor.id_obj,
    Functor.comp_obj, Operations.shriek, Open.derived, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc] using h

/-- Support coordinates are the realization of the two fixed operation coordinates.
Source: Stacks 00YV and 0F7J (blueprint: def-sf-system-finite-evaluation-coordinates).
Proof: use support_eq and the coefficient-equivalence triangle identity. -/
theorem support_fixed_eq {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : System l E X) :
    let R := sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (m + 1))
    (support l E o m c M).hom =
      (R.counitIso.app _).inv ≫ R.functor.map
        ((fixedPush l E o m c.g ((Operations.shriek l E o c.i).obj M)).hom ≫
          (ProperOpenPush
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) c.g).map
              (fixedShriek l E o m c.i M).hom) := by
  dsimp only
  rw [support_eq, Functor.map_comp, ← Category.assoc]
  have h := presentation_cancel
    (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (m + 1)))
    (push l E o m c.g ((Operations.shriek l E o c.i).obj M)).hom
  simpa only [fixedPush, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom] using
    congrArg (· ≫ (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (m + 1))).functor.map
        ((ProperOpenPush (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
          c.g).map (fixedShriek l E o m c.i M).hom)) h.symm

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
