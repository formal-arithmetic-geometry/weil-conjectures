/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Closed.ClosedOpenDualizingMate
import all WeilConjectures.AlgebraicGeometry.Closed.ClosedOpenDualizingMate
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
import all WeilConjectures.SixFunctors.Coefficient.CoefficientDualizingClosedAssembly
import all WeilConjectures.CategoryTheory.SixFunctors.CounitMateTransport
import WeilConjectures.AlgebraicGeometry.Open.OpenClosedCompactScalar

/-! # Compatibility of the open and closed dualizing coefficient mates

Source: the finite dualizing proof, paragraph 3
(blueprint: dualizing-open-closed-mate-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor scalarMate
  ProEtale.pbcFixedScalarExtension Functor.mapDerivedCategory
  rightDerivedLowerStarUpperShriekAdjunctionOfIsProper
  rightDerivedUpperShriekAdjunction

private theorem cancelIso_counit
    {C : Type*} [Category C] {X Y Z W : C} (q : X ≅ Y)
    (u : Y ⟶ Z) (v : Z ⟶ W) (w : X ⟶ W) (h : q.hom ≫ u ≫ v = w) :
    u ≫ v = q.inv ≫ w :=
  (q.eq_inv_comp).2 h

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem structural_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {P S : Scheme.{u}} [IsNoetherian S]
    (p : P ⟶ S) [HasCompactification p] :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) p).map
        (ExceptionalCoefficients.dualizingScalarMap φ p) ≫
      (rightDerivedUpperShriekAdjunction B p).counit.app
        (𝟙_ (DerivedCategoryModule B S)) =
      (ExceptionalCoefficients.chosenCompactSupportIso φ p).inv.app
        (dualizingComplex A p) ≫
        (scalarExtension φ S).map
          ((rightDerivedUpperShriekAdjunction A p).counit.app
            (𝟙_ (DerivedCategoryModule A S))) ≫ (ExceptionalCoefficients.unitIso φ S).hom := by
  dsimp only [dualizingComplex]
  exact cancelIso_counit
    ((ExceptionalCoefficients.chosenCompactSupportIso φ p).app
      (dualizingComplex A p)) _ _ _
    (ExceptionalCoefficients.tensor_unit_counit φ p)

private theorem closedComposite_counit
    {YA PA SA YB PB SB : Type*}
    [Category YA] [Category PA] [Category SA]
    [Category YB] [Category PB] [Category SB]
    {FA : PA ⥤ SA} {FB : PB ⥤ SB} {JA : YA ⥤ PA} {JB : YB ⥤ PB}
    {GA : SA ⥤ PA} {GB : SB ⥤ PB} {IA : PA ⥤ YA} {IB : PB ⥤ YB}
    (aP : FA ⊣ GA) (bP : FB ⊣ GB) (aI : JA ⊣ IA) (bI : JB ⊣ IB)
    (TY : YA ⥤ YB) (TP : PA ⥤ PB) (TS : SA ⥤ SB)
    (qP : FA ⋙ TS ≅ TP ⋙ FB) (qI : JA ⋙ TP ≅ TY ⋙ JB)
    (K : SA) (K' : SB) (unit : TS.obj K ⟶ K')
    (uP : TP.obj (GA.obj K) ⟶ GB.obj K')
    (b : TY.obj (IA.obj (GA.obj K)) ⟶ IB.obj (TP.obj (GA.obj K)))
    (hP : FB.map uP ≫ bP.counit.app K' =
      qP.inv.app (GA.obj K) ≫ TS.map (aP.counit.app K) ≫ unit)
    (hI : JB.map b ≫ bI.counit.app (TP.obj (GA.obj K)) =
      qI.inv.app (IA.obj (GA.obj K)) ≫ TP.map (aI.counit.app (GA.obj K))) :
    (JB ⋙ FB).map (b ≫ IB.map uP) ≫ (bI.comp bP).counit.app K' =
      (pasteIso qI qP).inv.app (IA.obj (GA.obj K)) ≫
        TS.map ((aI.comp aP).counit.app K) ≫ unit := by
  have hv := WeilConjectures.closedAssembly_counit aP bP aI bI TY TP TS
    qP.hom K K' unit (qI.hom.app (IA.obj (GA.obj K))) uP
    (by simpa only [NatIso.inv_hom_app] using hP) b
    (by simpa only [NatIso.inv_hom_app] using hI)
  apply (cancel_epi ((pasteIso qI qP).hom.app (IA.obj (GA.obj K)))).1
  simp only [Iso.hom_inv_id_app_assoc]
  simpa only [pasteIso_hom_app, Category.assoc] using hv

private theorem matePackages_transport
    {C P S C' P' S' : Type*}
    [Category C] [Category P] [Category S]
    [Category C'] [Category P'] [Category S']
    {LO : C ⥤ S} {RO : S ⥤ C} {LO' : C' ⥤ S'} {RO' : S' ⥤ C'}
    {FA : P ⥤ S} {GA : S ⥤ P} {FB : P' ⥤ S'} {GB : S' ⥤ P'}
    {JA : C ⥤ P} {IA : P ⥤ C} {JB : C' ⥤ P'} {IB : P' ⥤ C'}
    (aO : LO ⊣ RO) (bO : LO' ⊣ RO')
    (aP : FA ⊣ GA) (bP : FB ⊣ GB) (aI : JA ⊣ IA) (bI : JB ⊣ IB)
    (Q : C ⥤ C') (T : P ⥤ P') (R : S ⥤ S')
    (tA : LO ≅ JA ⋙ FA) (tB : LO' ≅ JB ⋙ FB)
    (qO : LO ⋙ R ≅ Q ⋙ LO') (qP : FA ⋙ R ≅ T ⋙ FB) (qI : JA ⋙ T ≅ Q ⋙ JB)
    (K : S) (K' : S') (unit : R.obj K ⟶ K')
    (uO : Q.obj (RO.obj K) ⟶ RO'.obj K')
    (uP : T.obj (GA.obj K) ⟶ GB.obj K')
    (dI : CoefficientCounitMateData aI bI Q T qI (GA.obj K))
    (hO : LO'.map uO ≫ bO.counit.app K' =
      qO.inv.app (RO.obj K) ≫ R.map (aO.counit.app K) ≫ unit)
    (hP : FB.map uP ≫ bP.counit.app K' =
      qP.inv.app (GA.obj K) ≫ R.map (aP.counit.app K) ≫ unit)
    (hc : R.map (tA.hom.app (RO.obj K)) ≫ (pasteIso qI qP).hom.app (RO.obj K) =
      qO.hom.app (RO.obj K) ≫ tB.hom.app (Q.obj (RO.obj K))) :
    ∃ (eA : RO.obj K ≅ (GA ⋙ IA).obj K) (eB : RO'.obj K' ≅ (GB ⋙ IB).obj K'),
      Q.map eA.hom ≫ (dI.hom ≫ IB.map uP) = uO ≫ eB.hom := by
  have hC := closedComposite_counit aP bP aI bI Q T R qP qI K K' unit
    uP dI.hom hP dI.counit
  exact counitMates_transport aO (aI.comp aP) bO (bI.comp bP) Q R
    tA tB qO (pasteIso qI qP) K K' unit uO (dI.hom ≫ IB.map uP) hO hC hc

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem open_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X) :
    (derivedExtension (A := B) j).map ((openScalarRestriction φ j).hom.app M) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j).counit.app ((scalarExtension φ X).obj M) =
      (ExceptionalCoefficients.openIso φ j).inv.app ((derivedRestriction j).obj M) ≫
        (scalarExtension φ X).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).counit.app M) := by
  apply (cancel_epi ((ExceptionalCoefficients.openIso φ j).hom.app
    ((derivedRestriction j).obj M))).1
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, compactScalarOpen_eq] using
    (etaleOpenTensorComparisons φ j).counit M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem openComposite_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X V S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [HasCompactification f] (j : V ⟶ X) [IsOpenImmersion j] :
    (derivedExtension (A := B) j ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        ((openScalarRestriction φ j).hom.app (dualizingComplex A f) ≫
          (derivedRestriction (A := B) j).map
            (ExceptionalCoefficients.dualizingScalarMap φ f)) ≫
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).comp
        (rightDerivedUpperShriekAdjunction B f)).counit.app
          (𝟙_ (DerivedCategoryModule B S)) =
      (pasteIso (ExceptionalCoefficients.openIso φ j)
        (ExceptionalCoefficients.chosenCompactSupportIso φ f)).inv.app
          ((derivedRestriction (A := A) j).obj (dualizingComplex A f)) ≫
        (scalarExtension φ S).map
          (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
            (rightDerivedUpperShriekAdjunction A f)).counit.app
              (𝟙_ (DerivedCategoryModule A S))) ≫ (ExceptionalCoefficients.unitIso φ S).hom := by
  exact closedComposite_counit
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction B f)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (scalarExtension φ V) (scalarExtension φ X) (scalarExtension φ S)
    (ExceptionalCoefficients.chosenCompactSupportIso φ f)
    (ExceptionalCoefficients.openIso φ j)
    (𝟙_ (DerivedCategoryModule A S)) (𝟙_ (DerivedCategoryModule B S))
    (ExceptionalCoefficients.unitIso φ S).hom
    (ExceptionalCoefficients.dualizingScalarMap φ f)
    ((openScalarRestriction φ j).hom.app (dualizingComplex A f))
    (structural_counit φ f) (open_counit φ j _)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Transport the open and closed counit mates across the compatible compact-support
factorizations. Source: the finite dualizing proof, paragraph 3
(blueprint: dualizing-open-closed-mate-normalization). -/
theorem closedOpen_dualizingMate_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X V P S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian V] [IsNoetherian P] [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : V ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p]
    (h : j ≫ f = i ≫ p)
    (hω : DerivedCategory.isBoundedConstructible A X
        (dualizingComplex A f) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b
        (dualizingComplex A f)) :
    ∃ (eA : (derivedRestriction (A := A) j).obj
          (dualizingComplex A f) ≅
        (rightDerivedUpperShriek A i).obj
          (dualizingComplex A p))
      (eB : (derivedRestriction (A := B) j).obj
          (dualizingComplex B f) ≅
        (rightDerivedUpperShriek B i).obj
          (dualizingComplex B p)),
      (openScalarRestriction φ j).hom.app (dualizingComplex A f) ≫
          (derivedRestriction (A := B) j).map
            (ExceptionalCoefficients.dualizingScalarMap φ f) ≫ eB.hom =
        (scalarExtension φ V).map eA.hom ≫
          closedDualizingCoefficientMate φ i (dualizingComplex A p) ≫
          (rightDerivedUpperShriek B i).map
            (ExceptionalCoefficients.dualizingScalarMap φ p) := by
  let GA := rightDerivedUpperShriek A f
  let HA := rightDerivedUpperShriek A p
  let aF := rightDerivedUpperShriekAdjunction A f
  let bF := rightDerivedUpperShriekAdjunction B f
  let aP := rightDerivedUpperShriekAdjunction A p
  let bP := rightDerivedUpperShriekAdjunction B p
  let aJ := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let bJ := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let aI := rightDerivedLowerStarUpperShriekAdjunctionOfIsProper A i
  let bI := rightDerivedLowerStarUpperShriekAdjunctionOfIsProper B i
  let qF := ExceptionalCoefficients.chosenCompactSupportIso φ f
  let qP := ExceptionalCoefficients.chosenCompactSupportIso φ p
  let qI := closedScalarIso φ i
  let qO := pasteIso (ExceptionalCoefficients.openIso φ j) qF
  let qC := pasteIso qI qP
  let K := 𝟙_ (DerivedCategoryModule A S)
  let K' := 𝟙_ (DerivedCategoryModule B S)
  let uO := (openScalarRestriction φ j).hom.app (GA.obj K) ≫
    (derivedRestriction (A := B) j).map (ExceptionalCoefficients.dualizingScalarMap φ f)
  -- Keep the constructed data abstract during kernel checking; hdI records its exact value.
  obtain ⟨dI, hdI⟩ :
      ∃ dI : CoefficientCounitMateData aI bI
          (scalarExtension φ V) (scalarExtension φ P) qI (HA.obj K),
        closedCoefficientMateData φ i (HA.obj K) = dI := ⟨_, rfl⟩
  obtain ⟨tA, tB, ht⟩ := openClosedCompactScalar_coherence φ f j i p h _ hω
  have hc : (scalarExtension φ S).map (tA.hom.app ((GA ⋙ derivedRestriction j).obj K)) ≫
      qC.hom.app ((GA ⋙ derivedRestriction j).obj K) =
      qO.hom.app ((GA ⋙ derivedRestriction j).obj K) ≫
        tB.hom.app ((scalarExtension φ V).obj ((GA ⋙ derivedRestriction j).obj K)) := by
    dsimp only [qC, qO]
    rw [pasteIso_hom_app, pasteIso_hom_app, closedScalarIso_hom_app]
    simp only [qF, qP, ExceptionalCoefficients.chosenCompactSupportIso_hom,
      Category.assoc]
    exact ht
  obtain ⟨eA, eB, he⟩ := matePackages_transport
    (aJ.comp aF) (bJ.comp bF) aP bP aI bI
    (scalarExtension φ V) (scalarExtension φ P) (scalarExtension φ S)
    tA tB qO qP qI K K' (ExceptionalCoefficients.unitIso φ S).hom
    uO (ExceptionalCoefficients.dualizingScalarMap φ p) dI
    (openComposite_counit φ f j) (structural_counit φ p) hc
  have he' := he.symm
  rw [← hdI] at he'
  refine ⟨eA, eB, ?_⟩
  simpa only [closedMate_eq, uO, GA, HA, K, K', constantComplex, dualizingComplex,
    Functor.comp_obj, Category.assoc] using he'
end AlgebraicGeometry.Etale
