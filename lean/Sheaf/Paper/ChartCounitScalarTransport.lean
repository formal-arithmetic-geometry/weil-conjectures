/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.PurEtaleScalarMateProjection
import Sheaf.Paper.EtaleCtfChartDomain
import Sheaf.Paper.ChartGeometricCounitEvaluation
import all Sheaf.SecSmoothPurity.ReductionExceptional
import all Sheaf.Paper.AffineCounitScalar
import Sheaf.Paper.RawChartScalarCounitPasting
import Sheaf.Paper.AffineCompactificationComparisonNormalization
import Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import all Sheaf.AlgebraicGeometry.ChartNormalizedModelIdentification
import all Sheaf.AlgebraicGeometry.ChartSumAffineCounitTransport
import Sheaf.Paper.EtaleCompactScalarCoherence
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness

/-! # Scalar compatibility of the specified chart counits

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts, retained Steps 7--11
(blueprint: lem-sp-chart-counit-scalar-transport).

The right comparison assembles the existing normalized tensor, pullback, shift
and root-line maps in the given order of affine coordinates.
The pro-etale comparison below is its conjugate through the specified site and
geometric comparisons, on every object, using the actual quasi-inverse counit.
The ring lift is exactly the presentation of the recorded pro-etale coefficient map.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.Etale.derivedTensor AlgebraicGeometry.Etale.upperStar
  AlgebraicGeometry.Etale.lowerStar
namespace AlgebraicGeometry.ProEtale.ChartFiniteRing
open AdjunctionTransfer CoefficientCompatibility


/-- The canonical scalar comparison for one ordered affine coordinate. Its root line
is supplied by the existing generator and derived-counit normalized comparison record.
Source: Charts, tensor/pullback and the normalized Tate line
(blueprint: lem-sp-chart-counit-scalar-transport). -/
def coordinateLineScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (L : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
      Etale.FiniteSmoothPurity.CoefficientLineComparison φ N N hA hB T)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (K : Etale.DerivedCategoryModule A S) :
    (Etale.scalarExtension φ (AffineSpace PUnit.{u + 1} S)).obj
        ((Etale.affineTraceLineRight A N hA S).obj K) ≅
      (Etale.affineTraceLineRight B N hB S).obj ((Etale.scalarExtension φ S).obj K) :=
  (Etale.scalarPullbackIso φ (ProjectiveLine.affineChart S)).symm.app _ ≪≫
    (Etale.ordinaryFinitePullback B (ProjectiveLine.affineChart S)).mapIso
      ((Etale.ExceptionalCoefficients.tensorIso φ (ProjectiveLine S)).app
          ((Etale.ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K,
            (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≪≫
        (Functor.uncurry.obj (Etale.ordinaryFiniteTensor B (ProjectiveLine S))).mapIso
          (Iso.prod ((Etale.scalarPullbackIso φ (ProjectiveLine S ↘ S)).symm.app K)
            ((Etale.FiniteSmoothPurity.scalarShiftIso φ (ProjectiveLine S) 2).app _ ≪≫
              (shiftFunctor _ (2 : ℤ)).mapIso
                (L (ProjectiveLine S) (affineTraceProjectiveInvertible N S hS)).derivedIso)))

/-- Iterate the actual scalar comparison in the given order of affine coordinates.
The zero-coordinate map is the identity, as is the recorded right tower.
Source: Charts, ordered affine integration
(blueprint: lem-sp-chart-counit-scalar-transport). -/
def coordinateAffineScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (L : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
      Etale.FiniteSmoothPurity.CoefficientLineComparison φ N N hA hB T)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (K : Etale.DerivedCategoryModule A S) →
      (Etale.scalarExtension φ (affineTraceTower S d)).obj
          ((Etale.affineTraceRight A N hA S d).obj K) ≅
        (Etale.affineTraceRight B N hB S d).obj ((Etale.scalarExtension φ S).obj K) :=
  Nat.rec (motive := fun n ↦ ∀ K : Etale.DerivedCategoryModule A S,
      (Etale.scalarExtension φ (affineTraceTower S n)).obj
          ((Etale.affineTraceRight A N hA S n).obj K) ≅
        (Etale.affineTraceRight B N hB S n).obj ((Etale.scalarExtension φ S).obj K))
    (fun _K ↦ Iso.refl _) (fun n ih K ↦
      coordinateLineScalarIso φ N hA hB L (affineTraceTower S n)
          (affineTraceInvertible N S hS n) ((Etale.affineTraceRight A N hA S n).obj K) ≪≫
        (Etale.affineTraceLineRight B N hB (affineTraceTower S n)).mapIso (ih K)) d

/-- The ordered affine scalar comparison followed by the exact etale pullback comparison.
These inputs retain the normalized root generators and all derived counit maps.
Source: Charts, the canonical comparison a_g
(blueprint: lem-sp-chart-counit-scalar-transport). -/
def coordinateChartScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (L : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
      Etale.FiniteSmoothPurity.CoefficientLineComparison φ N N hA hB T)
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ)
    (e : U ⟶ affineTraceTower Y d) (K : Etale.DerivedCategoryModule A Y) :
    (Etale.scalarExtension φ U).obj
        ((Etale.affineTraceRight A N hA Y d ⋙ Etale.ordinaryFinitePullback A e).obj K) ≅
      (Etale.affineTraceRight B N hB Y d ⋙ Etale.ordinaryFinitePullback B e).obj
        ((Etale.scalarExtension φ Y).obj K) :=
  (Etale.scalarPullbackIso φ e).symm.app _ ≪≫
    (Etale.ordinaryFinitePullback B e).mapIso
      (coordinateAffineScalarIso φ N hA hB L Y hY d K)


private theorem appendEvaluation
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {P Q R S : C} {X Y Z : D} (b : X ⟶ F.obj P)
    (d : P ⟶ Q) (a : Q ⟶ R) (v : R ⟶ S)
    (ε : F.obj S ⟶ Z) (t : F.obj R ⟶ Y) (q : Y ⟶ Z) (w : X ⟶ Y)
    (ht : b ≫ F.map d ≫ F.map a ≫ t = w)
    (hv : F.map v ≫ ε = t ≫ q) :
    b ≫ F.map (d ≫ a ≫ v) ≫ ε = w ≫ q := by
  simp only [F.map_comp, Category.assoc]
  rw [hv, reassoc_of% ht]

private theorem isoNormalizationCancel
    {C : Type*} [Category* C] {X Y Z : C} (g : X ≅ Y) (q : X ≅ Z)
    (v : Z ⟶ Y) (h : g.hom = q.hom ≫ v) :
    (g.symm ≪≫ q).hom ≫ v = 𝟙 Y := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← h, Iso.inv_hom_id]

private theorem coefficientTransportFinish
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (FA : C ⥤ D) (FB : E ⥤ F) (TU : C ⥤ E) (TY : D ⥤ F)
    (b : FA ⋙ TY ⟶ TU ⋙ FB)
    {W X : C} {Z : E} {K : D} (r : W ⟶ X) (a : TU.obj X ⟶ Z)
    (ua : FA.obj W ⟶ K) (ub : FB.obj Z ⟶ TY.obj K) (t : FA.obj X ⟶ K)
    (h : b.app X ≫ FB.map a ≫ ub = TY.map t)
    (hr : FA.map r ≫ t = ua) :
    b.app W ≫ FB.map (TU.map r ≫ a) ≫ ub = TY.map ua := by
  have hn := b.naturality r
  dsimp only [Functor.comp_map] at hn
  simp only [FB.map_comp, Category.assoc]
  rw [← reassoc_of% hn, h, ← TY.map_comp, hr]

private theorem evaluationPrecompose
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {W X : C} {Z : D} (r : W ⟶ X) (v : X ⟶ W)
    (s : F.obj W ⟶ Z) (t : F.obj X ⟶ Z)
    (hv : r ≫ v = 𝟙 W) (h : F.map v ≫ s = t) : F.map r ≫ t = s := by
  rw [← h, ← F.map_comp_assoc, hv, F.map_id, Category.id_comp]

private theorem coefficientCounitTransport
    {C : Type*} [Category C] {U V W D E P Q R S F : C}
    (e : U ≅ V) (c₀ : D ≅ Q) (c₁ : E ≅ R) (z : F ≅ S)
    {b : V ⟶ W} {d : W ⟶ D} {a : D ⟶ E} {δ : U ⟶ P}
    {β : P ⟶ Q} {a' : Q ⟶ R} {ε : R ⟶ S} {r : P ⟶ S} {t : U ⟶ F}
    (hs : e.hom ≫ b ≫ d = δ ≫ β ≫ c₀.inv)
    (hn : a ≫ c₁.hom = c₀.hom ≫ a')
    (hc : β ≫ a' ≫ ε = r) (hd : t ≫ z.hom = δ ≫ r) :
    b ≫ d ≫ a ≫ c₁.hom ≫ ε ≫ z.inv = e.inv ≫ t := by
  apply (cancel_epi e.hom).mp
  rw [reassoc_of% hs, reassoc_of% hn]
  simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% hc, ← reassoc_of% hd]
  simp

private theorem rawCounitTransport
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (S : C ⥤ D) (P : D ⥤ E) (F : C ⥤ E)
    (S' : C' ⥤ D') (P' : D' ⥤ E') (F' : C' ⥤ E')
    (TC : C ⥤ C') (TE : E ⥤ E')
    (b : F ⋙ TE ⟶ TC ⋙ F')
    (l : S ⋙ P ≅ F) (l' : S' ⋙ P' ≅ F')
    {X Y : C} {X' Y' : C'} {K : E}
    (r : Y ≅ X) (r' : Y' ≅ X')
    (a : TC.obj Y ⟶ Y') (a' : TC.obj X ⟶ X')
    (s : TE.obj (P.obj (S.obj X)) ⟶ P'.obj (S'.obj (TC.obj X)))
    (v : P.obj (S.obj X) ⟶ K) (v' : P'.obj (S'.obj X') ⟶ TE.obj K)
    (h : s ≫ P'.map (S'.map a') ≫ v' = TE.map v)
    (hl : TE.map (l.hom.app X) ≫ b.app X = s ≫ l'.hom.app (TC.obj X))
    (hr : a ≫ r'.hom = TC.map r.hom ≫ a') :
    b.app Y ≫ F'.map a ≫ F'.map r'.hom ≫ l'.inv.app X' ≫ v' =
      TE.map (F.map r.hom ≫ l.inv.app X ≫ v) := by
  rw [← F'.map_comp_assoc, hr]
  simp only [F'.map_comp, Category.assoc]
  have hn := b.naturality r.hom
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hn' := l'.inv.naturality a'
  dsimp only [Functor.comp_map] at hn'
  rw [reassoc_of% hn']
  have hi : b.app X ≫ l'.inv.app (TC.obj X) = TE.map (l.inv.app X) ≫ s := by
    apply (cancel_epi (TE.map (l.hom.app X))).1
    rw [reassoc_of% hl]
    simp only [← TE.map_comp_assoc,
      Iso.hom_inv_id_app, TE.map_id, Category.id_comp]
    exact Category.comp_id s
  rw [reassoc_of% hi, h]
  simp only [TE.map_comp]

private theorem scalarIsoPresentation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {X' Y' : D} (r : X ≅ Y) (s : X' ≅ Y') (a : F.obj X ≅ X') :
    a.hom ≫ s.hom = F.map r.hom ≫ (F.mapIso r.symm ≪≫ a ≪≫ s).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← F.map_comp_assoc, r.hom_inv_id, F.map_id, Category.id_comp]

private theorem scalarReplacement
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (S : C ⥤ D)
    (F' : C' ⥤ D') (G' : D' ⥤ E') (H' : C' ⥤ E') (S' : C' ⥤ D')
    (TC : C ⥤ C') (TD : D ⥤ D') (TE : E ⥤ E')
    (c : F ≅ S) (c' : F' ≅ S') (a : F ⋙ G ≅ H) (a' : F' ⋙ G' ≅ H')
    (bF : F ⋙ TD ⟶ TC ⋙ F') (bG : G ⋙ TE ⟶ TD ⋙ G')
    (bH : H ⋙ TE ⟶ TC ⋙ H') (s : S ⋙ TD ⟶ TC ⋙ S')
    (M : C)
    (hc : bF.app M ≫ c'.hom.app (TC.obj M) = TD.map (c.hom.app M) ≫ s.app M)
    (ha : TE.map (a.hom.app M) ≫ bH.app M =
      bG.app (F.obj M) ≫ G'.map (bF.app M) ≫ a'.hom.app (TC.obj M)) :
    TE.map (G.map (c.inv.app M) ≫ a.hom.app M) ≫ bH.app M =
      bG.app (S.obj M) ≫ G'.map (s.app M) ≫
        G'.map (c'.inv.app (TC.obj M)) ≫ a'.hom.app (TC.obj M) := by
  have hi : TD.map (c.inv.app M) ≫ bF.app M =
      s.app M ≫ c'.inv.app (TC.obj M) := by
    apply (cancel_mono (c'.hom.app (TC.obj M))).1
    simp only [Category.assoc, hc, ← TD.map_comp_assoc,
      Iso.inv_hom_id_app, TD.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  rw [TE.map_comp, Category.assoc, ha]
  have hn := bG.naturality (c.inv.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← G'.map_comp_assoc, hi, G'.map_comp, Category.assoc]

private def normalizedCoefficientLine
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    Etale.FiniteSmoothPurity.CoefficientLineComparison φ N N hA hB T := by
  have hi := reductionTateOrdinaryScalar_isIso φ T N hA hB
  exact {
    roots := 𝟙 _
    roots_power := by simp only [Category.id_comp, Nat.div_self hN, one_nsmul]
    sheafIso := asIso (((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
      (reductionEtaleTateMap φ T N hA hB))
    generators := by
      intro W a z
      simp only [asIso_hom, Equiv.apply_symm_apply]
      change (reductionEtaleTateMap φ T N hA hB).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
          Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a) z
      simpa only [reductionEtaleTateMap] using
        (reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose_spec W a z
    derivedIso := reductionEtaleTateIso φ T N hA hB hT
    derived_normalization := Eq.refl
      (WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T
          (Scheme.finiteEtaleTateLine T N A hA) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map
          (((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
            (reductionEtaleTateMap φ T N hA hB))) }

private theorem coordinateAffineScalarIso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : Etale.DerivedCategoryModule A S) :
    coordinateAffineScalarIso φ N hA hB (normalizedCoefficientLine φ N hN hA hB) S hS d K =
      reductionEtaleAffineScalarIso φ S N hA hB hS d K := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change coordinateLineScalarIso φ N hA hB (normalizedCoefficientLine φ N hN hA hB)
      (affineTraceTower S d) _ _ ≪≫
        (Etale.affineTraceLineRight B N hB (affineTraceTower S d)).mapIso
          (coordinateAffineScalarIso φ N hA hB
            (normalizedCoefficientLine φ N hN hA hB) S hS d K) = _
    rw [ih]
    rfl

attribute [local irreducible] normalizedCoefficientLine

set_option maxRecDepth 8192 in
private theorem chartAmbient_formula
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (M : Etale.EtaleCompactSupportNormalization R)
    {U V Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y]
    (e : U ⟶ V) (f : V ⟶ Y) [AlgebraicGeometry.Etale e] [IsSeparated e]
    [QuasiCompact e] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (ce : Compactification e) (cp : Compactification f)
    (cg : Compactification (e ≫ f)) (K : Etale.DerivedCategoryModule R U) :
    (Etale.etaleAmbientLeftComparison R M e f cp cg).hom.app K =
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cp).map
        ((M.comparison e ce).inv.app K) ≫ (etaleCompositor R ce cp cg).hom.app K := by
  let := ce.hasCompactification
  let := cp.hasCompactification
  let := cg.hasCompactification
  rw [← Etale.chart_comparison_ambient R M e f ce cp cg]
  simp only [Etale.chartNormalizedModelComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom]
  congr 1
  apply (cancel_mono ((Etale.rightDerivedLowerShriekIso R cg).hom.app K)).1
  change (Etale.ChartSumAffine.composition R ce cp cg).hom.app K ≫ _ = _
  rw [← Etale.ChartSumAffine.model_composition_to_chosen R e f ce cp cg K]
  simp only [etaleCompositor, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  simp

private theorem isoNaturalityCancel
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (c : F ≅ G) {X Y : C} (q : X ≅ Y) :
    F.map q.inv ≫ c.hom.app X ≫ G.map q.hom = c.hom.app Y := by
  have h := c.hom.naturality q.inv
  change F.map q.inv ≫ c.hom.app X = c.hom.app Y ≫ G.map q.inv at h
  rw [← Category.assoc, h, Category.assoc, ← G.map_comp,
    q.inv_hom_id, G.map_id, Category.comp_id]

private theorem counitComparisonNaturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (S : C ⥤ D) (A P : D ⥤ E) (F : C ⥤ E) (c : A ≅ P) (l : S ⋙ P ≅ F)
    {X X' : C} {Y : D} {Z : E} (r : X ≅ X') (v : S.obj X' ⟶ Y)
    (w : A.obj Y ⟶ Z) :
    l.inv.app X ≫ c.inv.app (S.obj X) ≫ A.map (S.map r.hom) ≫ A.map v ≫ w =
      F.map r.hom ≫ l.inv.app X' ≫ P.map v ≫ c.inv.app Y ≫ w := by
  have hn := c.inv.naturality (S.map r.hom ≫ v)
  change P.map (S.map r.hom ≫ v) ≫ c.inv.app Y =
    c.inv.app (S.obj X) ≫ A.map (S.map r.hom ≫ v) at hn
  have hl := l.inv.naturality r.hom
  change F.map r.hom ≫ l.inv.app X' = l.inv.app X ≫ P.map (S.map r.hom) at hl
  rw [← A.map_comp_assoc, ← reassoc_of% hn, P.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hl]

private theorem affineLeftOnPlus_eq
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (Y : Scheme.{u}) [IsNoetherian Y] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (d : ℕ) (cp : Compactification (affineTraceProjection Y d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower Y d).smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (affineLeftOnPlus R Y d cp).app M =
      (reductionEtaleAffineLeftIso R Y d cp).app M.obj := by
  apply Iso.ext
  with_unfolding_all
    simpa only [affineLeftOnPlus, Etale.orderedCompactificationComparison,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
      using (Etale.affineCompactificationComparison_normalization R k Y d cp M).symm

set_option maxRecDepth 8192 in
private theorem chartLeftOnPlus_eq
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (MA : Etale.EtaleCompactSupportNormalization R)
    {U Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian Y]
    [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e]
    [IsSeparated e] (cp : Compactification (affineTraceProjection Y d))
    (cg : Compactification (e ≫ affineTraceProjection Y d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    letI := affineTraceNoetherian Y d
    (chartLeftOnPlus R MA d e cp cg).app M =
      (reductionEtaleAffineLeftIso R Y d cp).app
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e
          inferInstance).mapDerivedCategory.obj M.obj) ≪≫
        (Etale.etaleAmbientLeftComparison R MA e (affineTraceProjection Y d) cp cg).app M.obj := by
  have := affineTraceNoetherian Y d
  apply Iso.ext
  let q := ((Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e
    inferInstance).mapDerivedCategoryPlusCompatibility).app M
  simp only [chartLeftOnPlus, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.symm_hom, Category.id_comp]
  rw [show (affineLeftOnPlus R Y d cp).hom.app
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e
        inferInstance).mapDerivedCategoryPlus.obj M) = _ from
    congrArg Iso.hom (affineLeftOnPlus_eq R k Y d cp _)]
  have hn := isoNaturalityCancel (reductionEtaleAffineLeftIso R Y d cp) q
  simpa only [q, Iso.app_hom, Iso.app_inv, Functor.comp_obj,
    ObjectProperty.ι_obj, Category.assoc] using congrArg
      (fun f ↦ f ≫ (Etale.etaleAmbientLeftComparison R MA e
        (affineTraceProjection Y d) cp cg).hom.app M.obj) hn

private theorem affineTraceAdjunction_unique
    (R : Type (u + 1)) [CommRing R] [Finite R] (N : ℕ) (hR : (N : R) = 0)
    (t t' : Etale.OrdinaryFiniteTwistTransport R N hR)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum R N hR t T hT)
    (D' : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum R N hR t' T hT)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    Etale.affineTraceAdjunction R N hR t D Y hY d =
      Etale.affineTraceAdjunction R N hR t' D' Y hY d := by
  obtain rfl := Etale.ordinaryFiniteTwistTransport_unique R N hR t t'
  have hD : D = D' := by
    funext T inst hT
    exact Etale.ordinaryFiniteP1Datum_unique R N hR _ T hT _ _
  subst D'
  rfl

variable {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
  (φ : A →+* B) {U Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian Y]
  (N : ℕ) (hA : (N : ULift.{u + 1, u} A) = 0) (hB : (N : ULift.{u + 1, u} B) = 0)
  (d : ℕ) (e : U ⟶ affineTraceTower Y d)
  [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
  (cp : Compactification (affineTraceProjection Y d))
  (cg : Compactification (e ≫ affineTraceProjection Y d))
  (MA : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} A))
  (tA : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} A) N hA)
  (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
    Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A) N hA tA T hT)
  (MB : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} B))
  (tB : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} B) N hB)
  (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
    Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} B) N hB tB T hT)
  (hY : IsUnit (N : Γ(Y, ⊤)))
  (CA : Datum (ULift.{u + 1, u} A) N hA d e cp cg MA tA PA hY)
  (CB : Datum (ULift.{u + 1, u} B) N hB d e cp cg MB tB PB hY)

private theorem datumCounit_raw
    (k : Type u) [Field k] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (K : (etaleProperty (ULift.{u + 1, u} A) Y).FullSubcategory) :
    letI := affineTraceNoetherian Y d
    (CA.adjEt.counit.app K).hom =
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cg).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e).hom.app
              ((Etale.affineTraceRight (ULift.{u + 1, u} A) N hA Y d).obj K.obj)) ≫
        (Etale.etaleAmbientLeftComparison (ULift.{u + 1, u} A) MA e
          (affineTraceProjection Y d) cp cg).inv.app
            ((Etale.rawChartRight (ULift.{u + 1, u} A) N hA d e).obj K.obj) ≫
        Etale.rawChartCounit N CA.positive (ULift.{u + 1, u} A) hA hY d e cp K.obj := by
  have := affineTraceNoetherian Y d
  let R := ULift.{u + 1, u} A
  let G := Etale.affineTraceRight R N hA Y d
  let E := (Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory
  let P := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cp
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg
  let l := Etale.etaleAmbientLeftComparison R MA e (affineTraceProjection Y d) cp cg
  let c := reductionEtaleAffineLeftIso R Y d cp
  let r := (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} R) e).app (G.obj K.obj)
  let v := (Etale.derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} R) e inferInstance).counit.app (G.obj K.obj)
  have ha := affineTraceAdjunction_unique R N hA tA
    (Etale.projectiveLineTraceTransport N CA.positive R hA) PA
    (Etale.projectiveLineTraceDatum N CA.positive R hA) Y hY d
  dsimp only [R] at ha
  rw [CA.etaleCounit, ha]
  have hleft := congrArg Iso.inv (chartLeftOnPlus_eq R k MA d e cp cg
    ((etaleToPlus R U).obj ((etaleRight R N hA d e CA.hRight).obj K)))
  simp only [Iso.app_inv] at hleft
  rw [hleft]
  simp only [Iso.trans_inv, Iso.app_inv, Adjunction.comp_counit_app]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  simp only [Etale.rawChartCounit, Etale.affineScalarCompactificationCounit, Iso.symm_inv]
  with_unfolding_all
    exact counitComparisonNaturality E (Etale.affineTraceLeft R Y d) P F c l r v
      ((Etale.affineTraceAdjunction R N hA
        (Etale.projectiveLineTraceTransport N CA.positive R hA)
        (Etale.projectiveLineTraceDatum N CA.positive R hA) Y hY d).counit.app K.obj)

include hA hB in
private theorem chartAmbient_scalar
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hne : ell ≠ pchar)
    (k : Type u) [Field k] [CharP k pchar] (n : ℕ) (hN : N = ell ^ n)
    [U.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (he : e ≫ affineTraceProjection Y d ≫ (Y ↘ Spec (.of k)) =
      (U ↘ Spec (.of k)))
    (K : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hK : etaleProperty (ULift.{u + 1, u} A) U K.obj) :
    letI := affineTraceNoetherian Y d
    (Etale.scalarExtension (uliftRingHom φ) Y).map
        ((Etale.etaleAmbientLeftComparison (ULift.{u + 1, u} A) MA e
          (affineTraceProjection Y d) cp cg).hom.app K.obj) ≫
        etaleCoefficientMap (uliftRingHom φ) cg K.obj =
      Etale.rawChartLeftScalarMap (uliftRingHom φ) d e cp K.obj ≫
        (Etale.etaleAmbientLeftComparison (ULift.{u + 1, u} B) MB e
          (affineTraceProjection Y d) cp cg).hom.app
            ((Etale.scalarExtension (uliftRingHom φ) U).obj K.obj) := by
  have := affineTraceNoetherian Y d
  let : (affineTraceTower Y d).Over (Spec (.of k)) :=
    ⟨affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (affineTraceTower Y d ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (affineTraceProjection Y d ≫ (Y ↘ Spec (.of k))))
  have : (affineTraceProjection Y d).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : e.IsOver (Spec (.of k)) := ⟨he⟩
  have := HasCompactification.of_isOver (S := Spec (.of k)) e
  let ce := HasCompactification.compactification e
  have hAA : ∃ m : ℕ, ∀ x : A, (ell ^ m) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    have hz : ((ell ^ n : ℕ) : A) = 0 := by
      have hzN : (N : A) = 0 := congrArg ULift.down hA
      simpa only [hN] using hzN
    rw [nsmul_eq_mul, hz, zero_mul]
  have hBB : ∃ m : ℕ, ∀ x : B, (ell ^ m) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    have hz : ((ell ^ n : ℕ) : B) = 0 := by
      have hzN : (N : B) = 0 := congrArg ULift.down hB
      simpa only [hN] using hzN
    rw [nsmul_eq_mul, hz, zero_mul]
  have hAA' : ∃ m : ℕ, ∀ x : ULift.{u + 1, u} A, (ell ^ m) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    rw [nsmul_eq_mul, show ((ell ^ n : ℕ) : ULift.{u + 1, u} A) = 0 by
      simpa only [← hN] using hA, zero_mul]
  have hBB' : ∃ m : ℕ, ∀ x : ULift.{u + 1, u} B, (ell ^ m) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    rw [nsmul_eq_mul, show ((ell ^ n : ℕ) : ULift.{u + 1, u} B) = 0 by
      simpa only [← hN] using hB, zero_mul]
  have hc := etaleProEtaleCoefficientCompatibility_sum ell pchar hp hne.symm k
    hAA' hBB' (uliftRingHom φ) e ce MA MB K.obj hK
  obtain ⟨_, ha, _⟩ := etaleProEtaleCoefficientCompatibility_composition
    ell pchar hp hne.symm k hAA hBB φ e (affineTraceProjection Y d) ce cp cg K hK
  have h := scalarReplacement
    _ _ _ _ _ _ _ _ (Etale.scalarExtension (uliftRingHom φ) U)
    (Etale.scalarExtension (uliftRingHom φ) (affineTraceTower Y d))
    (Etale.scalarExtension (uliftRingHom φ) Y)
    (MA.comparison e ce) (MB.comparison e ce)
    (etaleCompositor (ULift.{u + 1, u} A) ce cp cg)
    (etaleCompositor (ULift.{u + 1, u} B) ce cp cg)
    (Etale.compactScalarMap (uliftRingHom φ) ce)
    (Etale.compactScalarMap (uliftRingHom φ) cp)
    (Etale.compactScalarMap (uliftRingHom φ) cg)
    (sumCoefficientIso (uliftRingHom φ) e).hom K.obj
    (by simpa only [normalizedSumComparison, Etale.coefficient_map_eq] using hc)
    (by simpa only [Etale.coefficient_map_eq] using ha)
  rw [chartAmbient_formula _ MA e (affineTraceProjection Y d) ce cp cg,
    chartAmbient_formula _ MB e (affineTraceProjection Y d) ce cp cg]
  simpa only [Etale.rawChartLeftScalarMap, Etale.coefficient_map_eq, Category.assoc]
    using h

/-- The counit on the explicit geometric pro-etale chart functor. This is the
specified transported counit precomposed with the inverse geometric identification.
Source: Charts, actual transported counit
(blueprint: lem-sp-chart-counit-scalar-transport). -/
def geometricCounit
    (K : (proEtaleProperty (ULift.{u + 1, u} A) Y).FullSubcategory) :=
  (proEtaleLowerShriek (ULift.{u + 1, u} A) cg CA.hPro).map
      (CA.geometric.inv.app K) ≫ CA.adjPro.counit.app K

/-- Canonical scalar transport of the geometric chart right functor. Start with
CA.geometric inverse, identify its comparison functor by CA.heU, then use the actual
scalar/site map, the root-normalized ordered etale scalar map, CB's coordinate/site
normalization, the inverse scalar/site map on Y, and CA.eY's counit.
Source: Charts, tensor/pullback, shift, Tate and site comparison
(blueprint: lem-sp-chart-counit-scalar-transport). -/
def geometricScalarIso
    (L : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
      Etale.FiniteSmoothPurity.CoefficientLineComparison (uliftRingHom φ) N N hA hB T)
    (K : (proEtaleProperty (ULift.{u + 1, u} A) Y).FullSubcategory) :
    (liftedScalarExtension φ U).obj
        ((geometricRight (ULift.{u + 1, u} A) N hA d e).obj K.obj) ≅
      (geometricRight (ULift.{u + 1, u} B) N hB d e).obj
        ((liftedScalarExtension φ Y).obj K.obj) :=
  (liftedScalarExtension φ U).mapIso
      (((proEtaleProperty (ULift.{u + 1, u} A) U).ι.mapIso
          (CA.geometric.app K)).symm ≪≫
        eqToIso (congrArg (fun F ↦
          (F.obj ((etaleRight (ULift.{u + 1, u} A) N hA d e CA.hRight).obj
            (CA.eY.inverse.obj K))).obj) CA.heU)) ≪≫
    (pbcComparisonReduction U (uliftRingHom φ)).app
      ((etaleRight (ULift.{u + 1, u} A) N hA d e CA.hRight).obj
        (CA.eY.inverse.obj K)).obj ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U).mapDerivedCategory.mapIso
      (coordinateChartScalarIso (uliftRingHom φ) N hA hB L hY d e
        (CA.eY.inverse.obj K).obj) ≪≫
    chartGeometryComponent (ULift.{u + 1, u} B) N CB.positive hB CB.flatTwist hY d e
      ((Etale.scalarExtension (uliftRingHom φ) Y).obj (CA.eY.inverse.obj K).obj) ≪≫
    (geometricRight (ULift.{u + 1, u} B) N hB d e).mapIso
      (((pbcComparisonReduction Y (uliftRingHom φ)).app (CA.eY.inverse.obj K).obj).symm ≪≫
        (liftedScalarExtension φ Y).mapIso
          (eqToIso (congrArg (fun F ↦ (F.obj (CA.eY.inverse.obj K)).obj) CA.heY.symm) ≪≫
            (proEtaleProperty (ULift.{u + 1, u} A) Y).ι.mapIso (CA.eY.counitIso.app K)))

set_option maxRecDepth 8192 in
/-- The actual etale chart counit commutes with arbitrary finite coefficient change.
The witnesses only put the actual scalar-extended input in the existing full domain.
Source: Charts, retained Steps 7--11
(blueprint: lem-sp-chart-counit-scalar-transport).

Proof:
1. lem-sp-raw-chart-scalar-counit-pasting pastes the sum coefficient-counit identity
   and the ordered affine identity. The right map factors as inverse-image scalar
   comparison followed by pullback of the affine comparison, with the specified
   Tate generator normalization. It yields the raw sum-then-affine equation.
2. The sum and composition squares of lem-sp-et-proet-coefficient-compatibility
   give the coefficient square for the graph-normalized ambient left comparison.
   Normalize the affine comparison on D+ and identify the supplied projective-line
   data with the canonical data by uniqueness. Datum.etaleCounit becomes the raw
   counit precomposed with the inverse left comparison and exact/derived pullback.
3. Naturality moves the pullback identification through the coefficient map. The
   left coefficient square and inverse cancellation reduce the equation to Step 1.
   The compactifications cp and cg are arbitrary throughout, so their canonical
   refinement identifications are already included. No exceptional coefficient map
   is assumed invertible, and no orientation is chosen. -/
theorem chartCounitScalarTransport_etale
    (ell pchar : ℕ) [Fact ell.Prime] (_hp : 0 < pchar) (_hne : ell ≠ pchar)
    (k : Type u) [Field k] [CharP k pchar] (n : ℕ) (_hN : N = ell ^ n)
    [U.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (_he : e ≫ affineTraceProjection Y d ≫ (Y ↘ Spec (.of k)) =
      (U ↘ Spec (.of k))) :
    ∃ L : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
        Etale.FiniteSmoothPurity.CoefficientLineComparison (uliftRingHom φ) N N hA hB T,
    ∃ hScalar : ∀ K, etaleProperty (ULift.{u + 1, u} A) Y K →
        etaleProperty (ULift.{u + 1, u} B) Y
          ((Etale.scalarExtension (uliftRingHom φ) Y).obj K),
      ∀ K : (etaleProperty (ULift.{u + 1, u} A) Y).FullSubcategory,
        etaleCoefficientMap (uliftRingHom φ) cg
            ((etaleRight (ULift.{u + 1, u} A) N hA d e CA.hRight).obj K).obj ≫
          (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) cg).map
            (coordinateChartScalarIso (uliftRingHom φ) N hA hB L hY d e K.obj).hom ≫
          (CB.adjEt.counit.app
            ⟨(Etale.scalarExtension (uliftRingHom φ) Y).obj K.obj,
              hScalar K.obj K.property⟩).hom =
        (Etale.scalarExtension (uliftRingHom φ) Y).map (CA.adjEt.counit.app K).hom := by
  subst N
  have := affineTraceNoetherian Y d
  have hpos : 0 < ell ^ n := pow_pos (Fact.out : ell.Prime).pos n
  let L := normalizedCoefficientLine (uliftRingHom φ) (ell ^ n) hpos hA hB
  obtain ⟨hNoeth, hY', hr, hc, hGA, hhA, hEA, hPA, hGB, hhB, hEB, hPB,
      hS, hSV, hSU⟩ := Etale.rawChartScalarCounitPasting ell pchar _hp _hne.symm
    k (uliftRingHom φ) n hA hB d e _he cp
  refine Exists.intro L ?_
  refine Exists.intro hS ?_
  intro K
  let KB : (etaleProperty (ULift.{u + 1, u} B) Y).FullSubcategory :=
    ⟨(Etale.scalarExtension (uliftRingHom φ) Y).obj K.obj, hS K.obj K.property⟩
  let rA := (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e).app
      ((Etale.affineTraceRight (ULift.{u + 1, u} A) (ell ^ n) hA Y d).obj K.obj)
  let rB := (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) e).app
      ((Etale.affineTraceRight (ULift.{u + 1, u} B) (ell ^ n) hB Y d).obj KB.obj)
  let a := coordinateChartScalarIso (uliftRingHom φ) (ell ^ n) hA hB L hY d e K.obj
  let ar := Etale.rawChartScalarIso (uliftRingHom φ) (ell ^ n) hA hB hY d e K.obj
  have ha : a.hom ≫ rB.hom =
      (Etale.scalarExtension (uliftRingHom φ) U).map rA.hom ≫ ar.hom := by
    have hcoord : a = reductionEtaleChartScalarIso (uliftRingHom φ)
        (ell ^ n) hA hB hY d e K.obj := by
      dsimp only [a, coordinateChartScalarIso, reductionEtaleChartScalarIso]
      rw [coordinateAffineScalarIso_eq]
    rw [hcoord]
    dsimp only [ar, Etale.rawChartScalarIso]
    with_unfolding_all
      exact scalarIsoPresentation (Etale.scalarExtension (uliftRingHom φ) U) rA rB
        (reductionEtaleChartScalarIso (uliftRingHom φ) (ell ^ n) hA hB hY d e K.obj)
  -- The exact chart right value lies in the finite-Tor domain.
  let X := (Etale.rawChartRight (ULift.{u + 1, u} A) (ell ^ n) hA d e).obj K.obj
  have hX : etaleProperty (ULift.{u + 1, u} A) U X :=
    hhA _ (hGA _ K.property)
  have hXplus : _root_.DerivedCategory.TStructure.t.plus X :=
    ((etaleToPlus (ULift.{u + 1, u} A) U).obj ⟨X, hX⟩).property
  have hl := chartAmbient_scalar φ (ell ^ n) hA hB d e cp cg MA MB
    ell pchar _hp _hne k n rfl _he ⟨X, hXplus⟩ hX
  have hraw := rawCounitTransport
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e
      inferInstance).mapDerivedCategory
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cp)
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cg)
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) e
      inferInstance).mapDerivedCategory
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) cp)
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) cg)
    (Etale.scalarExtension (uliftRingHom φ) U)
    (Etale.scalarExtension (uliftRingHom φ) Y)
    (Etale.compactScalarMap (uliftRingHom φ) cg)
    (Etale.etaleAmbientLeftComparison (ULift.{u + 1, u} A) MA e
      (affineTraceProjection Y d) cp cg)
    (Etale.etaleAmbientLeftComparison (ULift.{u + 1, u} B) MB e
      (affineTraceProjection Y d) cp cg)
    rA rB a.hom ar.hom (Etale.rawChartLeftScalarMap (uliftRingHom φ) d e cp X)
    (Etale.rawChartCounit (ell ^ n) hpos (ULift.{u + 1, u} A) hA hY d e cp K.obj)
    (Etale.rawChartCounit (ell ^ n) hpos (ULift.{u + 1, u} B) hB hY d e cp KB.obj)
    (hc K.obj K.property) (by
      with_unfolding_all
        simpa only [Etale.coefficient_map_eq, X, Etale.rawChartRight, Functor.comp_obj]
          using hl) ha
  rw [datumCounit_raw (N := ell ^ n) hB d e cp cg MB tB PB hY CB k KB,
    datumCounit_raw (N := ell ^ n) hA d e cp cg MA tA PA hY CA k K]
  with_unfolding_all
    simpa only [Etale.coefficient_map_eq, a, KB, rA, rB, etaleRight,
      Etale.ordinaryFinitePullback, Etale.rawChartRight, Functor.comp_obj,
      ObjectProperty.lift, ObjectProperty.ι_obj, Functor.id_obj, Iso.app_hom,
      Category.assoc] using hraw

/-- The scalar counit equation on every pro-etale finite-Tor constructible input,
for the explicit geometric right functor and the specified fixed coefficient map.
Source: Charts, retained Steps 7--11
(blueprint: lem-sp-chart-counit-scalar-transport).

Proof:
1. Apply chartCounitScalarTransport_etale at the specified inverse comparison image
   J=CA.eY.inverse(K). The chart-domain theorem supplies both scalar-domain witnesses.
2. The coefficient/site square, naturality of the B compact-support comparison at
   the coordinate scalar map, and naturality of the scalar/site comparison at the
   A counit give the corresponding equation on the comparison images.
3. chartGeometricCounitEvaluation identifies both geometric counits using the actual
   endpoint isomorphisms from CA.eY's counit and the scalar/site comparison.
4. Datum.geometric_normalization cancels the A geometric identification. Naturality
   of the pro-etale coefficient map moves that identification through the square.
   The resulting right comparison is exactly geometricScalarIso. The supplied
   compactifications remain arbitrary, with their canonical comparisons. -/
theorem chartCounitScalarTransport
    (ell pchar : ℕ) [Fact ell.Prime] (_hp : 0 < pchar) (_hne : ell ≠ pchar)
    (k : Type u) [Field k] [CharP k pchar] (n : ℕ) (_hN : N = ell ^ n)
    [U.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (_he : e ≫ affineTraceProjection Y d ≫ (Y ↘ Spec (.of k)) =
      (U ↘ Spec (.of k))) :
    ∃ L : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
        Etale.FiniteSmoothPurity.CoefficientLineComparison (uliftRingHom φ) N N hA hB T,
    ∃ hScalar : ∀ K, proEtaleProperty (ULift.{u + 1, u} A) Y K →
        proEtaleProperty (ULift.{u + 1, u} B) Y ((liftedScalarExtension φ Y).obj K),
      ∀ K : (proEtaleProperty (ULift.{u + 1, u} A) Y).FullSubcategory,
        (proEtaleCoefficientMap φ cg).app
            ((geometricRight (ULift.{u + 1, u} A) N hA d e).obj K.obj) ≫
          (rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) cg).map
            (geometricScalarIso φ N hA hB d e cp cg MA tA PA MB tB PB hY CA CB L K).hom ≫
          (geometricCounit N hB d e cp cg MB tB PB hY CB
            ⟨(liftedScalarExtension φ Y).obj K.obj, hScalar K.obj K.property⟩).hom =
        (liftedScalarExtension φ Y).map
          (geometricCounit N hA d e cp cg MA tA PA hY CA K).hom := by
  obtain ⟨L, hSE, hE⟩ := chartCounitScalarTransport_etale φ N hA hB d e cp cg
    MA tA PA MB tB PB hY CA CB ell pchar _hp _hne k n _hN _he
  have : Fact (ringChar k).Prime := ⟨by
    rw [ringChar.eq k pchar]
    exact (CharP.char_is_prime_or_zero k pchar).resolve_right (Nat.ne_of_gt _hp)⟩
  have : Fact (ringChar k ≠ ell) := ⟨by
    rw [ringChar.eq k pchar]
    exact _hne.symm⟩
  have hSA : ((ell ^ n : ℕ) : ULift.{u + 1, u} A) = 0 := by
    simpa only [← _hN] using hA
  have hSB : ((ell ^ n : ℕ) : ULift.{u + 1, u} B) = 0 := by
    simpa only [← _hN] using hB
  have hS := (etaleCtfChartScalarDomain ell k (uliftRingHom φ) n hSA hSB Y).2
  refine ⟨L, hS, ?_⟩
  intro K
  let J := CA.eY.inverse.obj K
  let JA := (etaleRight (ULift.{u + 1, u} A) N hA d e CA.hRight).obj J
  let JB : (etaleProperty (ULift.{u + 1, u} B) Y).FullSubcategory :=
    ⟨(Etale.scalarExtension (uliftRingHom φ) Y).obj J.obj, hSE J.obj J.property⟩
  let HB := (etaleRight (ULift.{u + 1, u} B) N hB d e CB.hRight).obj JB
  let LA := (etaleToPlus (ULift.{u + 1, u} A) U).obj JA
  let LB := (etaleToPlus (ULift.{u + 1, u} B) U).obj HB
  have : (e ≫ affineTraceProjection Y d).IsOver (Spec (.of k)) := ⟨_he⟩
  have hAnnA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    have hz : ((ell ^ n : ℕ) : A) = 0 := congrArg ULift.down hSA
    rw [nsmul_eq_mul, hz, zero_mul]
  have hAnnB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    have hz : ((ell ^ n : ℕ) : B) = 0 := congrArg ULift.down hSB
    rw [nsmul_eq_mul, hz, zero_mul]
  obtain ⟨hLB, _, _, hs⟩ := etaleProEtaleCoefficientCompatibility ell pchar _hp
    _hne.symm k hAnnA hAnnB φ (e ≫ affineTraceProjection Y d) cg LA JA.property
  let LB' : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨(Etale.scalarExtension (uliftRingHom φ) U).obj JA.obj, hLB⟩
  let a := coordinateChartScalarIso (uliftRingHom φ) N hA hB L hY d e J.obj
  have hn := (compactSupportSiteComparison (ULift.{u + 1, u} B) cg).hom.naturality
    (ObjectProperty.homMk a.hom : LB' ⟶ LB)
  dsimp only [Functor.comp_map] at hn
  have hc := congrArg
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map) (hE J)
  simp only [Functor.map_comp] at hc
  have hd := (pbcComparisonReduction Y (uliftRingHom φ)).hom.naturality
    (CA.adjEt.counit.app J).hom
  dsimp only [Functor.comp_map] at hd
  have ht := coefficientCounitTransport
    ((liftedScalarExtension φ Y).mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) cg).app LA).symm)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) cg).app LB')
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) cg).app LB)
    ((pbcComparisonReduction Y (uliftRingHom φ)).app J.obj) hs hn hc hd
  let aA : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      Y).mapDerivedCategory.obj J.obj ≅ K.obj :=
    eqToIso (congrArg (fun F ↦ (F.obj J).obj) CA.heY.symm) ≪≫
      (proEtaleProperty (ULift.{u + 1, u} A) Y).ι.mapIso (CA.eY.counitIso.app K)
  let aB := ((pbcComparisonReduction Y (uliftRingHom φ)).app J.obj).symm ≪≫
    (liftedScalarExtension φ Y).mapIso aA
  let rA : (geometricRight (ULift.{u + 1, u} A) N hA d e).obj K.obj ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        U).mapDerivedCategory.obj JA.obj := ((proEtaleProperty (ULift.{u + 1, u} A) U).ι.mapIso
      (CA.geometric.app K)).symm ≪≫
    eqToIso (congrArg (fun F ↦ (F.obj JA).obj) CA.heU)
  let vA := (chartGeometryComponent (ULift.{u + 1, u} A) N CA.positive hA CA.flatTwist
    hY d e J.obj).hom ≫ (geometricRight (ULift.{u + 1, u} A) N hA d e).map aA.hom
  let vB := (chartGeometryComponent (ULift.{u + 1, u} B) N CB.positive hB CB.flatTwist
    hY d e JB.obj).hom ≫ (geometricRight (ULift.{u + 1, u} B) N hB d e).map aB.hom
  have evA := chartGeometricCounitEvaluation (ULift.{u + 1, u} A) N hA d e cp cg
    MA tA PA hY CA J K aA
  have evB := chartGeometricCounitEvaluation (ULift.{u + 1, u} B) N hB d e cp cg
    MB tB PB hY CB JB
    ⟨(liftedScalarExtension φ Y).obj K.obj, hS K.obj K.property⟩ aB
  have hvA : rA.hom ≫ vA = 𝟙 _ := by
    with_unfolding_all
      apply isoNormalizationCancel
        ((proEtaleProperty (ULift.{u + 1, u} A) U).ι.mapIso (CA.geometric.app K))
        (eqToIso (congrArg (fun F ↦ (F.obj JA).obj) CA.heU)) vA
      simpa only [vA, aA, J, JA, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom,
        Iso.app_hom, Functor.map_comp, ObjectProperty.ι_map,
        ObjectProperty.ι_obj, Category.assoc] using CA.geometric_normalization K
  have har :
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cg).map rA.hom ≫
        (compactSupportSiteComparison (ULift.{u + 1, u} A) cg).hom.app LA ≫
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          Y).mapDerivedCategory.map (CA.adjEt.counit.app J).hom ≫ aA.hom =
      (geometricCounit N hA d e cp cg MA tA PA hY CA K).hom := by
    apply evaluationPrecompose _ rA.hom vA _ _ hvA
    exact evA
  have hg : (geometricScalarIso φ N hA hB d e cp cg MA tA PA MB tB PB hY
      CA CB L K).hom =
      (liftedScalarExtension φ U).map rA.hom ≫
        (pbcComparisonReduction U (uliftRingHom φ)).hom.app JA.obj ≫
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
          U).mapDerivedCategory.map a.hom ≫ vB := by
    simp only [geometricScalarIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.symm_hom]
    rfl
  have evB' : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) cg).map vB ≫
      (geometricCounit N hB d e cp cg MB tB PB hY CB
        ⟨(liftedScalarExtension φ Y).obj K.obj, hS K.obj K.property⟩).hom =
      (compactSupportSiteComparison (ULift.{u + 1, u} B) cg).hom.app LB ≫
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
          Y).mapDerivedCategory.map (CB.adjEt.counit.app JB).hom ≫ aB.hom := evB
  have hEnd : (proEtaleCoefficientMap φ cg).app
      ((comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).mapDerivedCategory.obj JA.obj) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) cg).map
        ((pbcComparisonReduction U (uliftRingHom φ)).hom.app JA.obj ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
            U).mapDerivedCategory.map a.hom ≫ vB) ≫
      (geometricCounit N hB d e cp cg MB tB PB hY CB
        ⟨(liftedScalarExtension φ Y).obj K.obj, hS K.obj K.property⟩).hom =
      (liftedScalarExtension φ Y).map
        ((compactSupportSiteComparison (ULift.{u + 1, u} A) cg).hom.app LA ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            Y).mapDerivedCategory.map (CA.adjEt.counit.app J).hom ≫ aA.hom) := by
    conv_rhs => rw [← Category.assoc, Functor.map_comp]
    apply appendEvaluation
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) cg) _ _ _ vB _
      ((compactSupportSiteComparison (ULift.{u + 1, u} B) cg).hom.app LB ≫
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
          Y).mapDerivedCategory.map (CB.adjEt.counit.app JB).hom ≫
        ((pbcComparisonReduction Y (uliftRingHom φ)).app J.obj).inv)
      ((liftedScalarExtension φ Y).map aA.hom)
    · with_unfolding_all
        simpa only [LA, JB, etaleToPlus, ObjectProperty.ιOfLE_obj_obj,
          Functor.comp_obj, ObjectProperty.ι_obj, liftedScalarExtension,
          Functor.mapIso_inv, Iso.symm_inv, Iso.app_hom,
          Functor.map_comp, Functor.comp_map, ObjectProperty.ι_map,
          ObjectProperty.homMk_hom, Category.assoc] using ht
    · simpa only [aB, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
        Functor.mapIso_hom, Category.assoc] using evB'
  rw [hg]
  exact coefficientTransportFinish
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cg)
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) cg)
    (liftedScalarExtension φ U) (liftedScalarExtension φ Y)
    (proEtaleCoefficientMap φ cg) rA.hom _ _ _ _ hEnd har

end AlgebraicGeometry.ProEtale.ChartFiniteRing
