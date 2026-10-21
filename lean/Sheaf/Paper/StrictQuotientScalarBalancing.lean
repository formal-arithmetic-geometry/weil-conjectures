/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.StrictQuotientScalarBalancingData
import Sheaf.Paper.StrictQuotientPullbackCompatibility
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat

/-! # Augmented strict scalar balancing

Source: completed-exchange-coherence, strict coefficient supplement, steps 1--7.
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.StrictScalarBalancing
open CategoryTheory.ConstantCompletion
variable {A : Type (u + 1)} [CommRing A]

private theorem exact_square
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category A₄] [Category A₅] [Category A₆] [Category A₇]
    {qB : A₀ ⥤ A₄} {qR : A₁ ⥤ A₅} {tqB : A₂ ⥤ A₆} {tqR : A₃ ⥤ A₇}
    {rc : A₀ ⥤ A₁} {tc : A₂ ⥤ A₃} {dr : A₄ ⥤ A₅} {dt : A₆ ⥤ A₇}
    {tr : A₅ ⥤ A₇} {tb : A₄ ⥤ A₆} {redR : A₁ ⥤ A₃} {redB : A₀ ⥤ A₂}
    (W : MorphismProperty A₀) [qB.IsLocalization W]
    (α : rc ⋙ qR ≅ qB ⋙ dr) (βR : qR ⋙ tr ≅ redR ⋙ tqR)
    (γ : rc ⋙ redR ≅ redB ⋙ tc) (δ : tc ⋙ tqR ≅ tqB ⋙ dt)
    (βB : qB ⋙ tb ≅ redB ⋙ tqB) :
    ∃ e : dr ⋙ tr ≅ tb ⋙ dt,
      ∀ P : A₀, DerivedTowerComparisonFormula α βR.hom γ δ βB.hom e P := by
  let c : qB ⋙ (dr ⋙ tr) ≅ qB ⋙ (tb ⋙ dt) :=
    Functor.isoWhiskerRight α.symm tr ≪≫ Functor.isoWhiskerLeft rc βR ≪≫
      Functor.isoWhiskerRight γ tqR ≪≫ Functor.isoWhiskerLeft redB δ ≪≫
      Functor.isoWhiskerRight βB.symm dt
  let e := Localization.liftNatIso qB W _ _ (dr ⋙ tr) (tb ⋙ dt) c
  refine ⟨e, ?_⟩
  intro P
  have he : e.hom.app (qB.obj P) = c.hom.app P := by
    simp [e, Localization.liftNatIso, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft]
  unfold DerivedTowerComparisonFormula
  rw [he]
  simp only [c, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← dt.map_comp, Iso.inv_hom_id_app, dt.map_id]
  erw [Category.comp_id]


private theorem deltaRestriction_exists (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    ∃ δ : delta T d true ⋙ tdres (scalar T d) ≅
        dres (scalar T d) ⋙ delta T d false, DeltaRestrictionComputes T d δ := by
  let := HasDerivedCategory.standard (Mod (ring T d true))
  have : (Q (ring T d true)).IsLocalization
      (HomologicalComplex.quasiIso (Mod (ring T d true)) (.up ℤ)) :=
    inferInstanceAs ((DerivedCategory.Q (C := Mod (ring T d true))).IsLocalization
      (HomologicalComplex.quasiIso (Mod (ring T d true)) (.up ℤ)))
  obtain ⟨e, he⟩ := exact_square
    (HomologicalComplex.quasiIso (Mod (ring T d true)) (.up ℤ))
    (resFactors (scalar T d)) (deltaFactors T d false)
    (constantRestrictionComplex T d) (tresFactors (scalar T d)) (deltaFactors T d true)
  exact ⟨e.symm, he⟩

private theorem augmentation_square
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category A₄] [Category A₅] [Category A₆] [Category A₇]
    {qB : A₀ ⥤ A₄} {qR : A₁ ⥤ A₅} {tqB : A₂ ⥤ A₆} {tqR : A₃ ⥤ A₇}
    {rc : A₀ ⥤ A₁} {tc : A₂ ⥤ A₃} {dr : A₄ ⥤ A₅} {dt : A₆ ⥤ A₇}
    {tr : A₅ ⥤ A₇} {tb : A₄ ⥤ A₆} {redR : A₁ ⥤ A₃} {redB : A₀ ⥤ A₂}
    {dgR : A₅ ⥤ A₇} {dgB : A₄ ⥤ A₆} {ctR : A₁ ⥤ A₃} {ctB : A₀ ⥤ A₂}
    (α : rc ⋙ qR ≅ qB ⋙ dr) (βR : qR ⋙ tr ⟶ redR ⋙ tqR)
    (γ : rc ⋙ redR ≅ redB ⋙ tc) (δ : tc ⋙ tqR ≅ tqB ⋙ dt)
    (βB : qB ⋙ tb ⟶ redB ⋙ tqB)
    (zR : qR ⋙ dgR ≅ ctR ⋙ tqR) (zB : qB ⋙ dgB ≅ ctB ⋙ tqB)
    (ζ : rc ⋙ ctR ≅ ctB ⋙ tc)
    (uR : ctR ⟶ redR) (uB : ctB ⟶ redB)
    (ηR : dgR ⟶ tr) (ηB : dgB ⟶ tb)
    (ρ : tb ⋙ dt ≅ dr ⋙ tr) (δ₀ : dgB ⋙ dt ≅ dr ⋙ dgR)
    (P : A₀) [IsIso (βB.app P)]
    (hρ : DerivedTowerComparisonFormula α βR γ δ βB ρ.symm P)
    (hδ : DerivedTowerComparisonFormula α zR.hom ζ δ zB.hom δ₀.symm P)
    (hR : ηR.app (qR.obj (rc.obj P)) ≫ βR.app (rc.obj P) =
      zR.hom.app (rc.obj P) ≫ tqR.map (uR.app (rc.obj P)))
    (hB : ηB.app (qB.obj P) ≫ βB.app P =
      zB.hom.app P ≫ tqB.map (uB.app P))
    (hunit : uR.app (rc.obj P) ≫ γ.hom.app P =
      ζ.hom.app P ≫ tc.map (uB.app P)) :
    dt.map (ηB.app (qB.obj P)) ≫ ρ.hom.app (qB.obj P) =
      δ₀.hom.app (qB.obj P) ≫ ηR.app (dr.obj (qB.obj P)) := by
  unfold DerivedTowerComparisonFormula at hρ hδ
  simp only [Iso.symm_hom] at hρ hδ
  apply (cancel_mono (ρ.inv.app (qB.obj P))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  apply (cancel_mono (dt.map (βB.app P))).mp
  apply (cancel_epi (δ₀.inv.app (qB.obj P))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp]
  rw [← dt.map_comp, hB, dt.map_comp]
  rw [← Category.assoc, ← hδ]
  rw [Category.assoc, Category.assoc, Category.assoc]
  have hnδ := δ.hom.naturality (uB.app P)
  dsimp only [Functor.comp_map] at hnδ
  rw [← hnδ, ← hρ]
  have hnη := ηR.naturality (α.inv.app P)
  dsimp only [Functor.comp_obj] at hnη
  rw [← Category.assoc (ηR.app _), ← hnη]
  simp only [Category.assoc]
  rw [← tqR.map_comp_assoc, ← hunit, tqR.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ dgR.map (α.inv.app P) ≫ k ≫
      tqR.map (γ.hom.app P) ≫ δ.hom.app (redB.obj P)) hR.symm

private theorem ordinary_augmentation [IsNoetherianRing A] (T : Scheme.{u})
    (d : AdicCoefficientDatum A)
    (M : Mod (ring T d true)) :
    (reductionUnit (topology T) A d.ideal false).app ((res (scalar T d)).obj M) ≫
        (reductionTowerComparison (topology T) A d.ideal).hom.app M =
      (tres (scalar T d)).map ((reductionUnit (topology T) A d.ideal true).app M) := by
  let := d.noetherian
  apply NatTrans.ext
  funext n
  ext U m
  change (((reductionTowerComparison (topology T) A d.ideal).hom.app M).app n).val.app U
      (((reductionUnit (topology T) A d.ideal false).app
        ((res (scalar T d)).obj M)).app n |>.val.app U m) =
    (((reductionUnit (topology T) A d.ideal true).app M).app n).val.app U m
  have hR := (reductionUnit_existsUnique (topology T) A d.ideal false).exists.choose_spec
    ((res (scalar T d)).obj M) n.unop U m
  have hB := (reductionUnit_existsUnique (topology T) A d.ideal true).exists.choose_spec
    M n.unop U m
  erw [hR]
  erw [(reductionTowerComparison_existsUnique (topology T) A d.ideal).exists.choose_spec]
  erw [(finiteComparison_existsUnique (topology T) A d.ideal n.unop).exists.choose_spec]
  exact hB.symm

private theorem model_ext
    {C E H : Type*} [Category C] [Category E] [Category H]
    (q : C ⥤ E) (W : MorphismProperty C) [q.IsLocalization W]
    (S : C → Prop)
    (hres : ∀ X, ∃ (Y : C) (f : Y ⟶ X), S Y ∧ IsIso (q.map f))
    {F G : E ⥤ H} (a b : F ⟶ G)
    (h : ∀ Y, S Y → a.app (q.obj Y) = b.app (q.obj Y)) : a = b := by
  apply Localization.natTrans_ext q W
  intro X
  obtain ⟨Y, f, hY, hf⟩ := hres X
  have := hf
  apply (cancel_epi (F.map (q.map f))).mp
  rw [a.naturality, b.naturality, h Y hY]

private theorem flat_resolution (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (P : Cx (ring T d true)) :
    ∃ (K : Cx (ring T d true)) (f : K ⟶ P),
      (K.IsAcyclicTensorKFlat ∧ ∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
        IsIso ((Q (ring T d true)).map f) := by
  let := HasDerivedCategory.standard (Mod (ring T d true))
  obtain ⟨K, f, hK, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  refine ⟨K, f, ⟨?_, ?_⟩, ?_⟩
  · exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).1 hK
  · exact hf
  · exact (DerivedCategory.isIso_Q_map_iff_quasiIso (Mod (ring T d true)) f).2 hq

private theorem flat_iff_site {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}} (M : Mod R) :
    SheafOfModules.IsFlat M ↔ SheafOfModules.IsFlatOnSite (R := R) M := by
  let := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (MonoidalCategory.tensorRight M) ↔ _
  exact ⟨fun h ↦ ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso R M).symm h,
    fun h ↦ ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso R M) h⟩

private theorem augmentation_equation_of_computes
    (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (ρ : reduction T d true ⋙ tdres (scalar T d) ≅
      dres (scalar T d) ⋙ reduction T d false) (hρ : BalancingComputes T d ρ)
    (ηB : delta T d true ⟶ reduction T d true) (hηB : AugmentationComputes T d true ηB)
    (ηR : delta T d false ⟶ reduction T d false) (hηR : AugmentationComputes T d false ηR)
    (δ : delta T d true ⋙ tdres (scalar T d) ≅ dres (scalar T d) ⋙ delta T d false)
    (hδ : DeltaRestrictionComputes T d δ) :
    ∀ L : D (ring T d true),
      (tdres (scalar T d)).map (ηB.app L) ≫ ρ.hom.app L =
        δ.hom.app L ≫ ηR.app ((dres (scalar T d)).obj L) := by
  let := d.noetherian
  let := HasDerivedCategory.standard (Mod (ring T d true))
  let lhs := Functor.whiskerRight ηB (tdres (scalar T d)) ≫ ρ.hom
  let rhs := δ.hom ≫ Functor.whiskerLeft (dres (scalar T d)) ηR
  have hl : lhs = rhs := by
    apply model_ext (Q (ring T d true))
      (HomologicalComplex.quasiIso (Mod (ring T d true)) (.up ℤ))
      (fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ i : ℤ, SheafOfModules.IsFlat (P.X i))
      (flat_resolution T d)
    intro P hP
    have hc := (quotientPresentation (topology T) A d.ideal true).laws.2.1 P hP.1 hP.2
    have := hc
    have hflat := (flat_and_quotients (topology T) A d.ideal).1
    have hr := SheafOfModules.isKFlat_restrictScalars_of_flat
      (scalar T d) ((flat_iff_site _).1 hflat) P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1)
    have hpr := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hr.1
    have hfr := hr.2 (fun i ↦ (flat_iff_site _).1 (hP.2 i))
    apply augmentation_square (resFactors (scalar T d))
      (quotientPresentation (topology T) A d.ideal false).comparison
      (balanceComplex T d) (tresFactors (scalar T d))
      (quotientPresentation (topology T) A d.ideal true).comparison
      (deltaFactors T d false) (deltaFactors T d true) (constantRestrictionComplex T d)
      (NatTrans.mapHomologicalComplex (reductionUnit (topology T) A d.ideal false) (.up ℤ))
      (NatTrans.mapHomologicalComplex (reductionUnit (topology T) A d.ideal true) (.up ℤ))
      ηR ηB ρ δ P (hρ P hP.1 hP.2) (hδ P)
      (hηR _ hpr (fun i ↦ (flat_iff_site _).2 (hfr i))) (hηB P hP.1 hP.2)
    apply HomologicalComplex.hom_ext
    intro i
    exact ordinary_augmentation T d (P.X i)
  intro L
  exact congrArg (fun a ↦ a.app L) hl

private theorem balancing_exists (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    ∃ ρ : reduction T d true ⋙ tdres (scalar T d) ≅
        dres (scalar T d) ⋙ reduction T d false, BalancingComputes T d ρ := by
  let := d.noetherian
  obtain ⟨e, he⟩ := derivedReductionTowerComparison (topology T) A d.ideal
  exact ⟨e.symm, he⟩

private theorem augmentation_exists (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (b : Bool) : ∃ η : delta T d b ⟶ reduction T d b,
      AugmentationComputes T d b η := by
  let := HasDerivedCategory.standard (Mod (ring T d b))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (ring T d b))
  let β := (quotientPresentation (topology T) A d.ideal b).comparison
  have : (reduction T d b).IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (Mod (ring T d b)) (.up ℤ)) :=
    (quotientPresentation (topology T) A d.ideal b).laws.1
  let θ := (deltaFactors T d b).hom ≫ Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (reductionUnit (topology T) A d.ideal b) (.up ℤ))
    (TQ (ring T d b))
  let η := (reduction T d b).leftDerivedLift β
    (HomologicalComplex.quasiIso (Mod (ring T d b)) (.up ℤ)) (delta T d b) θ
  refine ⟨η, ?_⟩
  intro P _ _
  exact (reduction T d b).leftDerived_fac_app β
    (HomologicalComplex.quasiIso (Mod (ring T d b)) (.up ℤ)) (delta T d b) θ P

/-- Strict quotient balancing preserves the augmentation and canonical pullback
reassociation on arbitrary ambient inputs. All isomorphisms and equations are in the
actual derived category of strict towers.

Source: main-20261015, completed-exchange-coherence proof, second paragraph,
strict coefficient supplement old Step 4; Stacks 099M is completion context only.
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing).

Proof:
1. Invert the existing normalized derived reduction-tower comparison. Its formula
computes scalar balancing on every flat-term K-flat completed-coefficient complex.
2. Constant diagrams and scalar restriction are exact. Descend their ordinary
commuting square through localization to obtain deltaRestriction with its formula.
Lift the ordinary quotient-unit transformation through the universal left-derived
reduction functor. Its universal factorization equation gives augmentation_computes.
3. On sections the ordinary quotient unit inserts 1 and the ordinary balancing
comparison preserves that tensor. This proves the ordinary augmentation square.
Cancel the invertible comparison on a flat-term K-flat representative and use the
three representative formulas and naturality to obtain the derived square. Flat
restriction preserves the resolving class. Every complex admits such a resolution;
localization and naturality extend this equality to every derived object.
4. Apply strictQuotientPullbackCompatibility to the normalized balancing comparisons
on the two schemes. This separate source argument supplies only the pullback record
and its equation. Assemble it with the augmentation construction above. -/
theorem strictQuotientScalarBalancing (d : AdicCoefficientDatum A) :
    Nonempty (Balancing d) := by
  classical
  choose ρ hρ using fun T : Scheme.{u} ↦ balancing_exists T d
  choose η hη using fun (T : Scheme.{u}) (b : Bool) ↦ augmentation_exists T d b
  choose δ hδ using fun T : Scheme.{u} ↦ deltaRestriction_exists T d
  refine ⟨{ ρ := ρ
            ρ_computes := hρ
            augmentation := η
            augmentation_computes := hη
            deltaRestriction := δ
            deltaRestriction_computes := hδ
            augmentation_equation := ?_
            pullback := ?_ }⟩
  · intro T
    exact augmentation_equation_of_computes T d (ρ T) (hρ T)
      (η T true) (hη T true) (η T false) (hη T false) (δ T) (hδ T)
  · intro U V f
    exact strictQuotientPullbackCompatibility f d (ρ V) (ρ U) (hρ V) (hρ U)

end AlgebraicGeometry.Scheme.StrictScalarBalancing
