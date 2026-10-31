/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralChartComparisons
public import WeilConjectures.AlgebraicGeometry.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.PuritySectionInvariantIntrinsic
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginDerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.PurityDiagonalBaseChangeCompared
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.StandingExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.PurityDncInvariance
public import WeilConjectures.AlgebraicGeometry.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.ChartDncVectorFactorData
import WeilConjectures.AlgebraicGeometry.ChartExceptionalCounitEquation
import WeilConjectures.AlgebraicGeometry.ChartEpsilonPasting
import WeilConjectures.AlgebraicGeometry.ChartDiagonalSourceSquare
import WeilConjectures.AlgebraicGeometry.ChartDncSquare
import WeilConjectures.AlgebraicGeometry.ChartNormalIntegrationSquare
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition

/-! # Exceptional chart mates and the three diagonal comparison squares

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Steps 1--4; composition-coherence proof, Step 1.
(blueprint: lem-pur-chart-exceptional-mate-coherence).

All arrows are the published counit, Rees, normalized DNC and integration constructions.
The conclusion includes their domain assertions and identity and composition equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- The canonical identification of omega with the standing exceptional value.
Source: orientation-charts Step 3, uniqueness of counit-preserving right adjoints
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def omegaShriekIso (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := Dnc.compactifiable P g aY
  P.chartDiagonalDualizingStanding g

/-- Zero-section integration on the actual normal bundle, without a frame choice.
Source: orientation-charts Step 4
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def integration (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  ChartFactors.beta P d C.proj aV N

/-- The canonical pullback constraint on the shifted Tate coefficient of integration.
Source: orientation-charts Step 4
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def tateComparison (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  Dnc.pullComparison P e.hom
      (Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates B.X d) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory.mapIso
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t e.hom
          (P.diagonalExponent_isUnit (B.proj ≫ aV)) d)

/-- The three equations for the actual diagonal, normalized deformation and integration
arrows, with the final Tate constraint displayed.
Source: orientation-charts Steps 3--4
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def ThreeEquations (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) : Prop :=
  (q P aV e N).hom ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map
        (alpha P aV B).hom = (alpha P aV C).hom ≫ (eps P aV e N).hom ∧
  (delta P aV C).hom ≫ (r P aV e).hom =
    (q P aV e N).hom ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map
        (delta P aV B).hom ∧
  (r P aV e).hom ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map
        (integration P aV B N).hom ≫ (tateComparison P aV e t).hom =
    (integration P aV C N).hom

/-- Identity comparisons, expressed using the canonical identity pullback constraint.
Source: composition-coherence Step 1
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def Identity (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) (N : Etale.EtaleCompactSupportNormalization P.Coefficient) : Prop :=
  (eps P aV (Map.id C) N).hom ≫
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X).hom.app
        (omega P C.proj aV) = 𝟙 _ ∧
  (q P aV (Map.id C) N).hom ≫
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X).hom.app
        (sectionObject P aV C) = 𝟙 _ ∧
  (r P aV (Map.id C)).hom ≫
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X).hom.app
        (normalSection P aV C) = 𝟙 _

/-- Pasting for successive etale maps, including open restrictions. The pullback
composition constraint has direction composite pullback to iterated pullback.
Source: composition-coherence Step 1 and orientation-charts Steps 3--4
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def Composition (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B A : Chart V d} (v : Map C B) (e : Map B A)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) : Prop :=
  (eps P aV (Map.comp v e) N).hom ≫
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        v.hom e.hom).hom.app (omega P A.proj aV) =
    (eps P aV v N).hom ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.map
        (eps P aV e N).hom ∧
  (q P aV (Map.comp v e) N).hom ≫
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        v.hom e.hom).hom.app (sectionObject P aV A) =
    (q P aV v N).hom ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.map
        (q P aV e N).hom ∧
  (r P aV (Map.comp v e)).hom ≫
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        v.hom e.hom).hom.app (normalSection P aV A) =
    (r P aV v).hom ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.map
        (r P aV e).hom

/-- The stated domain, invertibility of the specific exceptional transpose, and its
counit-preserving identification with epsilon. The composition map itself is the
published standingExceptionalComposition, hence the conjugate of alpha for the
composite standing Hom bijection, rather than an arbitrary isomorphism.
Source: composition-coherence Step 1 and orientation-charts Step 3
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def ExceptionalMate (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) : Prop :=
  letI := Dnc.compactifiable P B.proj aV
  letI := Dnc.compactifiable P e.hom (B.proj ≫ aV)
  letI := Dnc.compactifiable P (e.hom ≫ B.proj) aV
  ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) C.X
      (omega P (e.hom ≫ B.proj) aV) ∧
  ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) C.X
      (omega P (e.hom ≫ B.proj) aV) ∧
  ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) B.X
      (supportOmega P B.proj aV e.hom) ∧
  IsIso (composition P B.proj aV e.hom) ∧
  (omegaShriekIso P (e.hom ≫ B.proj) aV).hom ≫
      composition P B.proj aV e.hom ≫
      (ProEtale.rightDerivedUpperShriek P.Coefficient e.hom).map
        (omegaShriekIso P B.proj aV).inv ≫ (rho P B.proj aV e.hom N).hom =
    (omegaCongr P aV e.over_eq).hom ≫ (eps P aV e N).hom

/-- The coordinate-chart assertion and its identity and arbitrary-map pasting clauses.
All normalization presentations are quantified; none is an orientation choice.
Source: orientation-charts Steps 1--4 and composition-coherence Step 1
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def Conclusion (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (d : ℕ) : Prop :=
  ∀ (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates),
    (∀ C : Chart V d, ExceptionalMate P aV (coordinate C) N ∧
      ThreeEquations P aV (coordinate C) N t) ∧
    (∀ C : Chart V d, Identity P aV C N) ∧
    (∀ (C B : Chart V d) (e : Map C B),
      ExceptionalMate P aV e N ∧ ThreeEquations P aV e N t) ∧
    (∀ (C B A : Chart V d) (v : Map C B) (e : Map B A), Composition P aV v e N)

private theorem transport_identity {D : Type*} [Category* D] (F : D ⥤ D)
    (τ : F ≅ 𝟭 D) {X Y : D} (a : X ≅ Y) (q : X ⟶ F.obj X) (e : Y ⟶ F.obj Y)
    (hs : q ≫ F.map a.hom = a.hom ≫ e) (he : e ≫ τ.hom.app Y = 𝟙 Y) :
    q ≫ τ.hom.app X = 𝟙 X := by
  apply (cancel_mono a.hom).mp
  calc
    (q ≫ τ.hom.app X) ≫ a.hom = q ≫ F.map a.hom ≫ τ.hom.app Y := by
      simpa only [Category.assoc, Functor.id_map] using
        congrArg (q ≫ ·) (τ.hom.naturality a.hom).symm
    _ = a.hom ≫ e ≫ τ.hom.app Y := by rw [← Category.assoc, hs, Category.assoc]
    _ = (𝟙 X) ≫ a.hom := by rw [he]; simp

private theorem transport_composition
    {D₀ D₁ D₂ : Type*} [Category* D₀] [Category* D₁] [Category* D₂]
    (F : D₁ ⥤ D₀) (G : D₂ ⥤ D₁) (H : D₂ ⥤ D₀) (τ : H ≅ G ⋙ F)
    {X₀ Y₀ : D₀} {X₁ Y₁ : D₁} {X₂ Y₂ : D₂}
    (a₀ : X₀ ≅ Y₀) (a₁ : X₁ ≅ Y₁) (a₂ : X₂ ≅ Y₂)
    (qv : X₀ ⟶ F.obj X₁) (qe : X₁ ⟶ G.obj X₂) (qve : X₀ ⟶ H.obj X₂)
    (ev : Y₀ ⟶ F.obj Y₁) (ee : Y₁ ⟶ G.obj Y₂) (eve : Y₀ ⟶ H.obj Y₂)
    (hv : qv ≫ F.map a₁.hom = a₀.hom ≫ ev)
    (he : qe ≫ G.map a₂.hom = a₁.hom ≫ ee)
    (hve : qve ≫ H.map a₂.hom = a₀.hom ≫ eve)
    (hp : eve ≫ τ.hom.app Y₂ = ev ≫ F.map ee) :
    qve ≫ τ.hom.app X₂ = qv ≫ F.map qe := by
  apply (cancel_mono (F.map (G.map a₂.hom))).mp
  calc
    (qve ≫ τ.hom.app X₂) ≫ F.map (G.map a₂.hom) =
        qve ≫ H.map a₂.hom ≫ τ.hom.app Y₂ := by
      simpa only [Category.assoc, Functor.comp_map] using
        congrArg (qve ≫ ·) (τ.hom.naturality a₂.hom).symm
    _ = a₀.hom ≫ eve ≫ τ.hom.app Y₂ := by
      rw [← Category.assoc, hve, Category.assoc]
    _ = a₀.hom ≫ ev ≫ F.map ee := by rw [hp]
    _ = qv ≫ F.map a₁.hom ≫ F.map ee := by
      rw [← Category.assoc, ← hv, Category.assoc]
    _ = qv ≫ F.map qe ≫ F.map (G.map a₂.hom) := by
      rw [← F.map_comp, ← he, F.map_comp]
    _ = (qv ≫ F.map qe) ≫ F.map (G.map a₂.hom) := (Category.assoc _ _ _).symm

/-- Constructible exceptional composition is the counit-normalized chart comparison;
the diagonal, DNC and integration arrows obey their three equations and all pasting.
Source: orientation-charts proof Steps 1--4 and composition-coherence proof Step 1
(blueprint: lem-pur-chart-exceptional-mate-coherence).

Proof: (1) Smooth exceptional pullback preserves ordinary bounded constructibility;
transport along diagonalDualizingComparison. A bounded constructible object has etale
origin, and compact-support pushforward preserves bounded-below etale origin, by
lem-sf-proetale-constructible-origin and thm-sf-comp-composition.
(2) The counit equation of lem-pur-chart-exceptional-counit-equation identifies c followed
by rho with epsilon. Since epsilon and rho are invertible, cancel to obtain invertibility
of c. Cancel omegaCongr and its inverse to obtain ExceptionalMate.
(3) Apply lem-pur-chart-diagonal-source-square, lem-pur-chart-dnc-square and
lem-pur-chart-normal-integration-square to the independently defined q, r, delta and beta.
These give exactly ThreeEquations, including the Tate comparison.
(4) lem-pur-chart-epsilon-pasting gives epsilon identity and composition. Conjugate the
first square by alpha, use naturality of pullback identity/composition constraints and
cancel alpha to deduce the same equations for q. Rewrite the DNC square using delta
inverse; naturality and cancellation transfer q's identity and composition equations to r.
The pullback associativity constraint gives all further pastings and open restrictions.
No orientation is selected in any step; all d, including zero, and empty charts remain. -/
theorem chart_exceptional_mate_coherence (P : PurityFiniteSetting.{u}) (V : Scheme.{u})
    [IsAffine V] (aV : V ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aV] [QuasiCompact aV] (d : ℕ) : Conclusion P aV d := by
  intro N t
  have hs {C B : Chart V d} (e : Map C B) :
      (q P aV e N).hom ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map
          (alpha P aV B).hom = (alpha P aV C).hom ≫ (eps P aV e N).hom :=
    congrArg Iso.hom (chart_diagonal_source_square P aV e N)
  have hd {C B : Chart V d} (e : Map C B) :
      (delta P aV C).hom ≫ (r P aV e).hom = (q P aV e N).hom ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map
          (delta P aV B).hom :=
    congrArg Iso.hom (chart_dnc_square P aV e N)
  have hr {C B : Chart V d} (e : Map C B) :
      (r P aV e).hom ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map
          (delta P aV B).inv = (delta P aV C).inv ≫ (q P aV e N).hom := by
    apply (cancel_epi (delta P aV C).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, hd]
    rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have equations {C B : Chart V d} (e : Map C B) : ThreeEquations P aV e N t := by
    refine ⟨hs e, hd e, ?_⟩
    exact congrArg Iso.hom (chart_normal_integration_square P aV e N t)
  have mate {C B : Chart V d} (e : Map C B) : ExceptionalMate P aV e N := by
    let := Dnc.compactifiable P B.proj aV
    let := Dnc.compactifiable P e.hom (B.proj ≫ aV)
    let := Dnc.compactifiable P (e.hom ≫ B.proj) aV
    let := Dnc.compactifiable P C.proj aV
    have hbc : ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} P.Coefficient) C.X (omega P (e.hom ≫ B.proj) aV) := by
      have heq : omega P (e.hom ≫ B.proj) aV ≅ omega P C.proj aV :=
        omegaCongr P aV e.over_eq
      apply (ProEtale.DerivedCategory.boundedConstructible _ C.X).prop_of_iso heq.symm
      apply (ProEtale.DerivedCategory.boundedConstructible _ C.X).prop_of_iso
        (P.diagonalDualizingComparison C.proj).symm
      apply ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      let := Dnc.invertibleExponent P aV
      exact Etale.boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension
        P.Coefficient C.proj d (P.chartCoefficientUnit_finiteTor V).1
    have hc := chart_exceptional_counit_equation P aV e N
    have hiso : IsIso (composition P B.proj aV e.hom) := by
      have hh : IsIso (composition P B.proj aV e.hom ≫
          (ProEtale.rightDerivedUpperShriek P.Coefficient e.hom).map
            (P.chartDiagonalDualizingStanding B.proj).inv ≫
          (rho P B.proj aV e.hom N).hom) := by
        rw [hc]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((ProEtale.rightDerivedUpperShriek P.Coefficient e.hom).map
          (P.chartDiagonalDualizingStanding B.proj).inv ≫
          (rho P B.proj aV e.hom N).hom)
    refine ⟨hbc, hbc.plusEtaleOrigin,
      hbc.plusEtaleOrigin.rightDerivedLowerShriek_obj e.hom, hiso, ?_⟩
    have hmate := congrArg
      ((P.chartDiagonalDualizingStanding (e.hom ≫ B.proj)).hom ≫ ·) hc
    simpa only [omegaShriekIso, eps, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc] using hmate
  have hp := chart_epsilon_pasting P aV (d := d)
  have hid (C : Chart V d) : Identity P aV C N := by
    have he := congrArg Iso.hom (hp.1 C N)
    have hq := transport_identity
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 C.X)).leftDerivedFunctor
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X)
      (alpha P aV C) (q P aV (Map.id C) N).hom (eps P aV (Map.id C) N).hom
      (hs (Map.id C)) he
    exact ⟨he, hq, transport_identity
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 C.X)).leftDerivedFunctor
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X)
      (delta P aV C).symm (r P aV (Map.id C)).hom (q P aV (Map.id C) N).hom
      (hr (Map.id C)) hq⟩
  have hcomp (C B A : Chart V d) (v : Map C B) (e : Map B A) :
      Composition P aV v e N := by
    have he := congrArg Iso.hom (hp.2 C B A v e N)
    have hq := transport_composition
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (v.hom ≫ e.hom)).leftDerivedFunctor
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom)
      (alpha P aV C) (alpha P aV B) (alpha P aV A)
      (q P aV v N).hom (q P aV e N).hom (q P aV (v.comp e) N).hom
      (eps P aV v N).hom (eps P aV e N).hom (eps P aV (v.comp e) N).hom
      (hs v) (hs e) (hs (v.comp e)) he
    exact ⟨he, hq, transport_composition
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (v.hom ≫ e.hom)).leftDerivedFunctor
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom)
      (delta P aV C).symm (delta P aV B).symm (delta P aV A).symm
      (r P aV v).hom (r P aV e).hom (r P aV (v.comp e)).hom
      (q P aV v N).hom (q P aV e N).hom (q P aV (v.comp e) N).hom
      (hr v) (hr e) (hr (v.comp e)) hq⟩
  exact ⟨fun C ↦ ⟨mate (coordinate C), equations (coordinate C)⟩, hid,
    fun _ _ e ↦ ⟨mate e, equations e⟩, hcomp⟩

end WeilConjectures.PurityFiniteSetting.ChartComparisons
