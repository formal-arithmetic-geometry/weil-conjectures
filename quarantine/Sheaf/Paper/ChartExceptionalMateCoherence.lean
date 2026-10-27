module

public import Sheaf.Paper.GeneralChartComparisons
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.FixedEtaleOriginDerivedCategory
public import Sheaf.Paper.ProEtaleConstructibleOrigin
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.ChartExceptionalCounitEquation
import Sheaf.Paper.ChartEpsilonPasting
import Sheaf.Paper.ChartDiagonalSourceSquare
import Sheaf.Paper.ChartDncSquare
import Sheaf.Paper.ChartNormalIntegrationSquare
import WeilConjectures.ConstructibleSheaf.SpecializationCriterion
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible

/-! # Exceptional composition and coherence of affine chart comparisons

Source: blueprint latest, sec-smooth-purity, orientation-charts proof Steps 1--4
and composition-coherence proof Step 1
(blueprint: lem-pur-chart-exceptional-mate-coherence).

Every comparison below is the actual counit-defined map or its canonical site transport.
The three equations concern alpha, normalized delta and integration-normalized beta.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- Zero-section integration purity on the actual normal bundle, in the published
conormal model. This reuses the independently integration-normalized map, with no
orientation choice. Source: chart proof Step 4
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def integration (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  ChartFactors.beta P d C.proj aV N

/-- Canonical pullback of the shifted Tate line, with the fixed pure-tensor coefficient
comparison. Source: chart proof Step 4
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def tateComparison (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  Dnc.pullComparison P e.hom (P.diagonalTwistEtale B.X d) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory.mapIso
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t e.hom (P.diagonalExponent_isUnit
          (B.proj ≫ aV)) d)

/-- The three stated equations for the actual chart comparison maps. The canonical
Tate constraint is displayed in the third equation. All normalized presentations
are quantified, rather than supplied as an orientation hypothesis.
Source: chart proof Steps 3--4
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def ThreeEquations (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B) : Prop :=
  ∀ (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates),
    q P aV e N ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
          (alpha P aV B) = alpha P aV C ≪≫ eps P aV e N ∧
    delta P aV C ≪≫ r P aV e = q P aV e N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
        (delta P aV B) ∧
    r P aV e ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
          (integration P aV B N) ≪≫ tateComparison P aV e t = integration P aV C N

/-- Identity equations, with the actual pullback-identity constraints. In particular
epsilon_1 is the identity after this canonical identification.
Source: composition-coherence proof Step 1
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def Identity (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) : Prop :=
  ∀ N : Etale.EtaleCompactSupportNormalization P.Coefficient,
    eps P aV (Map.id C) N ≪≫
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X).app
        (omega P C.proj aV) = Iso.refl _ ∧
    q P aV (Map.id C) N ≪≫
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X).app
        (sectionObject P aV C) = Iso.refl _ ∧
    r P aV (Map.id C) ≪≫
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X).app
        (normalSection P aV C) = Iso.refl _

/-- Pasting equations for all composable etale chart maps. The same equations applied
to a third map are the associativity equations, and open immersions are included.
Source: composition-coherence proof Step 1
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def Composition (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B A : Chart V d} (v : Map C B) (e : Map B A) : Prop :=
  ∀ N : Etale.EtaleCompactSupportNormalization P.Coefficient,
    eps P aV (v.comp e) N ≪≫
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom).app
        (omega P A.proj aV) = eps P aV v N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.mapIso
        (eps P aV e N) ∧
    q P aV (v.comp e) N ≪≫
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom).app
        (sectionObject P aV A) = q P aV v N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.mapIso
        (q P aV e N) ∧
    r P aV (v.comp e) ≪≫
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom).app
        (normalSection P aV A) = r P aV v ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.mapIso
        (r P aV e)

/-- The comparison is the specified standing c followed by rho; the domain is verified
for K=Rh!A and Ru!K, rather than assumed. The defining c is the transpose of alpha
followed by the standing counit, so this equation identifies the conjugate itself.
Source: chart proof Steps 1--2
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def ExceptionalMate (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B) : Prop :=
  IsIso (composition P B.proj aV e.hom) ∧
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) C.X
      (omega P (e.hom ≫ B.proj) aV) ∧
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) C.X
      (omega P (e.hom ≫ B.proj) aV) ∧
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) B.X
      (supportOmega P B.proj aV e.hom) ∧
    ∀ N : Etale.EtaleCompactSupportNormalization P.Coefficient,
      composition P B.proj aV e.hom ≫ (rho P B.proj aV e.hom N).hom =
        (omegaCongr P aV e.over_eq ≪≫ eps P aV e N).hom

/-- All comparisons on an affine etale coordinate chart and its further etale or open
restrictions, including the identity and all composable pastings. The coefficient
setting contains arbitrary finite E/Q_l and every positive level, without a ramification
restriction. Source: orientation-charts proof Steps 1--4; composition-coherence Step 1
(blueprint: lem-pur-chart-exceptional-mate-coherence). -/
def Conclusion (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (d : ℕ) : Prop :=
  (∀ C : Chart V d, ExceptionalMate P aV (coordinate C) ∧
    ThreeEquations P aV (coordinate C) ∧ Identity P aV C) ∧
  (∀ (C B A : Chart V d) (v : Map C B) (e : Map B A),
    ExceptionalMate P aV v ∧ ThreeEquations P aV v ∧ Composition P aV v e)

private theorem transport_identity
    {D : Type*} [Category* D] (F : D ⥤ D) (ι : F ≅ 𝟭 D)
    {S T : D} (a : S ≅ T) (q : S ≅ F.obj S) (e : T ≅ F.obj T)
    (h : q ≪≫ F.mapIso a = a ≪≫ e)
    (he : e ≪≫ ι.app T = Iso.refl T) :
    q ≪≫ ι.app S = Iso.refl S := by
  apply Iso.ext
  apply (cancel_mono a.hom).1
  have hn := ι.hom.naturality a.hom
  have hh := congrArg Iso.hom h
  have hi := congrArg Iso.hom he
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.id_map,
    Iso.refl_hom] at hh hi hn ⊢
  calc
    (q.hom ≫ ι.hom.app S) ≫ a.hom =
        (q.hom ≫ F.map a.hom) ≫ ι.hom.app T := by
      simpa only [Category.assoc] using
        congrArg (fun z => q.hom ≫ z) hn.symm
    _ = (a.hom ≫ e.hom) ≫ ι.hom.app T := by
      rw [hh]
    _ = a.hom := by rw [Category.assoc, hi, Category.comp_id]
    _ = 𝟙 S ≫ a.hom := by simp

private theorem transport_composition
    {D₀ D₁ D₂ : Type*} [Category* D₀] [Category* D₁] [Category* D₂]
    (F : D₁ ⥤ D₀) (G : D₂ ⥤ D₁) (H : D₂ ⥤ D₀) (c : H ≅ G ⋙ F)
    {S₀ T₀ : D₀} {S₁ T₁ : D₁} {S₂ T₂ : D₂}
    (a₀ : S₀ ≅ T₀) (a₁ : S₁ ≅ T₁) (a₂ : S₂ ≅ T₂)
    (q₀ : S₀ ≅ F.obj S₁) (q₁ : S₁ ≅ G.obj S₂) (q₂ : S₀ ≅ H.obj S₂)
    (e₀ : T₀ ≅ F.obj T₁) (e₁ : T₁ ≅ G.obj T₂) (e₂ : T₀ ≅ H.obj T₂)
    (h₀ : q₀ ≪≫ F.mapIso a₁ = a₀ ≪≫ e₀)
    (h₁ : q₁ ≪≫ G.mapIso a₂ = a₁ ≪≫ e₁)
    (h₂ : q₂ ≪≫ H.mapIso a₂ = a₀ ≪≫ e₂)
    (he : e₂ ≪≫ c.app T₂ = e₀ ≪≫ F.mapIso e₁) :
    q₂ ≪≫ c.app S₂ = q₀ ≪≫ F.mapIso q₁ := by
  apply Iso.ext
  apply (cancel_mono (F.map (G.map a₂.hom))).1
  have hn := c.hom.naturality a₂.hom
  have h₀' := congrArg Iso.hom h₀
  have h₁' := congrArg Iso.hom h₁
  have h₂' := congrArg Iso.hom h₂
  have he' := congrArg Iso.hom he
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.comp_map] at hn h₀' h₁' h₂' he' ⊢
  calc
    (q₂.hom ≫ c.hom.app S₂) ≫ F.map (G.map a₂.hom) =
        a₀.hom ≫ e₂.hom ≫ c.hom.app T₂ := by
      calc
        (q₂.hom ≫ c.hom.app S₂) ≫ F.map (G.map a₂.hom) =
            q₂.hom ≫ (c.hom.app S₂ ≫ F.map (G.map a₂.hom)) := by
              simp only [Category.assoc]
        _ = q₂.hom ≫ (H.map a₂.hom ≫ c.hom.app T₂) := by rw [← hn]
        _ = (q₂.hom ≫ H.map a₂.hom) ≫ c.hom.app T₂ := by
              simp only [Category.assoc]
        _ = (a₀.hom ≫ e₂.hom) ≫ c.hom.app T₂ := by rw [h₂']
        _ = a₀.hom ≫ e₂.hom ≫ c.hom.app T₂ := by simp only [Category.assoc]
    _ = a₀.hom ≫ e₀.hom ≫ F.map e₁.hom := by rw [he']
    _ = (q₀.hom ≫ F.map q₁.hom) ≫ F.map (G.map a₂.hom) := by
      calc
        a₀.hom ≫ e₀.hom ≫ F.map e₁.hom =
            (a₀.hom ≫ e₀.hom) ≫ F.map e₁.hom := by simp only [Category.assoc]
        _ = (q₀.hom ≫ F.map a₁.hom) ≫ F.map e₁.hom := by rw [h₀']
        _ = q₀.hom ≫ (F.map a₁.hom ≫ F.map e₁.hom) := by
              simp only [Category.assoc]
        _ = q₀.hom ≫ F.map (a₁.hom ≫ e₁.hom) := by rw [F.map_comp]
        _ = q₀.hom ≫ F.map (q₁.hom ≫ G.map a₂.hom) := by rw [h₁']
        _ = (q₀.hom ≫ F.map q₁.hom) ≫ F.map (G.map a₂.hom) := by
              rw [F.map_comp]
              simp only [Category.assoc]

private theorem reverse_square
    {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {S T : E} {S' T' : D} (a : S ≅ T) (b : S' ≅ T')
    (q : S ≅ F.obj S') (r : T ≅ F.obj T')
    (h : a ≪≫ r = q ≪≫ F.mapIso b) :
    r ≪≫ F.mapIso b.symm = a.symm ≪≫ q := by
  apply Iso.ext
  apply (cancel_epi a.hom).1
  have hh := congrArg Iso.hom h
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] at hh ⊢
  rw [← Category.assoc, hh]
  simp only [Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

private theorem omega_bounded (P : PurityFiniteSetting.{u})
    {X V : Scheme.{u}} (g : X ⟶ V)
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (d : ℕ) [SmoothOfRelativeDimension d g] :
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) X
      (omega P g aV) := by
  have := Dnc.compactifiable P g aV
  have := Dnc.invertibleExponent P aV
  apply (ProEtale.DerivedCategory.boundedConstructible _ X).prop_of_iso
    (P.diagonalDualizingComparison g).symm
  apply ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
  apply Etale.boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    P.Coefficient g d
  have := Scheme.isConstructibleSheaf_constantSheaf
    (X := V) (ModuleCat.of P.Coefficient P.Coefficient)
  exact Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0

/-- The specified exceptional composition mate is invertible and counit normalized;
the three actual diagonal arrows commute with chart pullback and coherent pasting.
Source: blueprint latest, sk-prop-sp-orientation-charts.proof.md, Steps 1--4 and
thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-chart-exceptional-mate-coherence).

Proof: bounded constructibility of the actual smooth exceptional image follows from
ordinary smooth exceptional preservation and its canonical comparison presentation.
Its etale origin and that of its compact-support image follow from the existing
constructibility and compact-support origin lemmas. The counit equation identifies
composition followed by rho with epsilon; cancellation proves composition invertible.
The three independent factor squares give ThreeEquations. Naturality of the pullback
identity and composition constraints, conjugated by alpha, transports epsilon pasting
to q pasting. Conjugate again by delta inverse to transport q pasting to r pasting.
These two categorical cancellation arguments establish every identity and composition
clause without separate geometric pasting calculations for q and r. -/
theorem chart_exceptional_mate_coherence (P : PurityFiniteSetting.{u})
    (V : Scheme.{u}) [IsAffine V] (aV : V ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aV] [QuasiCompact aV] (d : ℕ) : Conclusion P aV d := by
  have hm (C B : Chart V d) (e : Map C B) : ExceptionalMate P aV e := by
    have hbd : ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} P.Coefficient) C.X (omega P (e.hom ≫ B.proj) aV) := by
      apply (ProEtale.DerivedCategory.boundedConstructible _ C.X).prop_of_iso
        (omegaCongr P aV e.over_eq).symm
      exact omega_bounded P C.proj aV d
    have hor := hbd.plusEtaleOrigin
    have := Dnc.compactifiable P e.hom (B.proj ≫ aV)
    have hi : IsIso (composition P B.proj aV e.hom) := by
      let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
      exact IsIso.of_isIso_fac_right (chart_exceptional_counit_equation P aV e N)
    refine ⟨hi, hbd, hor, hor.rightDerivedLowerShriek_obj e.hom, ?_⟩
    intro N
    rw [chart_exceptional_counit_equation P aV e N]
    simp [eps, omegaCongr]
  have hs (C B : Chart V d) (e : Map C B) : ThreeEquations P aV e := by
    intro N t
    exact ⟨chart_diagonal_source_square P aV e N,
      chart_dnc_square P aV e N, chart_normal_integration_square P aV e N t⟩
  have hrev (C B : Chart V d) (e : Map C B)
      (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
      r P aV e ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
          (delta P aV B).symm = (delta P aV C).symm ≪≫ q P aV e N := by
    exact reverse_square _ _ _ _ _ (chart_dnc_square P aV e N)
  have hi (C : Chart V d) : Identity P aV C := by
    intro N
    have he := (chart_epsilon_pasting P aV).1 C N
    have hq := transport_identity _
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X)
      (alpha P aV C) (q P aV (Map.id C) N) (eps P aV (Map.id C) N)
      (chart_diagonal_source_square P aV (Map.id C) N) he
    exact ⟨he, hq, transport_identity _
      (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X)
      (delta P aV C).symm (r P aV (Map.id C)) (q P aV (Map.id C) N)
      (hrev C C (Map.id C) N) hq⟩
  have hc (C B A : Chart V d) (v : Map C B) (e : Map B A) :
      Composition P aV v e := by
    intro N
    have he := (chart_epsilon_pasting P aV).2 C B A v e N
    have hq := transport_composition _ _ _
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom)
      (alpha P aV C) (alpha P aV B) (alpha P aV A)
      (q P aV v N) (q P aV e N) (q P aV (v.comp e) N)
      (eps P aV v N) (eps P aV e N) (eps P aV (v.comp e) N)
      (chart_diagonal_source_square P aV v N)
      (chart_diagonal_source_square P aV e N)
      (chart_diagonal_source_square P aV (v.comp e) N) he
    exact ⟨he, hq, transport_composition _ _ _
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom)
      (delta P aV C).symm (delta P aV B).symm (delta P aV A).symm
      (r P aV v) (r P aV e) (r P aV (v.comp e))
      (q P aV v N) (q P aV e N) (q P aV (v.comp e) N)
      (hrev C B v N) (hrev B A e N) (hrev C A (v.comp e) N) hq⟩
  exact ⟨fun C => ⟨hm C _ (coordinate C), hs C _ (coordinate C), hi C⟩,
    fun C B A v e => ⟨hm C B v, hs C B v, hc C B A v e⟩⟩

end WeilConjectures.PurityFiniteSetting.ChartComparisons
