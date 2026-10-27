module

public import Sheaf.Paper.ChartDiagonalAssemblyData
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.Paper.AffineOrderedIntegrationTransposes
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.AlgebraicGeometry.AffineLinearTraceAction
import Sheaf.AlgebraicGeometry.AffineTraceLinePurity
import all Sheaf.AlgebraicGeometry.VectorIntegrationMate

/-! # Target-open restriction and equality detection for coordinate orientations

Source: blueprint sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, end of Step 4 and inherited Step 9.
(blueprint: lem-pur-chart-target-open-descent).

The affine comparison on a nonseparated base is the transpose of the actual
integration trace, in its ordered ordinary-etale presentation. All comparisons
below are the specified adjunction mates and root-line restriction maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The integration transpose is invertible without absolute separatedness of the base.
Source: vector-bundle purity and the actual integration site comparison
(blueprint: lem-pur-chart-target-open-descent).
Proof: the trivial bundle over the finite-type base is a separated finite-type
morphism. Vector-bundle purity applies over this Noetherian base without absolute
separatedness. The site comparison preserves its integration counit and transpose.
In the trivial frame that trace is the ordered affine trace defining diagonalAffineMate.
Consequently this actual mate is invertible, including rank zero and the empty base. -/
theorem chartTargetAffineMate_isIso (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    letI := P.noetherian aY
    IsIso (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d) := by
  let := P.noetherian aY
  let := affineTraceNoetherian Y d
  have hc : IsIso (Etale.affineTraceCounit P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t D Y (P.diagonalExponent_isUnit aY) d) := by
    unfold Etale.affineTraceCounit Etale.affineTraceAdjunction
    apply Etale.affineTraceAdjunctionTower_counit_isIso
    intro r K
    let := affineTraceNoetherian Y r
    exact Etale.affineTraceLineCounit_isIso P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates t
      (affineTraceTower Y r)
      (affineTraceInvertible P.diagonalExponent Y (P.diagonalExponent_isUnit aY) r)
      (D _ _) K
  unfold diagonalAffineMate
  let c := (Etale.affineLinearCompactComparison P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates Y (P.diagonalExponent_isUnit aY) d).inv ≫
      Etale.affineTraceCounit P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t D Y (P.diagonalExponent_isUnit aY) d
  have := Etale.affine_unit_adjunct_isIso P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates t D Y (P.diagonalExponent_isUnit aY) d hc
    (Iso.refl _) c
  infer_instance

/-- Gamma is the actual integration transpose on any finite-type base. On separated
opens it is the published ordered comparison, by ordered_integration_transposes.
Source: the explicitly specified extension of Gamma in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def chartTargetGamma (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :=
  letI := P.noetherian aY
  letI := P.chartTargetAffineMate_isIso Y aY d t D
  asIso (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d)

/-- The canonical Tate restriction, including the actual etale/pro-etale comparison.
Source: Tate restriction identifications in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def chartTargetTate (P : PurityFiniteSetting.{u}) {B C : Scheme.{u}}
    (b : B ⟶ C) (aC : C ⟶ Spec (.of P.field.k)) (d : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  Dnc.pullComparison P b (P.diagonalTwistEtale C d) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t b (P.diagonalExponent_isUnit aC) d)

/-- T in the target Lambda_U(d)[2d], using canonical Tate restriction.
Source: T = Lj* vartheta_f in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def chartTargetT (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.mapIso
      (P.diagonalDualizingObject d f aY) ≪≫
    P.chartTargetTate U.ι (f ≫ aY) d t

/-- Q is open restriction, exceptional composition and etale identification, followed
by pullback of the inverse actual integration transpose. Coordinates are read in
 the canonically isomorphic ordered affine tower, with no choice of orientation.
Source: the specified formula for Q in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def chartTargetQ (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ affineTraceTower Y d) [Etale e]
    (w : e ≫ affineTraceProjection Y d = U.ι ≫ f)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aY
  letI := P.noetherian (f ≫ aY)
  letI := isNoetherian_of_locallyOfFiniteType U.ι
  letI := affineTraceNoetherian Y d
  letI : IsSeparated (e ≫ affineTraceProjection Y d) := w.symm ▸ inferInstance
  letI := IsSeparated.of_comp e (affineTraceProjection Y d)
  letI := Dnc.compactifiable P f aY
  letI := Dnc.compactifiable P (U.ι ≫ f) aY
  letI : HasCompactification (e ≫ affineTraceProjection Y d) :=
    HasCompactification.of_eq w.symm
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.mapIso
      (P.diagonalDualizingComparison f) ≪≫
    Dnc.pullComparison P U.ι (P.diagonalOrdinaryDualizing f) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U.toScheme).mapDerivedCategory.mapIso
      (P.diagonalEtaleLocality N U.ι f ≪≫
        (P.diagonalDualizingCongr w).symm ≪≫
        (P.diagonalEtaleLocality N e (affineTraceProjection Y d)).symm ≪≫
        (Etale.ordinaryFinitePullback P.Coefficient e).mapIso
          (P.chartTargetGamma Y aY d t D).symm ≪≫
        Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t e
          (affineTraceInvertible P.diagonalExponent Y (P.diagonalExponent_isUnit aY) d) d)


/-- Canonical source-open identification D with omega_(f j), retaining the comparison
unit on both sides. Source: source restriction in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def chartTargetSource (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aY
  letI := P.noetherian (f ≫ aY)
  letI := isNoetherian_of_locallyOfFiniteType U.ι
  letI := Dnc.compactifiable P f aY
  letI := Dnc.compactifiable P (U.ι ≫ f) aY
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.mapIso
      (P.diagonalDualizingComparison f) ≪≫
    Dnc.pullComparison P U.ι (P.diagonalOrdinaryDualizing f) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U.toScheme).mapDerivedCategory.mapIso
        (P.diagonalEtaleLocality N U.ι f) ≪≫
    (P.diagonalDualizingComparison (U.ι ≫ f)).symm

/-- The target-open exceptional base-change identification, including its exact
comparison-unit normalization. Source: target restriction in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def chartTargetBase (P : PurityFiniteSetting.{u})
    {B Y : Scheme.{u}} (d : ℕ) (h : B ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.Opens) :=
  letI := Dnc.compactifiable P h aY
  letI := P.noetherian aY
  letI := isNoetherian_of_locallyOfFiniteType V.ι
  letI := Dnc.compactifiable P (h ∣_ V) (V.ι ≫ aY)
  (ProEtale.upperStar
      (ModuleCat.{u + 1} P.Coefficient) (h ⁻¹ᵁ V).ι).leftDerivedFunctor.mapIso
      (P.diagonalDualizingComparison h) ≪≫
    Dnc.pullComparison P (h ⁻¹ᵁ V).ι (P.diagonalOrdinaryDualizing h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (h ⁻¹ᵁ V).toScheme).mapDerivedCategory.mapIso
        (P.chartOrdinaryBaseChangeData d h aY V.ι (h ∣_ V) (h ⁻¹ᵁ V).ι
          (isPullback_morphismRestrict h V).flip) ≪≫
    (P.diagonalDualizingComparison (h ∣_ V)).symm

/-- Affine target restriction supplies exactly the geometry needed by the normalized
DNC assembly. This is conclusion data, imposing no absolute separatedness on Y.
Source: affine-target restriction in the node proof, Step 1
(blueprint: lem-pur-chart-target-open-descent).
Proof: the open composite is smooth of dimension 0+d=d, separated and finite type.
Apply affineTargetDiagonalDnc to this composite. Each affine target is separated
over k, so its separated finite-type inverse image is in the DNC domain. -/
theorem chartTargetGeometry (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (V : Y.affineOpens) :
    Nonempty (P.ChartAffineDiagonalGeometryData (U.ι ≫ f) aY d V) := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := isNoetherian_of_locallyOfFiniteType U.ι
  let : SmoothOfRelativeDimension d (U.ι ≫ f) :=
    Nat.zero_add d ▸ inferInstanceAs (SmoothOfRelativeDimension (0 + d) (U.ι ≫ f))
  obtain ⟨H, _⟩ := (P.affineTargetDiagonalDnc aY ((U.ι ≫ f) ≫ aY)
    (U.ι ≫ f) rfl d).2 V
      (HasRingHomProperty.appTop @LocallyOfFiniteType (V.1.ι ≫ aY) inferInstance)
  exact ⟨H⟩

/-- The local diagonal formula, under the canonical source and Tate identifications.
The geometry dictionary is quantified universally; it contains only propositions
about the specified restriction, and is supplied by chartTargetGeometry.
Source: restriction of T in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def ChartTargetDiagonalRestriction (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) : Prop :=
  letI := P.noetherian aY
  letI := P.noetherian (f ≫ aY)
  letI : SmoothOfRelativeDimension d (U.ι ≫ f) :=
    Nat.zero_add d ▸ inferInstanceAs (SmoothOfRelativeDimension (0 + d) (U.ι ≫ f))
  ∀ (V : Y.affineOpens) (H : P.ChartAffineDiagonalGeometryData (U.ι ≫ f) aY d V),
    letI := H.separated
    letI := H.finiteType
    letI := H.quasiCompact
    letI := H.smoothDimension
    letI := H.baseFiniteType
    letI := H.baseQuasiCompact
    letI := H.sourceSeparated
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        ((U.ι ≫ f) ⁻¹ᵁ V.1).ι).leftDerivedFunctor.map (P.chartTargetT d f aY U t).hom ≫
      (P.chartTargetTate ((U.ι ≫ f) ⁻¹ᵁ V.1).ι ((U.ι ≫ f) ≫ aY) d t).hom =
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        ((U.ι ≫ f) ⁻¹ᵁ V.1).ι).leftDerivedFunctor.map (P.chartTargetSource f aY U N).hom ≫
      (P.chartTargetBase d (U.ι ≫ f) aY V.1).hom ≫
      (P.chartDiagonalAssemblyData d ((U.ι ≫ f) ∣_ V.1) (V.1.ι ≫ aY) t).hom


/-- The actual coordinate map for any separated finite-type etale chart over a
finite-type base, without an affineness requirement on its source.
Source: Le*(Gamma^-1) c_e in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def chartTargetCoordinate (P : PurityFiniteSetting.{u})
    {B Y : Scheme.{u}} (d : ℕ) (h : B ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : B ⟶ affineTraceTower Y d) [Etale e]
    (w : e ≫ affineTraceProjection Y d = h)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aY
  letI := P.noetherian (h ≫ aY)
  letI := affineTraceNoetherian Y d
  letI : IsSeparated (e ≫ affineTraceProjection Y d) := w.symm ▸ inferInstance
  letI := IsSeparated.of_comp e (affineTraceProjection Y d)
  letI := Dnc.compactifiable P h aY
  letI : HasCompactification (e ≫ affineTraceProjection Y d) :=
    HasCompactification.of_eq w.symm
  P.diagonalDualizingComparison h ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      ((P.diagonalDualizingCongr w).symm ≪≫
        (P.diagonalEtaleLocality N e (affineTraceProjection Y d)).symm ≪≫
        (Etale.ordinaryFinitePullback P.Coefficient e).mapIso
          (P.chartTargetGamma Y aY d t D).symm ≪≫
        Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t e
          (affineTraceInvertible P.diagonalExponent Y (P.diagonalExponent_isUnit aY) d) d)

/-- The coordinatewise target restriction is Cartesian and supplies the restricted
etale chart on the actual inverse-image open. Both square certificates and the
restricted map are conclusions, so the restriction formula has no empty domain.
Source: the constructions U_V, p_V, e_V in the node statement
(blueprint: lem-pur-chart-target-open-descent).
Proof: each affine-line tower step is a polynomial base-change square. Paste
these squares, starting with the identity square in rank zero. Pull back the
etale chart along its top map; the pasted square identifies its source with
h^-1(V). Etaleness is stable under base change. The projection equality follows
from the pullback equations, including empty opens. -/
theorem chartTargetRestrictedChart
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    (U : X.Opens) (e : U.toScheme ⟶ affineTraceTower Y d) [Etale e]
    (w : e ≫ affineTraceProjection Y d = U.ι ≫ f) (V : Y.affineOpens) :
    IsPullback (affineTraceMap V.1.ι d) (affineTraceProjection V.1.toScheme d)
      (affineTraceProjection Y d) V.1.ι ∧
    ∃ eV : ((U.ι ≫ f) ⁻¹ᵁ V.1).toScheme ⟶ affineTraceTower V.1.toScheme d,
      Etale eV ∧
      IsPullback ((U.ι ≫ f) ⁻¹ᵁ V.1).ι eV e (affineTraceMap V.1.ι d) ∧
      eV ≫ affineTraceProjection V.1.toScheme d = (U.ι ≫ f) ∣_ V.1 := by
  let sq := affineTraceMap_isPullback V.1.ι d
  have outer : IsPullback ((U.ι ≫ f) ⁻¹ᵁ V.1).ι ((U.ι ≫ f) ∣_ V.1)
      (e ≫ affineTraceProjection Y d) V.1.ι := by
    rw [w]
    exact (isPullback_morphismRestrict (U.ι ≫ f) V.1).flip
  let eV := sq.lift (((U.ι ≫ f) ⁻¹ᵁ V.1).ι ≫ e)
    ((U.ι ≫ f) ∣_ V.1) (by rw [Category.assoc, outer.w])
  have heV : IsPullback ((U.ι ≫ f) ⁻¹ᵁ V.1).ι eV e
      (affineTraceMap V.1.ι d) := outer.of_bot' sq
  exact ⟨sq, eV, MorphismProperty.of_isPullback heV inferInstance,
    heV, sq.lift_snd _ _ _⟩

/-- The restricted coordinate arrow and its integration-transpose restriction equation.
A representative of each Cartesian affine-space square is quantified universally;
the second Cartesian square says precisely that eV is the restriction of e.
Source: restriction of Q in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def ChartTargetCoordinateRestriction (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ affineTraceTower Y d) [Etale e]
    (w : e ≫ affineTraceProjection Y d = U.ι ≫ f)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) : Prop :=
  letI := P.noetherian aY
  letI := P.noetherian (f ≫ aY)
  letI : SmoothOfRelativeDimension d (U.ι ≫ f) :=
    Nat.zero_add d ▸ inferInstanceAs (SmoothOfRelativeDimension (0 + d) (U.ι ≫ f))
  ∀ (V : Y.affineOpens) (H : P.ChartAffineDiagonalGeometryData (U.ι ≫ f) aY d V),
    letI := H.separated
    letI := H.finiteType
    letI := H.quasiCompact
    letI := H.smoothDimension
    letI := H.baseFiniteType
    letI := H.baseQuasiCompact
    ∀ (_sq : IsPullback (affineTraceMap V.1.ι d) (affineTraceProjection V.1.toScheme d)
        (affineTraceProjection Y d) V.1.ι)
      (eV : ((U.ι ≫ f) ⁻¹ᵁ V.1).toScheme ⟶ affineTraceTower V.1.toScheme d)
      [Etale eV]
      (_sqe : IsPullback ((U.ι ≫ f) ⁻¹ᵁ V.1).ι eV e (affineTraceMap V.1.ι d))
      (wV : eV ≫ affineTraceProjection V.1.toScheme d = (U.ι ≫ f) ∣_ V.1),
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          ((U.ι ≫ f) ⁻¹ᵁ V.1).ι).leftDerivedFunctor.map (P.chartTargetQ d f aY U e w t D N).hom ≫
        (P.chartTargetTate ((U.ι ≫ f) ⁻¹ᵁ V.1).ι ((U.ι ≫ f) ≫ aY) d t).hom =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          ((U.ι ≫ f) ⁻¹ᵁ V.1).ι).leftDerivedFunctor.map
            (P.chartTargetSource f aY U N).hom ≫
        (P.chartTargetBase d (U.ι ≫ f) aY V.1).hom ≫
        (P.chartTargetCoordinate d ((U.ι ≫ f) ∣_ V.1) (V.1.ι ≫ aY) eV wV t D N).hom

/-- Equality is detected on every affine target cover, for the two specified arrows.
This includes empty covers of the empty target and the empty source open.
Source: displayed implication in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def ChartTargetEqualityTest (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ affineTraceTower Y d) [Etale e]
    (w : e ≫ affineTraceProjection Y d = U.ι ≫ f)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) : Prop :=
  ∀ (I : Type v) (V : I → Y.affineOpens) (_hcover : (⨆ i, (V i).1) = ⊤),
    (∀ i, (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      ((U.ι ≫ f) ⁻¹ᵁ (V i).1).ι).leftDerivedFunctor.map (P.chartTargetT d f aY U t).hom =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      ((U.ι ≫ f) ⁻¹ᵁ (V i).1).ι).leftDerivedFunctor.map
        (P.chartTargetQ d f aY U e w t D N).hom) →
      (P.chartTargetT d f aY U t).hom = (P.chartTargetQ d f aY U e w t D N).hom


/-- The ordinary module sheaf Lambda_B(d) on the actual small pro-etale site.
Source: coefficient line in the equality test
(blueprint: lem-pur-chart-target-open-descent). -/
def chartTargetSheaf (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) (d : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent B
      P.diagonalExponent_annihilates (d : ℤ))

/-- The equality test removes the specified orientation and the shift. Full
faithfulness gives unique ordinary endomorphisms, whose derived restrictions are
exactly their ordinary sheaf restrictions. The final clause is their cover detection.
Source: the more precise equality test in the node statement; Stacks 06XS, 03EM, 04TQ
(blueprint: lem-pur-chart-target-open-descent). -/
def ChartTargetSheafTest (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) : Prop :=
  letI := Dnc.compactifiable P f aY
  ∃ ε : (P.diagonalTwist U.toScheme d)⟦-(2 * (d : ℤ))⟧ ≅
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology U.toScheme) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
          (P.chartTargetSheaf U.toScheme d),
    (∀ a : (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.obj
        (P.diagonalDualizing f) ⟶ P.diagonalTwist U.toScheme d,
      ∃! φ : P.chartTargetSheaf U.toScheme d ⟶ P.chartTargetSheaf U.toScheme d,
        (DerivedCategory.singleFunctor _ 0).map φ =
          ε.inv ≫ (shiftFunctor _ (-(2 * (d : ℤ)))).map
            ((P.chartTargetT d f aY U t).inv ≫ a) ≫ ε.hom) ∧
    (∀ (φ : P.chartTargetSheaf U.toScheme d ⟶ P.chartTargetSheaf U.toScheme d)
      (W : U.toScheme.Opens),
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) W.ι).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor _ 0).map φ) =
      (Functor.mapDerivedCategorySingleFunctor
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) W.ι) 0).hom.app
          (P.chartTargetSheaf U.toScheme d) ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) W.ι).map φ) ≫
      (Functor.mapDerivedCategorySingleFunctor
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) W.ι) 0).inv.app
          (P.chartTargetSheaf U.toScheme d)) ∧
    (∀ (a b : (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.obj
        (P.diagonalDualizing f) ⟶ P.diagonalTwist U.toScheme d)
      (φ ψ : P.chartTargetSheaf U.toScheme d ⟶ P.chartTargetSheaf U.toScheme d)
      (_hφ : (DerivedCategory.singleFunctor _ 0).map φ =
        ε.inv ≫ (shiftFunctor _ (-(2 * (d : ℤ)))).map
          ((P.chartTargetT d f aY U t).inv ≫ a) ≫ ε.hom)
      (_hψ : (DerivedCategory.singleFunctor _ 0).map ψ =
        ε.inv ≫ (shiftFunctor _ (-(2 * (d : ℤ)))).map
          ((P.chartTargetT d f aY U t).inv ≫ b) ≫ ε.hom),
      a = b ↔ φ = ψ) ∧
    (∀ (I : Type v) (V : I → Y.affineOpens) (_hcover : (⨆ i, (V i).1) = ⊤)
      (φ ψ : P.chartTargetSheaf U.toScheme d ⟶ P.chartTargetSheaf U.toScheme d),
      (∀ i, (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          ((U.ι ≫ f) ⁻¹ᵁ (V i).1).ι).map φ =
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          ((U.ι ≫ f) ⁻¹ᵁ (V i).1).ι).map ψ) → φ = ψ)

/-- The trace restriction equation in the ordered coordinate adjunction, before
transporting it together with the adjunction to the small pro-etale site.
Source: t_(p_V) C_(d,v) = v* t_p in the node statement
(blueprint: lem-pur-chart-target-open-descent). -/
def ChartTargetTraceRestriction (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) : Prop :=
  letI := P.noetherian aY
  ∀ V : Y.affineOpens,
    letI := isNoetherian_of_locallyOfFiniteType V.1.ι
    Etale.affineTraceExchange P.Coefficient V.1.ι d
        ((Etale.affineTraceRight P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates Y d).obj (Etale.ordinaryFiniteUnit P.Coefficient Y)) ≫
      (Etale.affineTraceLeft P.Coefficient V.1.toScheme d).map
        ((Etale.affineTraceRightBaseChange P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t V.1.ι (P.diagonalExponent_isUnit aY) d
          (Etale.ordinaryFiniteUnit P.Coefficient Y)).hom ≫
          (Etale.affineTraceRight P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates V.1.toScheme d).map
            (Etale.ordinaryFiniteUnitPullback P.Coefficient V.1.ι).hom) ≫
      Etale.affineTraceCounit P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t D V.1.toScheme
        (affineTracePullbackInvertible P.diagonalExponent V.1.ι
          (P.diagonalExponent_isUnit aY)) d =
      (Etale.ordinaryFinitePullback P.Coefficient V.1.ι).map
        (Etale.affineTraceCounit P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t D Y (P.diagonalExponent_isUnit aY) d) ≫
        (Etale.ordinaryFiniteUnitPullback P.Coefficient V.1.ι).hom

/-- Both restriction formulas and equality detection, with the actual integration
transpose on a possibly nonseparated base. The coefficient specialization E=Q_l
is the bottom intermediate field; positivity and the characteristic restriction
are already fields of P. Every normalized presentation is quantified, so none is
an additional orientation hypothesis.
Source: blueprint sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, end of Step 4 and inherited Step 9
(blueprint: lem-pur-chart-target-open-descent).

Proof:
1. Apply lem-pur-chart-cartesian-domain to the chart and target affine opens.
   All source opens, affine spaces and self-products are separated finite type
   over k there, even when Y is nonseparated. These are precisely the geometry
   dictionaries used by the local assembly.
2. For a:D->L, compose with T inverse and apply shift -2d. The root-line normal
   form identifies the object with the degree-zero Lambda_U(d). By
   lem-weil-pbc-derived-single-fully-faithful its endomorphisms come uniquely
   from ordinary module-sheaf endomorphisms. Exact open restriction commutes
   with singles and shifts (lem-sf-exact-functor-derived-triangulated), and the
   site localization is lem-weil-proetale-weakly-etale-localization. Thus their
   restrictions are precisely restrictions of these same sheaf maps.
3. The inverse images of an affine target cover cover U. The uniqueness clause
   of lem-pur-sheaf-hom-cover-gluing detects equality of the sheaf maps, hence
   of a and b. Apply this to T,Q. The empty-cover case is included.
4. On each affine source open of U_V, diagonal-dnc-chart-normalization gives
   the diagonal source factor, normalized DNC factor and zero-section factor.
   Their restrictions agree by dualizing-sigma-cocycle-locality, base change
   and etale locality of thm-pur-dnc-invariance, and base change of vector
   purity with its actual vector-integration-site-comparison. Step 3 glues
   these comparisons to T|_(U_V) = beta delta alpha^-1.
5. The affine trace is the actual integration in its trivial frame. Its target
   restriction is lem-amb-affine-space-top-trace. Transport this equality with
   its adjunction by vector-integration-site-comparison. Invert the resulting
   purity comparison. Affine-ordered-integration-transposes identifies it with
   the ordered Gamma on the separated target open. This is exactly the
   displayed trace equation and the Gamma factor in the local Q formula.
6. The other factors are the open comparison and canonical etale exceptional
   composition. Finite-etale-dualizing-normalization and dualizing-sigma-
   cocycle-locality identify their open restrictions, including every
   comparison unit. Compose with Step 5 to obtain the Q restriction formula.
   Step 3 now proves the displayed implication. For d=0 all shifts and ordered
   lists are zero and every normalization retains the identity; U empty gives
   the unique maps of zero sheaves. -/
theorem chartTargetOpenDescent (P : PurityFiniteSetting.{u})
    (_hE : P.extension = ⊥) {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ affineTraceTower Y d) [Etale e]
    (w : e ≫ affineTraceProjection Y d = U.ι ≫ f)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    P.ChartTargetDiagonalRestriction d f aY U t N ∧
      P.ChartTargetCoordinateRestriction d f aY U e w t D N ∧
      P.ChartTargetTraceRestriction Y aY d t D ∧
      P.ChartTargetSheafTest.{u, v} d f aY U t ∧
      P.ChartTargetEqualityTest.{u, v} d f aY U e w t D N := by
  sorry

end WeilConjectures.PurityFiniteSetting
