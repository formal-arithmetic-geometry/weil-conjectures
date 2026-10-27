module

public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.PurityCoprojection
public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization
public import Sheaf.Paper.StandingExceptionalComposition
public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.AlgebraicGeometry.RegularImmersionPureCodimension
public import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.SmoothPurityMap
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.ProjectionMateExact
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.AlgebraicGeometry.Morphisms.Flat

public import Sheaf.Paper.RegularImmersionPurityComparison
public import Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility
public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure
import Sheaf.Paper.PurityCompositionCoherence
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.RingTheory.Etale.LocalDimension

/-! # Étale locality of the specified smooth-purity orientation

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(i)--(ii)
(blueprint: lem-pur-etale-orientation-locality).

The comparison is the actual five-arrow exceptional paste. The equation compares
only the specified diagonal orientations and their canonical co-projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

namespace AlgebraicGeometry.ProEtale.RegularImmersionPurity

section Square
variable (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X U V : Scheme.{u}}
  [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [IsSeparated (Z ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
  [QuasiCompact (U ↘ Spec (.of P.field.k))]
  [IsSeparated (U ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
  [QuasiCompact (V ↘ Spec (.of P.field.k))]
  [IsSeparated (V ↘ Spec (.of P.field.k))]
  (i : Z ⟶ X) (e : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
  [i.IsOver (Spec (.of P.field.k))] [e.IsOver (Spec (.of P.field.k))]
  [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
  [IsClosedImmersion i] [IsClosedImmersion iU]
  [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
  [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]

/-- The five-arrow paste, with the coefficient pullback written explicitly.
Each exceptional compositor is the standing adjunction mate; each rho is the
recorded counit-normalized étale comparison. Source: Step 4(i)
(blueprint: lem-pur-etale-orientation-locality). -/
def etaleOrientationComparison [Etale v] (sq : IsPullback iU v e i) (c : ℕ) :
    (exceptional P iU).obj (P.diagonalTwist U c) ⟶
      (P.smoothPurityPullback v).obj ((exceptional P i).obj (P.diagonalTwist X c)) :=
  letI := FiniteEtaleNormalization.compactification P iU
  letI := FiniteEtaleNormalization.compactification P e
  letI := FiniteEtaleNormalization.compactification P v
  letI := FiniteEtaleNormalization.compactification P i
  letI := FiniteEtaleNormalization.compactification P (iU ≫ e)
  letI := FiniteEtaleNormalization.compactification P (v ≫ i)
  (exceptional P iU).map
    ((P.compositionTwistPullback e c).inv ≫
      (rhoIso P e (P.diagonalTwist X c) (twist_bounded P c)).inv) ≫
    (compIso P iU e (P.diagonalTwist X c) (twist_bounded P c)).inv ≫
    (rightDerivedUpperShriekCongr (ModuleCat.{u + 1} P.Coefficient) sq.w).hom.app
      (P.diagonalTwist X c) ≫
    (compIso P v i (P.diagonalTwist X c) (twist_bounded P c)).hom ≫
    (rhoIso P v ((exceptional P i).obj (P.diagonalTwist X c))
      (exceptional_bounded P i _ (twist_bounded P c))).hom

/-- The orientation equation, using the geometric conclusions as proof arguments.
These proofs only install source-implied instances; they are conclusions of the
locality theorem, never extra hypotheses. Source: Step 4(ii)
(blueprint: lem-pur-etale-orientation-locality). -/
def EtaleOrientationEquation (sq : IsPullback iU v e i) (c : ℕ)
    (hi : WeilConjectures.PurityConventions.IsRegularOfPureCodimension i c)
    [Smooth (X ↘ Spec (.of P.field.k))] [IsRegular Z]
    (hv : Etale v) (hU : Smooth (U ↘ Spec (.of P.field.k))) (hV : IsRegularScheme V)
    (hiU : WeilConjectures.PurityConventions.IsRegularOfPureCodimension iU c) : Prop :=
  letI := hv
  letI := hU
  letI := hV.2
  comparison P iU c hiU ≫ etaleOrientationComparison P i e v iU sq c =
    (P.compositionTwistPullback v 0).inv ≫
      (P.smoothPurityPullback v).map (comparison P i c hi)

end Square

/-- The rank-zero diagonal orientation is the normalized unit orientation eta.
Source: Step 4(i), rank-zero chart normalization
(blueprint: lem-pur-etale-orientation-locality). -/
def EtaleUnitOrientation (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e] : Prop :=
  letI := (Etale.iff_smoothOfRelativeDimension_zero e).mp inferInstance
  letI := FiniteEtaleNormalization.compactification P e
  letI := P.noetherian (X ↘ Spec (.of P.field.k))
  letI := P.noetherian (U ↘ Spec (.of P.field.k))
  P.chartDualizingUnit e ≪≫
      P.chartOrdinaryOrientation 0 e (X ↘ Spec (.of P.field.k)) ≪≫
      eqToIso (compositionEtalePowerZero P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates U) ≪≫ smoothPurityUnitIso P.Coefficient U =
    FiniteEtaleNormalization.eta P e


/-- Compatibility of B with the specified co-projections. Both co-projections
are quantified under their exact projection/counit characterizations. This is the
recorded compatibility square for every invertible finite-Tor coefficient, hence
for each Tate shift. Source: Step 4(ii)
(blueprint: lem-pur-etale-orientation-locality). -/
def EtaleCoprojectionCompatibility
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) (e : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    [i.IsOver (Spec (.of P.field.k))] [e.IsOver (Spec (.of P.field.k))]
    [IsClosedImmersion i] [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v] [Etale v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [IsClosedImmersion iU]
    (sq : IsPullback iU v e i)
: Prop :=
  ∀ (K L : Etale.DerivedCategoryModule P.Coefficient X)
    (_hK : FiniteEtaleNormalization.domain P X K) (_hL : FiniteEtaleNormalization.domain P X L)
    (_hInv : Etale.DerivedCategory.isInvertible P.Coefficient X L)
    (co_i : (FiniteEtaleNormalization.exceptional P i).obj
        (Etale.DerivedCategory.etaleDerivedTensor P.Coefficient X K L) ≅
      Etale.DerivedCategory.etaleDerivedTensor P.Coefficient Z
        ((FiniteEtaleNormalization.exceptional P i).obj K)
        ((FiniteEtaleNormalization.pull P i).obj L))
    (co_iU : (FiniteEtaleNormalization.exceptional P iU).obj
        (Etale.DerivedCategory.etaleDerivedTensor P.Coefficient U
          ((FiniteEtaleNormalization.pull P e).obj K) ((FiniteEtaleNormalization.pull P e).obj L)) ≅
      Etale.DerivedCategory.etaleDerivedTensor P.Coefficient V
        ((FiniteEtaleNormalization.exceptional P iU).obj
          ((FiniteEtaleNormalization.pull P e).obj K))
        ((FiniteEtaleNormalization.pull P iU).obj ((FiniteEtaleNormalization.pull P e).obj L)))
    (_hco_i : FiniteEtaleNormalization.etaleCoprojectionProperty P i K L co_i)
    (_hco_iU : FiniteEtaleNormalization.etaleCoprojectionProperty P iU
      ((FiniteEtaleNormalization.pull P e).obj K)
      ((FiniteEtaleNormalization.pull P e).obj L) co_iU),
    (FiniteEtaleNormalization.exceptional P iU).map
        (FiniteEtaleNormalization.coprojectionTensorPullback P.Coefficient e K L).hom ≫
        co_iU.hom ≫
        FiniteEtaleNormalization.coprojectionTensorHom P.Coefficient V
          (FiniteEtaleNormalization.coprojectionRhoComparison P i e v iU sq.w K).hom
          (FiniteEtaleNormalization.pullbackComposition P i e v iU sq.w L).hom =
      (FiniteEtaleNormalization.coprojectionRhoComparison P i e v iU sq.w
        (Etale.DerivedCategory.etaleDerivedTensor P.Coefficient X K L)).hom ≫
        (FiniteEtaleNormalization.pull P v).map co_i.hom ≫
        (FiniteEtaleNormalization.coprojectionTensorPullback P.Coefficient v
          ((FiniteEtaleNormalization.exceptional P i).obj K)
          ((FiniteEtaleNormalization.pull P i).obj L)).hom

/-- All clauses of étale locality, with geometric consequences and their proof
instances bound inside the conclusion. No smoothness or regularity after base change
is imposed as a further hypothesis. Source: Step 4(i)--(ii)
(blueprint: lem-pur-etale-orientation-locality). -/
def EtaleOrientationConclusion
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) (u : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    [i.IsOver (Spec (.of P.field.k))] [u.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsClosedImmersion i]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] [Etale u]
    (sq : IsPullback iU v u i) (c : ℕ)
    (hi : WeilConjectures.PurityConventions.IsRegularOfPureCodimension i c)
    [Smooth (X ↘ Spec (.of P.field.k))] [IsRegular Z] : Prop :=
  ∃ hc : IsClosedImmersion iU, ∃ hv : Etale v,
    ∃ hft : LocallyOfFiniteType (V ↘ Spec (.of P.field.k)),
    ∃ hqc : QuasiCompact (V ↘ Spec (.of P.field.k)),
    ∃ hs : IsSeparated (V ↘ Spec (.of P.field.k)),
    ∃ hvqc : QuasiCompact v, ∃ hvs : IsSeparated v,
    ∃ hiqc : QuasiCompact iU,
    ∃ hU : Smooth (U ↘ Spec (.of P.field.k)),
    ∃ hV : IsRegularScheme V,
    ∃ hVs : Smooth (V ↘ Spec (.of P.field.k)),
  letI := hc
  letI := hv
  letI := hft
  letI := hqc
  letI := hs
  letI := hvqc
  letI := hvs
  letI := hiqc
  letI := hU
  letI := hV.2
  letI := hVs
  ∃ hiU : WeilConjectures.PurityConventions.IsRegularOfPureCodimension iU c,
  EtaleUnitOrientation P u ∧ EtaleUnitOrientation P v ∧
    IsIso (etaleOrientationComparison P i u v iU sq c) ∧
    EtaleCoprojectionCompatibility P i u v iU sq ∧
    EtaleOrientationEquation P i u v iU sq c hi hv hU hV hiU

/-- Étale locality of exactly the diagonal smooth-purity orientation composite.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(i)--(ii)
(blueprint: lem-pur-etale-orientation-locality).

Proof:
1. Use lem-pur-finite-etale-dualizing-normalization for rho and eta. Étale base
   change gives v étale, and smooth-relative-dimension-permanence gives smooth
   structure maps on U and V. Étale local ring maps preserve dimension and are
   flat. Pull back each regular generating sequence: flatness preserves every
   injective multiplication, and the final local quotient is nonzero. Thus iU
   is regular of the same codimension, also for the empty sequence. Smoothness
   over the perfect field gives regularity of V. The rank-zero chart clause of
   lem-pur-diagonal-dnc-chart-normalization identifies both diagonal orientations
   with eta, on affine charts and therefore globally as maps of degree-zero sheaves.
2. The standing exceptional compositor is the adjunction mate of compact-support
   composition. Its invertibility and identity/associativity laws, together with
   normalized rho, give exactly the five-arrow etaleOrientationComparison. The
   square equality identifies the two composites; all its factors are invertible.
3. At the coefficient unit, theta is the unitor: the proper projection mate is
   identity and the open tensor comparison is the unitor. Apply
   thm-pur-composition-coherence to aU=aX u and aV=aZ v. The normalized etale
   dualizing comparison then identifies the actual pulled-back diagonal factors.
4. lem-pur-etale-coprojection-rho-compatibility gives precisely the co-projection
   square in EtaleCoprojectionCompatibility for all invertible finite-Tor inputs,
   in particular for Tate shifts. Its projection transformation is the specified
   one of def-exchange-projection, so no arbitrary endpoint isomorphism is used.
5. Expand pur9-rg-def-phi, paste the orientation equalities of step 3 and the
   co-projection equalities of step 4, and use compositor associativity. This gives
   comparison(iU);B = v*(comparison(i)), with the explicit unit and Tate pullback
   identifications. The finite-clopen component characterization assembles these
   equalities even when component dimensions vary. No Kummer or fundamental class
   identification enters the calculation. -/
theorem etale_orientation_locality
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) (u : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    [i.IsOver (Spec (.of P.field.k))] [u.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsClosedImmersion i]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] [Etale u]
    (sq : IsPullback iU v u i) (c : ℕ)
    (hi : WeilConjectures.PurityConventions.IsRegularOfPureCodimension i c)
    [Smooth (X ↘ Spec (.of P.field.k))] (hZ : IsRegularScheme Z) :
    @EtaleOrientationConclusion P Z X U V _ _ _ _ _ _ _ _ _ _ _ _ _
      i u v iU _ _ _ _ _ _ _ _ _ sq c hi _ hZ.2 := by
  sorry

end AlgebraicGeometry.ProEtale.RegularImmersionPurity
