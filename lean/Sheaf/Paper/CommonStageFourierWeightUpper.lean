/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.CommonStageConstituentNonexceptional
public import Sheaf.Paper.AdicPunctualWeights
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Sheaf.Paper.WeilFourierPlancherel
import Sheaf.Paper.PbcCoefficientTwists
import Sheaf.Paper.WeilComplexTraceFunction
import Sheaf.Paper.LisseIntegralSmallCoefficients
import Sheaf.Paper.PbcQbarCategory
import Sheaf.Paper.WeilFourierInversion
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.LocalFrobeniusTrace
import Mathlib.LinearAlgebra.Trace
import Sheaf.Paper.LocalFrobeniusTransportNormalization
import Sheaf.Paper.PointFibreEquivalence
import Sheaf.Paper.RationalStalkExact
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
import Sheaf.Paper.CommonStageFourierTransform
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.IntrinsicQbarCategory
import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy

/-! # Upper weight of a Fourier partner in the common-stage Weil category

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-p-dl-a1-fourier-weight,
upper weight proposition, order 3121 (blueprint: prop-a1-fourier-weight-upper).

Every sheaf, purity condition and Fourier isomorphism uses the recorded common-stage
interfaces. Ordinary sheaf direct image is formed before the signed shift by one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The actual ordinary middle extension [1] in the recorded fixed-pair category.
The first functor is ordinary j_* on Weil sheaves, the second includes the heart,
and the third tensors with the canonically descended constant coefficient line [1].
The forgetful comparisons in CommonStageCurveWeilMiddleExtension identify its
carrier with (qbarCurveOrdinaryPushforward M)[1]. No Rj_* is used.
Source: blueprint upper weight proposition (blueprint: prop-a1-fourier-weight-upper). -/
def sfAffineShiftedMiddleExtension (F : FourierSetting.{u}) (A : SfAffineLineOpen F)
    (M : sfCommonStageWeilSheaf F.field F.coefficients.l F.coefficients.different
      A.U F.coefficients.Qbar) :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar :=
  (qbarAffineWeilShift F).obj
    ((qbarCurveWeilOrdinaryPushforward F.field F.coefficients.l F.coefficients.different
      F.coefficients.Qbar (SfAffineLineOpen.curve F A)).obj M).obj

/-- Fourier transform for an arbitrary base-field character psi. The recorded
common-stage transform is used with its actual evaluation kernel, multiplied by
the unique trace-pairing coefficient expressing psi in the fixed prime character.
Source: def-fd-transform and def-fd-additive-character, rank-one application
(blueprint: prop-a1-fourier-weight-upper). -/
def sfAffineFourierTransformForCharacter (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (ψ : AddChar F.field.k₀ F.coefficients.Qbar)
    (c : Compactification (fourierModelSnd F PUnit.{u + 1}).left)
    (K : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar) :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar :=
  letI := (fourierSquareModel_geometry F PUnit.{u + 1}).1
  letI := (fourierSquareModel_geometry F PUnit.{u + 1}).2.1
  letI : IsNoetherian
      (pullback (fourierAffineModel F PUnit.{u + 1}).hom
        (fourierAffineModel F PUnit.{u + 1}).hom) :=
    (fourierSquareModel_geometry F PUnit.{u + 1}).2.2
  letI : CharP Γ(pullback (fourierAffineModel F PUnit.{u + 1}).hom
      (fourierAffineModel F PUnit.{u + 1}).hom, ⊤) F.field.p :=
    fourierSquareModel_characteristic F PUnit.{u + 1}
  let b : Γ(pullback (fourierAffineModel F PUnit.{u + 1}).hom
      (fourierAffineModel F PUnit.{u + 1}).hom, ⊤) :=
    (pullback.fst (fourierAffineModel F PUnit.{u + 1}).hom
        (fourierAffineModel F PUnit.{u + 1}).hom ≫
        (fourierAffineModel F PUnit.{u + 1}).hom).appTop
      ((Scheme.ΓSpecIso (.of F.field.k₀)).inv.hom (sfFourierCharacterScale F Ψ hΨ ψ))
  let ev : Γ(pullback (fourierAffineModel F PUnit.{u + 1}).hom
      (fourierAffineModel F PUnit.{u + 1}).hom, ⊤) :=
    AffineSpace.stdPairing PUnit.{u + 1} (Spec (.of F.field.k₀))
  commonStageFourierTransform F (fourierModelFst F PUnit.{u + 1})
    (fourierModelSnd F PUnit.{u + 1}) c
    (fourierAdicKernel F (fourierAffineModel F PUnit.{u + 1}).hom
      (fourierAffineModel F PUnit.{u + 1}).hom Ψ (b * ev)) 1 K

/-- Compatibility with the recorded standard affine transform for the trace character.
Source: def-fd-transform, rank-one normalization
(blueprint: prop-a1-fourier-weight-upper).
Proof: uniqueness in the trace-pairing specification makes the coefficient of
Psi composed with trace equal to one. Its constant global section is one, so the
kernel is the standard evaluation kernel. The same compactification, pullback,
tensor, shift and compact-support functors give the comparison. -/
theorem sfAffineFourierTransformForCharacter_trace (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (c : Compactification (fourierModelSnd F PUnit.{u + 1}).left)
    (K : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar) :
    Nonempty (sfAffineFourierTransformForCharacter F Ψ hΨ
        (fourierTraceBaseCharacter F Ψ) c K ≅
      affineCommonStageFourierTransform F PUnit.{u + 1} Ψ c K) := by
  sorry

/-- The Fourier partner of a nonzero irreducible nonexceptional lisse Weil sheaf
pure of real weight w, if pure of real weight v, has v at most w+1.
Source: main-20261015 sk-p-dl-a1-fourier-weight, order 3121
(blueprint: prop-a1-fourier-weight-upper).

Proof, following the node's eight steps:
1. Apply prop-fd-zero-extension-comparison. The complement of the dense open is
finite. Obtain FT(j_!M[1])=G[1] and 0 to B' to G to j'_*M' to 0, with B' lisse
on the dual line and squared local eigenvalue norms at most q_y^w. Put r=rank M>0
and b=rank B'>=0, constant on the connected opens.
2. At a rational point over a closed point y of degree e dividing n, restrict to
Spec kappa(y). By common-stage calculus descend the object and inverse Weil map
to one finite field E. Point-fibre equivalence gives a free lattice in its finite
E-space. The local-power lemma and local-Frobenius transport normalization identify
the rational-point operator with F_y^(n/e). Triangularize, including repeated
and nonsemisimple eigenvalues. Purity and the triangle inequality bound the two
trace norms by r q^(nw/2) and b q^(nw/2), respectively.
3. Compact-support base change and Weil equivariance identify the traces of
j_!M[1] with minus the trace on U and zero off U. There are q^n affine-line
points, so its squared trace energy is at most r^2 q^(n(w+1)).
4. Plancherel bounds the squared trace energy of G by r^2 q^(n(w+2)); that of
B' is at most b^2 q^(n(w+1)). The shift signs disappear on squaring.
5. Rational-stalk exactness gives the Frobenius-equivariant stalk sequence on U'.
Block upper triangular matrices give trace additivity for every power; with the
same rational/closed-point normalization this says t_M'=t_G-t_B'.
6. Sum |a-c|^2 <= 2|a|^2+2|c|^2 and enlarge to the whole line. Since q>1,
the energy on U' is at most C q^(n(w+2)), with C=2(r^2+b^2)>0 independent of n.
This calculation holds for every real w, including negative and fractional w.
7. M' is nonzero: otherwise Fourier inversion makes (j_*M)[1](-1) zero. Cancel
the shift and the invertible rank-one Tate line, then restrict to U to contradict
M nonzero. Neither irreducibility nor nonvanishing of M' is an added hypothesis.
8. The dense open U' of the line is a smooth geometrically connected affine
curve. Apply sk-l-dl-a1-energy to M', v, B=w+2 and this positive C. It gives
v <= (w+2)-1=w+1. All constructions above use their adic common-stage versions;
no equivalence with the older pro-etale WeilSheaf category is assumed. -/
theorem commonStage_fourierPartner_weight_le_add_one (F : FourierSetting.{u})
    (iota : F.coefficients.Qbar ≃+* ℂ)
    (ψ : AddChar F.field.k₀ F.coefficients.Qbar) (hψ : ψ ≠ 1)
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (c : Compactification (fourierModelSnd F PUnit.{u + 1}).left)
    (A A' : SfAffineLineOpen F)
    (M : sfCommonStageWeilSheaf F.field F.coefficients.l F.coefficients.different
      A.U F.coefficients.Qbar)
    (M' : sfCommonStageWeilSheaf F.field F.coefficients.l F.coefficients.different
      A'.U F.coefficients.Qbar)
    (hMlisse : HasCommonStageLisseLattice F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFiber A.U).left M.obj.carrier)
    (hMnonzero : ¬ IsZero M)
    (hMirreducible : ∀
      (G : sfCommonStageWeilSheaf F.field F.coefficients.l F.coefficients.different
        A.U F.coefficients.Qbar) (i : G ⟶ M), Mono i →
      HasCommonStageLisseLattice F.coefficients.l F.coefficients.Qbar
        (F.field.geometricFiber A.U).left G.obj.carrier → IsZero G ∨ IsIso i)
    (hne : SfIsConstituentNonexceptional F A Ψ hΨ ψ M) (w v : ℝ)
    (hw : SfIsPunctuallyPureOfWeight F.field F.coefficients.l F.coefficients.different
      F.coefficients.Qbar A.U iota M w)
    (hM'lisse : HasCommonStageLisseLattice F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFiber A'.U).left M'.obj.carrier)
    (hFT : Nonempty
      (sfAffineFourierTransformForCharacter F Ψ hΨ ψ c
          (sfAffineShiftedMiddleExtension F A M) ≅ sfAffineShiftedMiddleExtension F A' M'))
    (hv : SfIsPunctuallyPureOfWeight F.field F.coefficients.l F.coefficients.different
      F.coefficients.Qbar A'.U iota M' v) :
    v ≤ w + 1 := by
  sorry

end WeilConjectures
