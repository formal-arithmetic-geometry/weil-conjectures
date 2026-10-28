/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.NormalizedSmoothOrientationUnits

public import Sheaf.Paper.SmoothOrientationPuritySquares
public import Sheaf.Paper.SmoothOrientationStageExchange

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.FiniteCoefficientSmoothPurity
public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.AdmissibleVerdierExchange
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.AdicPurityScalarNaturality
public import Sheaf.Paper.RationalSmoothPurityCanonical
import all Sheaf.Paper.FiniteReductionOfPurity
import all Sheaf.Paper.AdicPurityScalarNaturalityData
import Sheaf.Paper.FiniteCoefficientDirectImage
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Algebra.Homology.SitePerfectScalarHomComparison
import Sheaf.Paper.CommonStageSmoothOperationIdentification
import Sheaf.Paper.RationalScalarComparisonIdentification
import Sheaf.Paper.FiniteCoefficientHomChange
import Sheaf.Paper.PurAdicReconstruction
import Sheaf.Paper.FiniteTorStability

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: lem-pod-smooth-oriented-exchange-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] CategoryTheory.Functor.mapIso CategoryTheory.Iso.trans
  smoothOrientationDatumUnit

/-- Site exchange comparisons under the stipulated smooth orientation.

Finite gamma is `smoothPurityMap` at the coefficient unit. Integral gamma is the
fixed normalized family `I`, whose finite reductions are required here to equal
those very finite smooth-purity maps. Rationalization and the common-stage functors
are applied to the same arrows. There is no existential choice of a new purity
family in this assertion. The site-perfect object occurs in the exchange equation,
and admissibility is used to form the exchange isomorphisms at the two stages.
The final transport uses `RHom(K, gamma.inv)` and the evaluation-transposed Hom map
into the source twist, followed by ordinary direct image.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: lem-pod-smooth-oriented-exchange-comparisons).

Proof:

1. Apply [thm-pur-finite-reduction-of-purity] to $f=a_X$ and the coefficient unit on $s$. Its
vertical arrows are the six-operation finite-reduction maps of [def-pur-finite-reduction-
comparisons]: on $Lf^*K(d)[2d]$ the pullback, twist and shift comparison, which at the coefficient
unit is $h_Q$, and on $Rf^!K$ the unique arrow whose compact-support transpose is the reduced
counit, which at the unit is the exceptional-adjunction comparison $z_Q$. So the theorem gives
$z_Q Q_X\gamma_\Lambda=\gamma_{\Lambda'}h_Q$ for finite quotients. All hypotheses hold: $a_X$ is
smooth separated of pure relative dimension $d$, both schemes are separated finite type over $k$,
and the coefficient unit has Tor amplitude $[0,0]$. This uses the diagonal-purity reduction
theorem, without a properness or finite-field-descent hypothesis. For any coefficient square of
this form, compose on the left with $\eta_{\Lambda'}$ and on the right with $Q_X\eta_\Lambda$. The
two inverse identities give $\eta_{\Lambda'}z_Q=h_Q Q_X\eta_\Lambda$. Thus the inverse square
follows from the forward square, for every stage treated below.

2. For integral reduction, [thm-pur-adic-reconstruction] says that the specified integral purity
map reduces to exactly the finite purity map under the canonical comparisons, at every $n$. This
is the required forward square. Use the simultaneous family specified in the question: [lem-pur-
adic-purity-scalar-naturality] supplies its integral-extension equation $b\,C(\gamma_E)=\gamma_F
a$. At the coefficient unit its $a$ is $h_Q$, and its $b$ is $z_Q$: the statement explicitly
defines $b$ as the exceptional-adjunction transpose of scalar extension of the counit after the
inverse compact-support comparison. It also identifies completed integral scalar extension with
ordinary derived tensor. Therefore its equation is precisely our integral-extension square. No
uniqueness of lifts or inference of equality of integral maps from equality of all reductions is
used.

3. At rationalization, [thm-pur-rational-and-qbar-purity] identifies the purity map with
rationalization of the adic map. [lem-pur-rational-scalar-comparison-identification] identifies
the localized source comparison with the specified tensor/twist/shift comparison and the localized
exceptional comparison with the counit-preserving mate. Applying rationalization to the integral
square consequently gives the square with $h_Q,z_Q$, including finite field extensions. For a
common-stage extension use [lem-pur-common-stage-smooth-operation-identification]: its two
functors and their map actions are the stipulated smooth and exceptional operations, and equations
of compatible transformations retain their finite-stage representatives. Represent our square at a
common finite field; it is the preceding rational square there, and hence is the asserted square
in the common-stage category. Step 1's inverse calculation applies to each of these squares.

4. Now assume the exceptional admissibility and site-perfect hypotheses on $K$ in the question.
[thm-sf-ctf-stability] gives the bounded constructible finite-Tor domains for $C=Ra_{X!}K$, $D_XK$
and their ordinary direct images at finite level, and its higher-stage clauses give the derived-
complete, rational and common-stage domains. In particular the coefficient unit, its exceptional
image, and the internal Homs used here lie in the indicated domains. For finite quotients the
comparison on $X$ is the evaluation-transpose isomorphism of [lem-fix-site-perfect-scalar-hom],
applied with first variable $K$. The point comparison is the finite-Tor internal-Hom map of [thm-
coef-finite-hom], applied on $s$ to $C$ and the point dualizing object. The ordinary-direct-image
comparison for $D_XK$ is [lem-coef-finite-direct-image], in its explicitly stated pro-etale form.
These statements do not require the quotient ring to be flat. All other operation comparisons,
their evaluations and adjunction units and counits are those preserved by [lem-fix-operation-
reduction]. In particular we do not infer finite-quotient ordinary-direct-image comparison from
that elementary operation lemma.

5. Apply [fix-cor-verdier-exchange] to $f=a_X$ and $Y=s$. Its structure maps are $a_X$ and
$\operatorname{id}_s$. The latter has the identity adjunction, cohomological-dimension bound zero
and zero interval shifts, so is admissible; $a_X$ is admissible by hypothesis. The exchange is the
canonical evaluation-transposed one of [def-sf-verdier-exchange-data]. Its asserted coefficient
compatibility is therefore the square for the actual dual scalar arrows and counit-normalized
ordinary-direct-image arrow defined there. Its source is $Q_sD_sC$ and its target is
$Ra_{X*}D_XK'$. On the source, evaluation coefficient change gives $\delta_{Q,C}$; changing the
compact-support input from $Q_sC$ to $C'$ gives precomposition by $u_Q^{-1}$, namely
$D_s(u_Q^{-1})$. On the target the ordinary-direct-image arrow followed by Hom comparison and the
dualizing mate is exactly $R_Q$. Thus the compatibility assertion, with these endpoints and the
stipulated comparisons verified in step 4, reads $$R_Q
Q_s(e_\Lambda)=e_{\Lambda'}D_s(u_Q^{-1})\delta_{Q,C}.$$ This also fixes the direction of
$u_Q^{-1}$; contravariance would make $D_s(u_Q)$ have the wrong source.

6. Write $c_\omega:Q_XD_XK\to D_XK'$ and $c_H:Q_XP_\Lambda(K)\to P_{\Lambda'}(K')$ for evaluation-
transposed Hom comparison followed by $z_Q$ and $h_Q$, respectively. Naturality in the second Hom
variable, with step 1's inverse square, gives $$c_H
Q_X(\theta_\Lambda)=\theta_{\Lambda'}c_\omega.$$ Explicitly, transpose both sides: their
evaluations are coefficient-changed evaluation into $Q_X\omega_\Lambda$ followed by $h_Q
Q_X\eta_\Lambda$, respectively by $\eta_{\Lambda'}z_Q$. These are equal by the already proved
square, so the adjunction bijection gives equality of the arrows. The evaluation-preserving
comparisons, natural in the second Hom variable, are those of [lem-fix-site-perfect-scalar-hom] on
$X$ at finite quotients (first variable $K$) and of [lem-fix-operation-reduction] at the other
stages. Let $b_T:Q_sRa_{X*}T\to Ra_{X*}Q_XT$ be the ordinary comparison. Its naturality ([lem-
coef-finite-direct-image] at finite quotients, [lem-fix-operation-reduction] otherwise) gives $b_P
Q_s(Ra_{X*}\theta)=Ra_{X*}(Q_X\theta)b_D$. Consequently, for $R_Q^H=Ra_{X*}(c_H)b_P$, the
preceding equality gives $$R_Q^H Q_s(Ra_{X*}\theta_\Lambda)=Ra_{X*}(\theta_{\Lambda'})R_Q.$$
Compose step 5's square with $Ra_{X*}\theta_{\Lambda'}$ and substitute this identity. The
resulting square is the oriented square, and its right arrow is $R_Q^H$, the specified
tensor/internal-Hom comparison into $P_{\Lambda'}(K')$. This calculation identifies the arrow
itself rather than only its source and target.
-/
theorem smoothOrientedExchangeComparisons
    (P : PurityFiniteSetting.{u})
    (S : SixFunctorOperationDatum P.field P.coefficients P.extension P.level P.level_pos)
    {X : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (aX : X ⟶ Spec (.of P.field.k))
    [aX.IsOver (Spec (.of P.field.k))]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (d : ℕ) [SmoothOfRelativeDimension d aX]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := aX))
    (I : AdicPurityScalarNaturality.Data P.field P.coefficients aX d T)
    (c : Compactification aX)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) :
      (P.finiteReduction m hm hmn X).map (P.smoothPurityMap aX d
          (smoothOrientationDatumUnit P S).obj
          (smoothOrientationDatumUnit P S).property) ≫
        P.finiteReductionExceptionalComparison m hm hmn aX d
          (smoothOrientationDatumUnit P S).obj
          (smoothOrientationDatumUnit P S).property =
      (P.finiteReductionSourceComparison m hm hmn aX d
        (smoothOrientationDatumUnit P S).obj).hom ≫
        (P.finiteReductionSetting m hm).smoothPurityMap aX d
          ((P.finiteReduction m hm hmn (Spec (.of P.field.k))).obj
            (smoothOrientationDatumUnit P S).obj)
          (P.finiteReduction_preserves_ctf m hm hmn (Spec (.of P.field.k))
            (smoothOrientationDatumUnit P S).obj
            (smoothOrientationDatumUnit P S).property) ∧
      canonicalFiniteInversePuritySquare P aX d
        (smoothOrientationDatumUnit P S).obj
        (smoothOrientationDatumUnit P S).property m hm hmn ∧
      (∀ E, ∃ core : CompletedUnitPullback.Core P.coefficients.l E.val aX,
        specifiedIntegralUnitPurityNormalization P aX d T I E core) ∧
      (∀ E n, specifiedUnitPurityReductionSquare P aX d T I E n) ∧
      (∀ E F h,
        specifiedUnitPurityScalarSquare P aX d T I E F h (𝟭 _) ∧
        specifiedUnitPurityScalarSquare P aX d T I E F h
          (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
            P.coefficients.Qbar (AdicPurityScalarNaturality.fieldStage
              P.field P.coefficients F) X) ∧
        specifiedUnitPurityScalarSquare P aX d T I E F h
          (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
            P.coefficients.Qbar (AdicPurityScalarNaturality.fieldStage
              P.field P.coefficients F) X ⋙
          AdicSmoothDualizing.modelScalar (RationalSmoothPurityCanonical.stageSetting P F) X ⋙
          AdicSmoothDualizing.commonInclusion
            (RationalSmoothPurityCanonical.stageSetting P F) X)) ∧
      (∀ E, specifiedUnitPurityRationalizationSquare P aX d T E c) ∧
      specifiedCommonUnitPuritySquare P aX d T c ∧
      (∀ E F h,
        specifiedRationalUnitPurityScalarSquare P aX d T E F h c (𝟭 _) ∧
        specifiedRationalUnitPurityScalarSquare P aX d T E F h c
          (AdicSmoothDualizing.modelScalar (RationalSmoothPurityCanonical.stageSetting P F) X ⋙
            AdicSmoothDualizing.commonInclusion
              (RationalSmoothPurityCanonical.stageSetting P F) X)) ∧
      (∀ s : SmoothOrientationCoefficient P,
        ∀ K₀ : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
          P.coefficients.Qbar X (s.stage P),
        ∀ _hK : smoothOrientationSitePerfect P.coefficients.l P.coefficients.Qbar X (s.stage P) K₀,
        canonicalExchangeAtStage P aX d s K₀) := by
  sorry

end WeilConjectures
