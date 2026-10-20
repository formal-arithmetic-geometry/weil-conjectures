/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.SixFunctors.FiniteDualizing
public import Sheaf.Paper.IntegralCompactSupportPrescribedReductions
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.SixFunctors.FiniteMappingAdjunction
public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Paper.DirectImageChangeRingTranspose
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.PointProEtaleSectionsExact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import Sheaf.SixFunctors.CoefTowerNaturalCurrying
public import Sheaf.SixFunctors.NormalizedTowerTensorEvaluation

/-! # Finite adjunctions and quotient transitions

Source: main-20261015, prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-finite-adjunction-transition).

The helpers name the actual mapping complexes H and J, their transition maps,
the prescribed point-section reduction alpha, and the evaluation-defined horizontal.
The theorem states the square in D(R), naturality, and the finite trace identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace FiniteAdjunctionTransition

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The actual integral global mapping complex, with its R-module action.
Source: integral-dualizing proof, paragraph 2, first finite mapping complex
(blueprint: lem-coef-finite-adjunction-transition). -/
def H (r : ℕ) :=
  coefPairingIntegralHom l E X r (integralDualizingFiniteTerm l E D X r)

/-- Restrict the counit-defined tau to completed integral coefficients. The final
comparison is the section-normalized composition of actual restrictions.
Source: integral-dualizing proof, paragraph 2, left vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def restrictedTau (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :=
  (scalarReductionDerivedRestriction l E X m).map
      (integralDualizingExceptionalTransition l E D X hl h) ≫
    (normalizedDVRResCompletedComp l E X D hl h).hom.app
      (integralDualizingFiniteTerm l E D X n)

/-- H_m to H_n is postcomposition by the actual restricted exceptional transition.
Source: integral-dualizing proof, paragraph 2, left vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def HTransition (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (H D l E X m).obj (op K) ⟶ (H D l E X n).obj (op K) :=
  (coefPairingIntegralSections l E X).map
    ((coefficientIntegralInternalHom l E X).map
      (Prod.mkHom (𝟙 (op K)) (restrictedTau D l E X hl h)))

/-- C is exact coefficient-point sections of the integral compact-support Roos limit.
T and e below present the actual finite compact-support reduction tower, including
its transitions. This is the value to which prescribedReductions applies.
Source: integral-dualizing proof, paragraph 2, C=Gamma(s,Ra_!K)
(blueprint: lem-coef-finite-adjunction-transition). -/
abbrev C
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))))) :=
  coefCurryingIntegralSections l E D X T

/-- The coefficient-point dual J_r=RHom_R(C,A_r), contravariant in K.
Source: integral-dualizing proof, paragraph 2, right mapping complex
(blueprint: lem-coef-finite-adjunction-transition). -/
def J
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))))) (r : ℕ) :=
  (C D l E X T).op ⋙ coefCurryingPointHom l E r

/-- Postcomposition in RHom_R(C,-) by the genuine R-linear quotient A_m to A_n.
Source: integral-dualizing proof, paragraph 2, right vertical map
(blueprint: lem-coef-finite-adjunction-transition). -/
def JTransition
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
    {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (J D l E X T m).obj (op K) ⟶ (J D l E X T n).obj (op K) :=
  (ihom ((C D l E X T).obj K)).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
      (coefTraceQuotientMap l E h))

variable
  (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
  (a₀ b₀ : ℤ)
  (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
    DerivedCategory (pbcTowers (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
  (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation (Spec (.of D.k))
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ≅
      compactSupportRestrictedLevel l E (finiteDualizingCompactification D X) n)
  (M : CoefCurryingModels l E D X Q a₀ b₀ T e)

/-- The point-section reduction comparison alpha_r is the scalar adjunct of the
actual Roos projection. Its adjunction has unit x mapped to 1 tensor x; the tower
transition equation fixes its successive-reduction normalization. In particular
this does not choose from point_sections_derived_reduction's Nonempty isomorphism.
Source: integral-dualizing proof, paragraph 2, prescribed reductions
(blueprint: lem-coef-finite-adjunction-transition). -/
def alpha (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
  CoefTower.reductionComparison D l E (finiteDualizingCompactification D X) T e r K

/-- Scalar adjunction on the full mapping complex, defined by base change of
normalized evaluation and the actual scalar adjunction counit. The finite tensor
comparison is normalized on K-flat representatives by M.calculus.
Source: integral-dualizing proof, paragraph 2, scalar-Hom identification
(blueprint: lem-coef-finite-adjunction-transition). -/
def scalarHom (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (H D l E X r).obj (op K) ⟶
      (coefPairingFiniteHom l E X r (integralDualizingFiniteTerm l E D X r)).obj (op K) :=
  (coefPairingIntegralSections l E X).map
    (coefficientEnrichedAdjunctionMap M.calculus.integralClosed (M.calculus.finiteClosed r)
      (coefficientFiniteDerivedExtension l E X r) (coefficientFiniteAdjunction l E X r)
      (M.calculus.finiteTensor r) K (integralDualizingFiniteTerm l E D X r))

/-- The specified horizontal map. The first factor is the evaluation-defined scalar
adjunction from integral Hom to finite Hom. The second factor is the finite mapping
adjunction pairing characterization: insert the
actual compact-support projection, balance scalars, apply projection and evaluation,
then the finite exceptional counit, and curry. In particular no independent alpha_r
is chosen from the point-reduction theorem's Nonempty statement.
Source: integral-dualizing proof, paragraph 2, gamma tilde
(blueprint: lem-coef-finite-adjunction-transition). -/
def finiteHorizontal (r : ℕ)
    (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) :
    (H D l E X r).obj (op K.obj) ⟶ (J D l E X T r).obj (op K.obj) :=
  scalarHom D l E X Q a₀ b₀ T e M r K.obj ≫
    M.finiteArrow l E D X Q a₀ b₀ T e r K

/-- The finite mapping-adjunction square itself in D(R), and its contravariant
naturality in K. Quantified gamma_m and gamma_n carry the finite adjunction's
projection/evaluation/counit characterization through finiteHorizontal. C and its
finite projections are the prescribed integral compact-support construction.
The realization equations fix scalar adjunction, the action on the actual tau,
and the finite exceptional counits. They normalize the construction witnesses
provided by the cited pairing, trace-rectification and coaugmentation nodes.
All interval endpoints and every morphism of
integral inputs are quantified. The final clause is the unchanged etale trace identity.

Source: main-20261015, prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-finite-adjunction-transition).

Complete proof plan from the DAG (canonical scalar tensor reassociations understood):

1. Fix $m\ge n$, put $A=A_m$, $B=A_n$, and write $T_W=-\otimes^L_{A_W}B_W$ and $U_W$ for
restriction, also on the point module categories. All sites are taken in the module universe.
Use the fixed compactification in the statement throughout. Let
$d:C_m\otimes_A^LB\xrightarrow{\sim}C_n$ be its coefficient comparison followed by point
sections, and let $\alpha_r:C\otimes_R^LA_r\xrightarrow{\sim}C_r$ be the comparisons assumed in
the statement. Their specified successive-reduction normalization gives
$$d\circ(\alpha_m\otimes_A^LB)=\alpha_n.$$
Here and below the canonical scalar tensor reassociations are understood. We use precisely these
supplied comparisons, not an independently chosen isomorphism between the endpoints. The finite
input $K_r$ is bounded constructible and has finite Tor amplitude by hypothesis; the same
properties of $\omega_r$ are included in the finite dualizing result and the assumed finite Tor
amplitude of $\omega_r$. Thus coefficient comparisons at $K_m$ and $\omega_m$ are isomorphisms.
Uses: lem-coef-integral-compact-support, lem-pod-point-sections-derived-reduction,
lem-fix-compact-support-coefficient-change, lem-coef-finite-dualizing.

2. Use the evaluation-normalized scalar-Hom isomorphism of [lem-sfb-dc-hom-scalar-adjunction]
for $R_X\to(A_r)_X$ and, on the one-object module site, for $R\to A_r$. It is natural in both
arguments and commutes with coefficient ring maps; there is no flatness assumption on $A\to B$.
In particular postcomposition by $\operatorname{Res}_m\tau_{m,n}$ on $H_m$ is the scalar-adjoint
version of
$$f_m\longmapsto f_n=u_{m,n}\circ T_X(f_m).$$
To spell out its meaning, take an arbitrary $P\in D(R)$ and $h:P\to H_m$. Put
$P_r=P\otimes_R^LA_r$, and let $(P_r)_X$ denote its constant complex on $X$. The global-sections
adjunction and tensor-Hom transposition identify $h$ with an evaluation map
$$f_m:(P_m)_X\otimes_A^LK_m\longrightarrow\omega_m.$$
The corresponding map for the left transition applied to $h$ is the displayed $f_n$, with
$T_X((P_m)_X\otimes_A^LK_m)\cong(P_n)_X\otimes_B^LK_n$. The formula follows also directly from
the scalar-adjunction unit $x\mapsto x\otimes1$: the adjunct of $\tau_{m,n}f_m$ sends $x\otimes
b$ to $b\tau_{m,n}f_m(x)$, which is $u_{m,n}T_X(f_m)$. Uses: lem-sfb-dc-hom-scalar-adjunction,
lem-pur-sheaf-ring-derived-coefficient-adjunction,
lem-weil-pbc-ringed-internal-hom-exact-restriction, lem-weil-pbc-ringed-projection-mate-exact,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

3. The finite dualizing node states, with its indices renamed $A=A_m$, $B=A_n$,
$$\varepsilon_n\circ F_n(u_{m,n})=(T_s\varepsilon_m)\circ c_{m,n,\omega_m}^{-1}.$$
Its last clause identifies this counit-defined map with its finite pro-etale realization, so
this is the identity for the functors in this item. This already proves the trace assertion,
including its specified normalization. Equivalently, without an inverse on the right,
$$\varepsilon_n F_n(u_{m,n})c_{m,n,\omega_m}=T_s\varepsilon_m.$$
We will use this last equality when composing the evaluation pairings. Restriction of compact
support along $A\to B$ is the canonical one for the same compactification, by
[lem-sf-compact-support-restriction-of-scalars]. Uses: lem-coef-finite-dualizing,
lem-sf-compact-support-restriction-of-scalars.

4. The coefficient square for the proper factor is a square of ringed topoi: its two vertical
arrows are $p$ at $A$ and $B$, and its horizontal arrows are the identity underlying topos with
structural ring map $A_W\to B_W$. Apply [lem-weil-pbc-ringed-exchange-tensor-coherence] to this
square. Its pullbacks along the horizontal arrows are exactly $T_W$. Its exchange is the
canonical proper coefficient map, with this normalization by
[lem-sp-direct-image-change-ring-transpose]. Hence the proper projection map commutes with
coefficient change for every input and every tensor parameter, without requiring any exchange to
be invertible. The same generic ringed-topos statement applies to the sections morphism from
$s_{\mathrm{proet}}$ to the one-object coefficient site. Sections are the derived direct image
for this morphism, and are computed termwise here by [lem-weil-point-proetale-sections-exact].
These applications are legitimate for arbitrary $P_m$, not only constructible parameters. Uses:
lem-weil-pbc-ringed-exchange-tensor-coherence, lem-sp-direct-image-change-ring-transpose,
lem-weil-point-proetale-sections-exact.

5. For the open factor use [lem-cbc-extension-zero-projection-formula]. With coefficient
parameter $B_{\overline X}$ it gives the canonical comparison $T_{\overline X}j_!M\cong
j_!T_XM$, before forgetting the $B$ action: on total-tensor representatives it is the balanced
map $(j_!x)\otimes b\mapsto j_!(x\otimes b)$. To justify these representatives, choose a K-flat
flat-term resolution $Q\to M$. The open tensor formula and exactness of $j_!$ and $j^*$ show
$j_!Q$ is K-flat, since tensoring it with an acyclic complex is $j_!$ of $Q$ tensored with an
acyclic restriction. For two tensor factors, scalar change of the open projection map and the
open projection after scalar change restrict to the identical balanced tensor map on $X$; the
$j_!\dashv j^*$ bijection makes them equal on $\overline X$. Tensor reassociation respects the
$B$ action by $b(x\otimes y)=(bx)\otimes y$. Therefore, substituting this open identity and the
proper identity of step 4 into the defining composite $\operatorname{PF}^c=Rp_*(\gamma_j)\pi_p$
proves coefficient compatibility of the compact-support projection map. This is just pasting
those two identities in the fixed compactification; no compactification-independence theorem or
inverse projection map is needed. Uses: lem-cbc-extension-zero-projection-formula,
lem-cbc-proetale-extension-zero, lem-pc-kflat-resolution,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-exchange-projection.

6. For $h:P\to H_m$ as in step 2, define $b_m(f_m):P_m\otimes_A^LC_m\to A$ as follows. Apply the
point-section projection map, then the compact-support projection for $(K_m,(P_m)_s)$, then
$\Gamma(s,F_m(f_m))$, and finally $\Gamma(s,\varepsilon_m)$. Tensor symmetry puts $P_m$ first
throughout. Thus its last two arrows are
$$\Gamma(s,F_m((P_m)_X\otimes_A^LK_m))\xrightarrow{\Gamma
F_m(f_m)}\Gamma(s,F_m\omega_m)\xrightarrow{\Gamma\varepsilon_m} A.$$
Apply the current [lem-coef-finite-mapping-adjunction] to $M=K_m$: the item hypotheses make
$K_m$ bounded constructible with finite Tor amplitude, so its canonical natural isomorphism and
stated evaluation/counit normalization identify the $R$-linear pairing adjoint to
$\widetilde\gamma_mh:P\to J_m$ exactly as
$$P\otimes_R^LC\longrightarrow
P_m\otimes_A^L(C\otimes_R^LA)\xrightarrow{1\otimes\alpha_m}
P_m\otimes_A^LC_m\xrightarrow{b_m(f_m)}A.$$
Define $b_n(f_n)$ by the same composite at $B$. All projection arrows here are ambient
morphisms, so the construction makes sense without a constructibility or Tor hypothesis on $P$.
Uses: lem-coef-finite-mapping-adjunction, lem-sfb-dc-hom-scalar-adjunction,
def-exchange-projection, lem-weil-pbc-ringed-projection-mate-exact,
def-weil-finite-coefficient-point.

7. Apply coefficient change to the composite defining $b_m(f_m)$. Steps 4 and 5 move it through
the point-section and compact-support projection arrows. Naturality of the coefficient map moves
it through $F_m(f_m)$; at the resulting last arrow use the trace equality of step 3. The
resulting explicit equality is
$$b_n(u_{m,n}T_Xf_m)\circ(1_{P_n}\otimes d)=T_{\mathrm{pt}}(b_m(f_m)),$$
as maps
$$P_n\otimes_B^L(C_m\otimes_A^LB)\longrightarrow B.$$
Indeed the left route, before trace, is $\Gamma F_n(T_Xf_m)$ followed by $\Gamma F_n(u_{m,n})$,
whereas the coefficient-changed right route is $\Gamma(T_s\varepsilon_m)$ after the coefficient
comparison at $\omega_m$. The equation $\varepsilon_nF_n(u)c_{\omega_m}=T_s\varepsilon_m$
identifies exactly these last composites. Naturality applies also to the potentially unbounded
source of $f_m$: the coefficient maps there are the ambient mates from steps 4 and 5, not
isomorphisms asserted by the finite-Tor theorem. Only $c_{K_m}$, giving $d$, and $c_{\omega_m}$
are inverted. Uses: lem-coef-finite-dualizing, lem-weil-pbc-ringed-exchange-tensor-coherence,
def-exchange-projection, lem-fix-compact-support-coefficient-change.

8. Let $q:A\twoheadrightarrow B$. Under scalar adjunction, postcomposing $b_m(f_m)$ with $q$
corresponds to $T_{\mathrm{pt}}(b_m(f_m))$: the counit identifies $A\otimes_A^LB$ with $B$.
Therefore the equality of step 7, precomposed with $1\otimes(\alpha_m\otimes_A^LB)$, and
$d(\alpha_m\otimes_A^LB)=\alpha_n$ from step 1, give equality of pairings on $P\otimes_R^LC$:
$$q\circ b_m(f_m)\circ(1\otimes\alpha_m)=b_n(f_n)\circ(1\otimes\alpha_n).$$
Here both sides include the scalar-extension units from $P\otimes_R^LC$ displayed in step 6.
Their equality uses the unit for the composite $R\to A\to B$; on a K-flat representative it is
$x\mapsto(x\otimes1)\otimes1=x\otimes1$. Thus the transition on the right is exactly
postcomposition by the quotient $q$, not an arbitrarily chosen reduction identification. Uses:
lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-coef-integral-compact-support,
lem-pod-point-sections-derived-reduction.

9. Transpose step 8 under tensor-Hom adjunction in $D(R)$. By steps 2 and 6 its two maps $P\to
J_n$ are respectively
$$J(q)\,\widetilde\gamma_mh\quad\text{and}\quad\widetilde\gamma_n
H(\operatorname{Res}_m\tau_{m,n})h.$$
Since $P$ and $h:P\to H_m$ were arbitrary, take $P=H_m$ and $h=1_{H_m}$. This proves the desired
commuting square as equality of morphisms in $D(R)$. Tensor-Hom transposition is a bijection, so
this tests the full derived morphisms and does not infer equality from their actions on
individual cohomology groups. Uses: lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-pur-rhom-global-sections.

10. For a morphism $z:K\to K'$ between objects satisfying the hypotheses, the maps on $H_r$ are
precomposition by $z$ (or $z_r$ after scalar adjunction), and the maps on $J_r$ are
precomposition by $C(z):C\to C'$. The current [lem-coef-finite-mapping-adjunction] states that
$\gamma_{r,M}$ is a canonical natural isomorphism for every finite constructible finite-Tor $M$,
so it applies to both $K_r$ and $K'_r$ and is natural in $z_r$. The scalar-Hom comparison and
$\alpha_r$ are natural as well. Explicitly, the evaluation relation is $f'_r(1\otimes z_r)$;
inserting it in step 6 replaces compact support by $F_r(z_r)$, hence replaces the pairing by
precomposition with $1\otimes C_r(z_r)$. It follows after transposition that
$J_r(C(z))\widetilde\gamma_{r,K'}=\widetilde\gamma_{r,K}H_r(z)$. Precomposition by $z$ commutes
with postcomposition by $\tau_{m,n}$, and precomposition by $C(z)$ commutes with postcomposition
by $q$. Thus the proved squares are contravariantly natural in $K$. When $m=n$ the coefficient
units and $u_{m,m}=1$ give the identity square; when $K=0$ or $X$ is empty all pairings have
zero source. These cases require no additional hypothesis. Uses:
lem-coef-finite-mapping-adjunction, lem-sfb-dc-hom-scalar-adjunction,
lem-coef-integral-compact-support, lem-pod-point-sections-derived-reduction,
lem-coef-finite-dualizing. -/
theorem finiteAdjunctionTransition (hl : l ≠ D.p)
    (_homega : ∀ n : ℕ, HasFiniteProEtaleTorAmplitude X
      (Padic.coefficientExtensionRing l E (n + 1))
      (integralDualizingFiniteTerm l E D X n))
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (_hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition.{u, u} l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes.{u, u} l E X h).map (eQ n).hom =
        (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h)
    (_hab : a₀ ≤ b₀)
    (_htransition : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      (pbcTowerTransition (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) m n h).app
          (T.obj K) ≫ (e n).hom.app K =
        (e m).hom.app K ≫ compactSupportRestrictedTransition l E
          (finiteDualizingCompactification D X) m n h K)
    (_hM : M.IsSpecified l E D X Q a₀ b₀ T e)
    (_hTensor : ∀ n : ℕ, M.tensorEvaluation n = canonicalTensorEvaluation l E n)
    (_hscalar : ∀ (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      (M.integralHom r).inv.app (op K) ≫ (M.finiteHom r).hom.app (op K) =
        scalarHom D l E X Q a₀ b₀ T e M r K)
    (eTrace : ∀ n : ℕ,
      (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
        coefTraceFiniteValue l E D X n)
    (_hTrace : ∀ (m n : ℕ) (h : n ≤ m),
      (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫
          (eTrace n).hom ≫ coefTraceFiniteCounit l E D X n ≫
            (coefTraceTargetIso l E D n).hom =
        (eTrace m).hom ≫ coefTraceFiniteCounit l E D X m ≫
          (coefTraceTargetIso l E D m).hom ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
              (coefTraceQuotientMap l E h))
    (_hOrigin : ∀ n : ℕ,
      (M.omegaEvaluation n).hom ≫ (M.omegaOrigin n).hom = (eTrace n).hom)
    (_hHom : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      (coefTraceTransition l E h).app ((coefPairingHom l E X M.calculus Q).obj (op K)) ≫
          (M.integralHom n).hom.app (op K) =
        (M.integralHom m).hom.app (op K) ≫ HTransition D l E X hl h K) :
    (∀ (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory)
      (m n : ℕ) (h : n ≤ m)
      (γ_m : (H D l E X m).obj (op K.obj) ≅ (J D l E X T m).obj (op K.obj))
      (γ_n : (H D l E X n).obj (op K.obj) ≅ (J D l E X T n).obj (op K.obj)),
      γ_m.hom = finiteHorizontal D l E X Q a₀ b₀ T e M m K →
      γ_n.hom = finiteHorizontal D l E X Q a₀ b₀ T e M n K →
      HTransition D l E X hl h K.obj ≫ γ_n.hom =
        γ_m.hom ≫ JTransition D l E X T h K.obj) ∧
    (∀ (K K' : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory)
      (z : K ⟶ K') (r : ℕ)
      (γ : (H D l E X r).obj (op K.obj) ≅ (J D l E X T r).obj (op K.obj))
      (γ' : (H D l E X r).obj (op K'.obj) ≅ (J D l E X T r).obj (op K'.obj)),
      γ.hom = finiteHorizontal D l E X Q a₀ b₀ T e M r K →
      γ'.hom = finiteHorizontal D l E X Q a₀ b₀ T e M r K' →
      (H D l E X r).map z.hom.op ≫ γ.hom =
        γ'.hom ≫ (coefCurryingPointHom l E r).map ((C D l E X T).map z.hom).op) ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      (finiteDualizingEtaleSupport l E D X n).map
          (finiteDualizingEtaleComparison l E D X h) ≫
        finiteDualizingEtaleCounit l E D X n =
      Etale.ExceptionalCoefficients.comparisonInverse (finiteDualizingQuotient l E h)
          (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X m) ≫
        (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
          (finiteDualizingEtaleCounit l E D X m) ≫
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
          (Spec (.of D.k))).hom) := by
  sorry

end FiniteAdjunctionTransition
end WeilConjectures
