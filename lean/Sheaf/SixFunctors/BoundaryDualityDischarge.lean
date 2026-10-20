/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.SixFunctors.BoundaryDualityInput
import Sheaf.Paper.FiniteStageVerdierBiduality
import Sheaf.Paper.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.SixFunctors.ClosedCostalkDuality
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.Paper.DualityPairing
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.ProjectionCompactification
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.BoundaryDualizingComposition
import Sheaf.Paper.BoundaryProEtaleProjectionComparison
import Sheaf.Paper.BoundaryProEtaleQCompatibility
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.SixFunctors.BoundaryAlphaNormalization
import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-!
# Discharge of the finite-stage boundary duality input

Source: `literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-biduality-general/cor-weil-boundary-duality-discharge.md`,
node `cor-weil-boundary-duality-discharge` (blueprint: cor-weil-boundary-duality-discharge).

The proof follows the finite-stage small-site duality and its comparison transport: finite-type
locally closed pieces are separated and finite type, duality preserves the finite-Tor constructible
subcategory, and the normalized tensor-Hom transposes identify the canonical boundary exchange
with the double-dual comparison. The pro-etale comparison transports these maps and identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/--
The finite-stage boundary duality input holds for every separated finite-type scheme over the
fixed algebraic closure of a finite field and every positive finite coefficient level. Its second
clause is the canonical evaluation-defined boundary exchange, including its evaluation and
double-dual compatibility.

Source: `literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-biduality-general/cor-weil-boundary-duality-discharge.md`,
node `cor-weil-boundary-duality-discharge` (blueprint: cor-weil-boundary-duality-discharge).

Proof plan (the node's fourteen steps):

1. Work first on the small etale sites with $A=A_{E,n}$ and $\ell\ne\operatorname{char}k$. By
[lem-weil-pbc-finite-type-over-noetherian], $Y$ is Noetherian. Write a locally closed piece $W$ as
a closed subscheme of an open $V\subseteq Y$. The Noetherian-open lemma makes $V$ Noetherian and
its inclusion quasi-compact, hence finite type by the quasi-compact-open lemma; the closed
inclusion is proper and finite type by the closed-immersion lemma. Composing finite generating
sets on affine charts proves $W/k$ finite type. Its diagonal is the restriction of the closed
diagonal of $Y/k$, hence is closed; thus $W/k$ is separated. The finite-type-over-Noetherian lemma
applies again to $W$.

2. On every piece, [thm-fix-general-biduality] gives preservation of $D^b_{ctf}$ by $D_W$ and
invertibility of $\delta$. Apply [lem-weil-boundary-dualizing-composition] to the structure maps
and to $i:Z\hookrightarrow T$: the etale adjoints restrict to $D^+$, and the counit-compatible
composition gives $Ri^!\omega_T\cong\omega_Z$. This also supplies their comparison-class pro-etale
transport. No unbounded pro-etale adjunction is required.

3. Fix $L\in D^b_{ctf}(T,A)$ and put $P=i^*D_TL$ and $U=Ri^!L$. The etale $i^*$ is the exact
constant-coefficient inverse image by [prop-weil-pbc-inverse-image-modules-exact];
[prop-constructible-pullback] therefore makes $P$ bounded constructible. For its Tor bound, use
[lem-sf-comparison-tor-amplitude] to send $D_TL$ to the finite-Tor pro-etale category, apply
[lem-sf-pullback-tor-amplitude] there, and identify its result with $\nu_Z^*P$ by
[lem-weil-pbc-comparison-pullback]. The converse clause of [lem-sf-comparison-tor-amplitude]
reflects that bound to the bounded etale complex $P$. Thus $P\in D^b_{ctf}(Z,A)$ with no silent
identification of the two sites. Apply [lem-weil-closed-costalk-duality] to $D_TL$. It gives an
isomorphism $\widetilde\alpha_{D_TL}:Ri^!D_TD_TL\to D_ZP$. Thus $$\widetilde
c_L=\widetilde\alpha_{D_TL}\circ Ri^!\delta_L:U\xrightarrow{\sim}D_ZP.$$ Consequently $U$ is
finite-Tor constructible, because $D_ZP$ is so by [thm-fix-general-biduality]. The same argument
applied to any $K\in D^b_{ctf}(T,A)$ shows $Ri^!K\in D^b_{ctf}(Z,A)$, in particular for $K=D_TL$.
This conclusion used costalk duality and biduality, without using the boundary exchange. Here the
tildes distinguish a preservation witness from the evaluation-normalized comparison to be
constructed in step 6; no normalization of the costalk lemma is inferred from its statement.

4. Record the tensor--internal-Hom adjunction used in the remaining map calculations on the actual
ringed sites. Given $B,C,H\in D(A_W)$, choose a K-flat flat-term representative $Q$ of $C$ by
[lem-pc-kflat-resolution] and a K-injective representative $I$ of $H$ by
[prop-pur-kinjective-resolutions-exist]. The definition [def-pur-derived-internal-hom] and
[lem-pur-hom-kflat-into-kinjective] show that $\mathcal Hom^\bullet(Q,I)$ is a K-injective
representative of $R\mathcal Hom(C,H)$. The natural complex isomorphism
[lem-sc-derived-hom-tensor-total] identifies the representatives of $R\mathcal Hom(B,R\mathcal
Hom(C,H))$ and $R\mathcal Hom(B\otimes^LC,H)$. Taking $H^0$ of derived global sections and
applying [lem-pur-rhom-global-sections] gives $$\operatorname{Hom}(B,R\mathcal
Hom(C,H))\cong\operatorname{Hom}(B\otimes^LC,H).$$ The counit is evaluation; transposition is
natural in all three variables. This proves the needed adjunction from statements about small
ringed sites, rather than citing an adjunction for $\mathcal O_X$-modules as though it were an
adjunction for etale $A$-modules. Tensor symmetry is the signed interchange of homogeneous
factors, $x\otimes y\mapsto(-1)^{\deg x\deg y}y\otimes x$; the two interchanges compose to the
identity and respect the total differential.

5. Write $\mu_N:Ri_!Ri^!N\to N$ for the exceptional counit. For $M,N\in D^b_{ctf}(T,A)$ define
$q_{M,N}:i^*M\otimes_A^LRi^!N\to Ri^!(M\otimes_A^LN)$ as the transpose of
$$Ri_!(i^*M\otimes_A^LRi^!N)\xrightarrow{\mathrm{PF}^{-1}}M\otimes_A^LRi_!Ri^!N
\xrightarrow{1\otimes\mu_N}M\otimes_A^LN.$$
The projection formula applies since $M$ is finite-Tor and $Ri^!N$ is bounded constructible by
step 3; tensor symmetry gives this order. The exceptional adjunction is the etale ambient one.
Transposing the natural projection/counit composite makes $q$ natural in both variables.

6. Apply [lem-weil-boundary-alpha-normalization] using the tensor-Hom adjunction of step 4 and the
preservation established in steps 2--3. Its explicit Hom chain proves that the transpose of
$$r_K=Ri^!(\mathrm{ev}_K\circ\sigma_{K,D_TK})\circ q_{K,D_TK}\circ\sigma_{Ri^!D_TK,i^*K}$$ is the
isomorphism $\alpha_K:Ri^!D_TK\xrightarrow{\sim}D_Zi^*K$. This fixes the evaluation normalization,
rather than inferring it from the existence-only costalk statement. Put $c_L=\alpha_{D_TL}\circ
Ri^!\delta_L:U\xrightarrow{\sim}D_ZP$. Both factors are isomorphisms. The preliminary $\widetilde
c_L$ of step 3 served only to establish the finite-Tor domain.

7. By [lem-weil-duality-pairing], $\delta_L$ is the transpose of evaluation after tensor symmetry.
The defining transpose equation is therefore
$$\mathrm{ev}_{D_TL}\circ(\delta_L\otimes1_{D_TL})=\mathrm{ev}_L\circ\sigma_{L,D_TL}.$$ This is an
equality of maps $L\otimes^LD_TL\to\omega_T$, with the same signed symmetry as in step 4. No
invertibility is needed for this identity.

8. Let $$b_L=Ri^!\mathrm{ev}_L\circ q_{D_TL,L}:P\otimes^LU\longrightarrow\omega_Z.$$ This is the
pairing whose transpose defines $\beta_L$ in [def-weil-boundary-duality-input]. Let
$t(c_L)=\mathrm{ev}_P\circ(c_L\otimes1_P)$ be the transpose of $c_L$. The formula for $r$ in step
6, naturality of $q$ in its second variable, naturality of tensor symmetry, and step 7 give the
following equality of maps $U\otimes^LP\to\omega_Z$: $$\begin{aligned}
t(c_L)&=r_{D_TL}\circ(Ri^!\delta_L\otimes1_P)\\
&=Ri^!\bigl(\mathrm{ev}_{D_TL}\circ\sigma_{D_TL,D_TD_TL}\circ(1_{D_TL}\otimes\delta_L)\bigr)\circ
q_{D_TL,L}\circ\sigma_{U,P}\\
&=Ri^!\bigl(\mathrm{ev}_{D_TL}\circ(\delta_L\otimes1_{D_TL})\circ\sigma_{D_TL,L}\bigr)\circ
q_{D_TL,L}\circ\sigma_{U,P}\\
&=Ri^!\bigl(\mathrm{ev}_L\circ\sigma_{L,D_TL}\circ\sigma_{D_TL,L}\bigr)\circ
q_{D_TL,L}\circ\sigma_{U,P}\\ &=b_L\circ\sigma_{U,P}. \end{aligned}$$ The last line uses
$\sigma_{L,D_TL}\sigma_{D_TL,L}=1$. Thus $c_L$ and $\beta_L$ are the two currying maps of this
same pairing, in opposite tensor orders.

9. Naturality of evaluation for $c_L:U\to D_ZP$ gives
$$\mathrm{ev}_U\circ(D_Zc_L\otimes1_U)=\mathrm{ev}_{D_ZP}\circ(1_{D_ZD_ZP}\otimes c_L).$$
Precomposing with $\delta_P\otimes1_U$ and using the transpose identity from step 7 on $Z$ shows
that the transpose of $D_Z(c_L)\circ\delta_P$ is $b_L$. Uniqueness under the adjunction of step 4
therefore gives the specified-map identity $$\beta_L=D_Z(c_L)\circ\delta_P.$$ Both factors are
isomorphisms: $c_L$ is an isomorphism by step 6, a functor sends its inverse to an inverse, and
$\delta_P$ is an isomorphism by [thm-fix-general-biduality], since $P\in D^b_{ctf}(Z,A)$. Hence
the canonical evaluation-defined boundary map is an isomorphism.

10. For the evaluation compatibility, fix $K\in D^b_{ctf}(T,A)$. The transpose of
$\beta_{D_TK}\circ i^*\delta_K$ is $$Ri^!\mathrm{ev}_{D_TK}\circ
q_{D_TD_TK,D_TK}\circ(i^*\delta_K\otimes1_{Ri^!D_TK}).$$ Naturality of $q$ and step 7 rewrite this
as $$Ri^!(\mathrm{ev}_K\circ\sigma_{K,D_TK})\circ
q_{K,D_TK}:i^*K\otimes^LRi^!D_TK\longrightarrow\omega_Z.$$ On the other hand the transpose of
$D_Z(\alpha_K)\circ\delta_{i^*K}$ is $r_K\circ\sigma_{i^*K,Ri^!D_TK}$, by naturality of evaluation
and the defining transpose of $\delta_{i^*K}$. This is the very same displayed map, by the formula
for $r_K$ in step 6. Uniqueness of transposition yields $$\beta_{D_TK}\circ
i^*\delta_K=D_Z(\alpha_K)\circ\delta_{i^*K}.$$ Composing with $(D_Z\alpha_K)^{-1}$ gives exactly
the double-dual compatibility required in [def-weil-boundary-duality-input]. The two cancellations
of symmetry use its involutivity, so they include the Koszul signs.

11. For the pro-etale realization put $C_W=\nu_W^*$. Every bounded constructible input has an
etale-origin representative by [lem-sf-proetale-constructible-origin], and
[lem-sf-comparison-tor-amplitude] preserves and reflects its finite Tor interval. The ordinary
restriction is identified by [lem-weil-pbc-comparison-pullback]. The specified exceptional
restriction is $C_Zi^\times R\nu_{T,*}$; the site-comparison unit identifies its value on $C_TN$
with $C_Zi^\times N$. These are bounded-below inputs, so the comparison-class adjunction applies.
For $i$, choose its identity-open compactification. Its finite-type source has a finite dimension
bound by [lem-fin-finite-type-fibre-dimension-bound] over $\operatorname{Spec}k$, checking the
class-adjunction dimension hypothesis.

12. Use the identity-open compactification of $i$, so $F_e=Ri_{e,*}$ and $F_p=Ri_{p,*}$. Let
$\eta_B:F_pC_ZB\xrightarrow{\sim}C_TF_eB$ be the inverse of the named canonical direct-image mate.
The hypotheses of [lem-weil-boundary-proetale-projection-comparison] use exactly this mate and the
monoidal tensor-pullback comparison. It gives $$\mu^p_{C_TN}=C_T(\mu^e_N)\eta_{i^\times N},\qquad
\eta_{B\otimes i_e^*M}\pi_p=C_T(\pi_e)(\eta_B\otimes1).$$ Thus both exceptional counits and the
named projection transformations, including their inverses on the finite-Tor inputs of step 3,
agree under comparison.

13. Check the hypotheses of [lem-weil-finite-duality-site-comparison]. The constant sheaf $A_W$ is
locally constant finite, hence constructible, and $A_W\otimes_A^LN=N$ shows Tor interval $[0,0]$.
On a K-injective representative $I$ of $H$, the internal Hom complex from $A_W$ is $I$ itself, so
$R\mathcal Hom_A(A_W,H)\cong H$. Therefore $\omega_{W,e}=D_WA_W$ is bounded finite-Tor
constructible by biduality. Every first variable needed below is finite-Tor: the inputs and their
duals by step 2, ordinary and exceptional restrictions by step 3, and further duals by step 2. The
comparison lemma consequently applies with second variable $\omega_{W,e}$. Denote its dualizing
comparison by $w_W$ and its internal-Hom comparison by $\chi_{W,H}:C_WD_WH\cong D_W^pC_WH$. It
identifies evaluation and its double-dual transpose.

14. The counit and projection identities of step 12 satisfy the hypotheses of
[lem-weil-boundary-proetale-q-compatibility]. It identifies $q^p_{C_TM,C_TN}$ with $C_Zq^e_{M,N}$
and the transposes of all the evaluation/symmetry pairings used here. In conjunction with $w,\chi$
from step 13, the explicit formula for $r$ in step 6 identifies $\alpha^p$ with the comparison of
$\alpha^e$. The formula for $b$ in step 8 identifies the canonical $\beta^p$ with the comparison
of $\beta^e$. Applying the comparison to the two sides of the equalities of steps 9--10, and using
its identified double-dual transposes, proves invertibility of $\beta^p$ and
$$\beta^p_{D_T^pC_TK}\circ i_p^*\delta^p_{C_TK}=D_Z^p(\alpha^p_{C_TK})\circ\delta^p_{i_p^*C_TK}.$$
Together with preservation from step 2, these are precisely the two clauses of
[def-weil-boundary-duality-input].
-/
theorem boundary_duality_input
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ)
    (Y : Scheme.{u})
    (aY : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    BoundaryDualityInput D l hl E n Y aY := by
  sorry

end AlgebraicGeometry.ProEtale
