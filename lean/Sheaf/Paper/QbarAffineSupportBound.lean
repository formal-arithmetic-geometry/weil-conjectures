/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.QbarDerivedDirectImage
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.PbcSupportCondition
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Paper.IntegralConstructibleReductionFibres
import Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntegralTStructure
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.QbarOrdinaryAdjunction
import Sheaf.Paper.SfIntegralDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Affine higher-direct-image support bound at adic field coefficients

Source: BBD, Theorem 4.1.1, with the finite-coefficient calculation in Stacks
Project, Tag 0F0X, and the adic interpretation in Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-per-qbar-affine-support-bound).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.PerAdic

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime]
  [Fact (IsUnit (l : k))]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Affine finite-type pushforward lowers the closed support dimension by the
cohomological degree, and has no negative cohomology.  The support is the closure of
the nonzero geometric-fibre locus used by `pbcQbarCohomologySupport`; the empty support
therefore satisfies every bound.  Source: BBD Theorem 4.1.1 and Stacks Tag 0F0X
(blueprint: lem-per-qbar-affine-support-bound).
Proof (the eleven steps of the DAG node):

1. The schemes $X,Y$ are noetherian by [lem-weil-pbc-finite-type-over-noetherian], since a field
is noetherian, and finite-dimensional by [lem-kun-dimension-finite-type]. By
[lem-per-adic-heart-pullback-fibres], choose a finite coefficient field $E$ and
$F_E\in\operatorname{Sh}_c(X,E)$ representing $F$. The same node computes fibres at the common
stage by extension from $E$ to $\overline{\mathbf Q}_\ell$. A vector space is zero if and only if
its extension to a field is zero (a basis remains linearly independent). Thus $F_E$ has the same
nonzero-fibre locus and the same closed support $Z$ as $F$. Put $A=\mathcal O_E$, choose its
uniformizer $\varpi$, and write $B_T=\varprojlim_n(A/\varpi^n)_T$ and $E_T=B_T[1/\varpi]$. The
heart assertion of [prop-weil-localized-tstructure] supplies an integral heart object $H$ with
$Q_XH\cong F_E$.

2. Give $Z$ its reduced induced closed scheme structure $i:Z\hookrightarrow X$ by
[lem-weil-pbc-reduced-induced-closed-subscheme], and let $j:U\hookrightarrow X$ be the
complementary open. It is quasi-compact since $X$ is noetherian. By
[lem-weil-pbc-continuous-coefficients-immersion-restriction], the restricted coefficient rings are
$B_Z,E_Z$ and $B_U,E_U$. Form the actual module sheaf $K=i_*i^{-1}H$. The ringed open-closed lemma
makes $i_*$ exact and gives $j^{-1}K=0$ and $i^{-1}i_*\cong\operatorname{id}$. Restrict a finite
stratification for $H$ to $Z$, and add the zero stratum $U$: on each resulting piece $K$ is
locally a completed coefficient module associated to a finitely presented $A$-module, or zero.
Therefore [lem-weil-pbc-integral-stratified-perfect-characterization] puts $K[0]$ in the integral
constructible category, including compatible etale-origin witnesses. This construction permits
torsion in $H$ and in $K$.

3. Write $J_T$ for [lem-per-continuous-rational-derived-realization]. Its t-exact realization and
restriction comparison identify $J_X(F_E)$ with $E_X\otimes_{B_X}H$ and its restriction to $U$
with $J_U(j^*F_E)$. The latter is zero: all its adic fibres vanish by the definition of $Z$, and
[lem-per-adic-heart-pullback-fibres] makes those fibres conservative. The open-closed short exact
sequence consequently gives $J_X(F_E)\cong i_*i^{-1}J_X(F_E)$. Localization is the sheaf colimit
of repeated multiplication by $\varpi$. It commutes with $i^{-1}$, and with $i_*$ by the
filtered-colimit clause of [lem-weil-pbc-proetale-ringed-open-closed], since $X$ is qcqs. The
coefficient restriction isomorphisms from Step 2 therefore identify $J_X(Q_XK)=E_X\otimes_{B_X}K$
with $i_*i^{-1}J_X(F_E)$. Full faithfulness of $J_X$ gives $Q_XK\cong F_E$. We have obtained an
integral heart representative supported on $Z$, without assuming that an arbitrary original
representative $H$ has that support.

4. Let $K_1=K\otimes^L_{B_X}(A/\varpi)_X$. The two-term resolution of
[det-pe-derived-nakayama-resolution] identifies it, after restriction of scalars, with
$\operatorname{Cone}(\varpi:K\to K)$. Thus its only possible cohomology sheaves are $K[\varpi]$ in
degree $-1$ and $K/\varpi K$ in degree zero, by the kernel/cokernel clause of
[lem-weil-heart-short-exact-triangles]. Choose an etale-origin witness $L_1\in
D^+(X_{\mathrm{et}},A/\varpi)$ for $K_1$, as supplied by membership in
[def-weil-pbc-bounded-constructible-complete]. The comparison inverse image is exact by
[sk-thm-pe-direct-image-comparison] and fully faithful by [thm-weil-pbc-site-comparison]. It
follows that $L_1$ has only $T=\mathcal H^{-1}L_1$ and $G=\mathcal H^0L_1$, and both are supported
on $Z$: restriction of $K_1$ to $U$ is zero, and comparison on $U$ is faithful. They are sheaves
of modules over the finite ring $A/\varpi$, hence are torsion abelian sheaves after forgetting
scalars.

5. For any $x\in Z$, its irreducible closed closure $C=\overline{\{x\}}$ lies in $Z$. The
dimension formula [lem-sc-closed-irreducible-dimension-trdeg] gives
$\operatorname{trdeg}_k\kappa(x)=\dim C\le\dim Z\le a$. The middle inequality follows directly by
viewing each irreducible closed chain in $C$ as one in $Z$. Thus the supports of the underlying
abelian sheaves of $T,G$ lie in $E_a(X)$, in the notation of
[lem-kun-affine-direct-image-support-bound]. Apply that node to both sheaves:
$\operatorname{supp}R^rf_*T\subset E_{a-r}(Y)$ and $\operatorname{supp}R^rf_*G\subset E_{a-r}(Y)$
for $r\ge0$. Its hypotheses hold because $f$ is affine over $k$, $X,Y$ are finite type over $k$,
and both input sheaves are torsion. The module/abelian comparison
[lem-sbc-higher-direct-image-forget-comparison] identifies these bounds with the bounds for
module-valued higher direct images.

6. The ordinary truncation triangle is $T[1]\to L_1\to G\to T[2]$. Apply the triangulated derived
direct image of [lem-weil-pbc-derived-direct-image-triangulated] and take the long exact
cohomology sequence, as in [lem-weil-heart-short-exact-triangles]. For $q\ge0$ it contains
$R^{q+1}f_*T\to\mathcal H^q(Rf_*L_1)\to R^qf_*G$. Step 5 bounds the outer supports by
$E_{a-q-1}(Y)$ and $E_{a-q}(Y)$, respectively. Since the first set is contained in the second,
exactness of etale geometric stalks [prop-weil-pbc-geometric-stalks-exact] gives
$\operatorname{supp}\mathcal H^q(Rf_*L_1)\subset E_{a-q}(Y)$. This explicitly includes the degree
$-1$ Tor term of the derived reduction. It does not replace $K_1$ by the ordinary quotient
$K/\varpi K$.

7. Put $M=Rf_*K$ integrally. The theorem [lem-sf-integral-direct-image-constructible], applied
over the field $k$ with $\ell$ invertible, makes $M$ bounded constructible and gives
$M\otimes^L(A/\varpi)\cong Rf_{*,1}K_1$. Under [sk-thm-pe-direct-image-comparison], the right side
is $\nu_Y^*Rf_{\mathrm{et},*}L_1$. Here $f$ is qcqs by [lem-weil-pbc-affine-morphism-permanence].
Each $N_q=\mathcal H^q(M)$ is an integral heart object by [prop-weil-pbc-integral-tstructure]. The
uniformizer cone from [det-pe-derived-nakayama-resolution] and the long exact sequence from
[lem-weil-heart-short-exact-triangles] give a monomorphism $N_q/\varpi N_q\hookrightarrow\mathcal
H^q(M\otimes^L(A/\varpi))$. By [lem-a1-integral-constructible-reduction-fibres] its source is
$\nu_Y^*C_q$ for a constructible etale sheaf $C_q$. The target is $\nu_Y^*\mathcal
H^q(Rf_{\mathrm{et},*}L_1)$. Exact full faithfulness of comparison [thm-weil-pbc-site-comparison]
reflects this monomorphism and supplies the etale monomorphism $C_q\hookrightarrow\mathcal
H^q(Rf_{\mathrm{et},*}L_1)$.

8. Fix $q\ge0$ and a geometric point $\bar y$ over $y\notin E_{a-q}(Y)$. Steps 6--7 and exactness
of geometric stalks [prop-weil-pbc-geometric-stalks-exact] give $(C_q)_{\bar y}=0$. By
[lem-a1-integral-constructible-reduction-fibres], the adic integral fibre module $P_{\bar y}$ of
$N_q$ is finite over $A$ and $P_{\bar y}/\varpi P_{\bar y}\cong(C_q)_{\bar y}=0$. Apply
[lem-weil-pbc-nakayama-local-generators] with the local ring $A$, maximal ideal $(\varpi)$, and
submodule zero, to get $P_{\bar y}=0$. Its rational fibre $P_{\bar y}\otimes_AE$ is therefore
zero. The cohomology comparison in [prop-weil-localized-tstructure] gives $Q_YN_q\cong\mathcal
H^q(Q_YM)$. By [prop-weil-pbc-rational-transport] and Step 3, $Q_YM\cong Rf_*^{\mathrm{rat}}F_E$.
Thus the nonzero-fibre locus of $\mathcal H^q(Rf_*^{\mathrm{rat}}F_E)$ is contained in
$E_{a-q}(Y)$.

9. Finite coefficient extension commutes with direct image by [prop-weil-pbc-scalar-extension],
and with standard cohomology and geometric fibres by [lem-per-adic-heart-pullback-fibres]. Passing
to the common finite-stage category therefore identifies the output in Step 8 with $\mathcal
H^q(Rf_*F)$ after extending fibres to $\overline{\mathbf Q}_\ell$. Faithful extension of vector
spaces preserves their zero locus. This output is constructible: integral direct-image
constructibility in Step 7 and rational transport put it in the constructible category, and its
cohomology is in the constructible heart. Its nonzero-fibre locus $S$ is consequently
constructible by [lem-per-adic-heart-pullback-fibres]. We have proved $S\subset E_{a-q}(Y)$.

10. Set $b=a-q$. If $b<0$, then $E_b(Y)=\varnothing$, so Step 9 gives $S=\varnothing$ and the
claimed empty-support bound. Suppose $b\ge0$. For each irreducible component $C$ of $\overline S$,
its generic point $\eta_C$ belongs to $S$. Indeed, write the constructible set $S$ as a finite
union of locally closed subsets and then their irreducible pieces; the closure of at least one
piece is $C$, and that piece contains an open dense subset of $C$, hence its generic point. Now
[lem-sc-closed-irreducible-dimension-trdeg] gives $\dim C=\operatorname{trdeg}_k\kappa(\eta_C)\le
b$. Every irreducible closed chain in the finite union $\overline S=\bigcup C$ lies in a
component, so $\dim\overline S\le b$. Since $\operatorname{Supp}\mathcal H^q(Rf_*F)=\overline S$
by the given closed-support convention, this proves the stated inequality. Constructibility is
essential here; no dimension bound for the closure of an arbitrary subset of $E_b(Y)$ is used.

11. For the negative-degree assertion put $R=Rf_*F$. The ordinary adjunction
[lem-per-qbar-ordinary-adjunction] applies to $f$, since it is affine, hence separated, and finite
type. Let $A_-=\tau^{\le-1}R$ in the bounded standard t-structure. By
[lem-weil-heart-short-exact-triangles], it is built by finitely many truncation triangles from the
objects $\mathcal H^j(A_-)[-j]$ with $j\le-1$. The pullback of
[lem-per-adic-heart-pullback-fibres] is triangulated and carries each heart object into the heart.
Extension closure therefore gives $Lf^*A_-\in D^{\le-1}(X)$. Orthogonality of the standard
t-structure gives $\operatorname{Hom}(Lf^*A_-,F)=0$, so adjunction gives
$\operatorname{Hom}(A_-,R)=0$. In particular the canonical truncation map $A_-\to R$ is zero. In
each degree $j<0$ it induces the canonical isomorphism on cohomology. A zero morphism which is an
isomorphism has zero source and target, so $\mathcal H^j(R)=0$ for every $j<0$.
-/
theorem qbarAffineSupportBound
    (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] [IsAffineHom f] [LocallyOfFiniteType f]
    (F : CommonHeart l Ω X)
    (a : ℤ) (ha : 0 ≤ a)
    (hF : topologicalKrullDim
      (pbcQbarCohomologySupport l Ω X.scheme F.obj 0) ≤ (a.toNat : ℕ∞)) :
    (∀ q : ℕ,
      (pbcQbarCohomologySupport l Ω Y.scheme
        ((qbarDerivedDirectImage l Ω X Y f).obj F.obj) (q : ℤ)).Nonempty →
      0 ≤ a - (q : ℤ) ∧
      topologicalKrullDim
        (pbcQbarCohomologySupport l Ω Y.scheme
          ((qbarDerivedDirectImage l Ω X Y f).obj F.obj) (q : ℤ)) ≤
        ((a - (q : ℤ)).toNat : ℕ∞)) ∧
    (∀ q : ℤ, q < 0 →
      IsZero ((cohomology (commonT l Ω Y) q).obj
        ((qbarDerivedDirectImage l Ω X Y f).obj F.obj))) := by
  sorry

end AlgebraicGeometry.Scheme.PerAdic
