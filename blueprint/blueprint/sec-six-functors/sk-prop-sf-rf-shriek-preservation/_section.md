+++
id = "sk-prop-sf-rf-shriek-preservation"
kind = "section"
title = "Preservation for the exceptional inverse image"
order = 2059
uses = ["sk-def-sf-admissible", "sk-def-sf-operations", "sk-def-sf-setting", "sk-lem-sf-mate", "sk-prop-sf-existence"]
lean = ["AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion", "AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isFinite_of_etale", "AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion", "AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension", "AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek"]
+++
*Proposition (sketch).*

Let $A=A_{E,n}$ and let $f:X\to Y$ be a separated finite-type morphism of
finite-type $k$-schemes ($k=\overline{\mathbf F}_q$ as in
[sk-def-sf-setting]; the dimension bounds below are those of these
schemes), and let $Rf^!$ be the constructible exceptional adjoint of
[sk-def-sf-operations] (vi). No admissibility datum is assumed. Then
$Rf^!$ preserves the constructible intervals and the finite-Tor subcategory in
the following cases: (i) $f$ an open immersion or finite étale, with the
same interval; (ii) $f=i:Z\hookrightarrow T$ a closed immersion,
$D_c^{[a,b]}\mapsto D_c^{[a,b+2d+1]}$ for a target $T$ of dimension $\le d$
— a bound in terms of the dimension of the *target*, not of the
codimension of $Z$: no bound of the form $2\operatorname{codim}(Z,T)+1$ holds
for arbitrary closed immersions (see the proof), and the sharper codimension
statement $Ri^!\Lambda_T\cong\Lambda_Z(-c)[-2c]$ of [sk-thm-regular] is a
separate theorem with regularity hypotheses ($Z$ regular and $T$ smooth, a
regular pair, not merely a regular immersion) and a coefficient hypothesis
(the unit object); (iii) $f$ smooth of pure relative dimension $d$, with the
shift $-2d$; (iv) *every* separated finite-type $f$,
with $D_c^{[a,b]}\mapsto D_c^{[a-2D,\,b+2\dim Y+1]}$, where $D$ is the
maximal embedding dimension of the affine charts
$U\hookrightarrow\mathbf A^{d_U}_V$ of $f$ used in the proof — the sum of
the shifts of (ii) and (iii), chart by chart. Clause (iv) is a
*theorem*, not the unpacking of an assumed datum: it proves, for the
unconditional $Rf^!$, the two preservation clauses (2)–(3) of
[sk-def-sf-admissible] with explicit constants, for every separated
finite-type morphism of finite-type $k$-schemes and with constants
independent of $n$. In particular every such morphism satisfies the
constructible analogue of exceptional-adjoint admissibility at every finite
stage, and wherever a statement below assumes that a morphism "carries the
admissibility datum" in this constructible sense, the hypothesis is
discharged by this clause and [sk-prop-sf-existence] (c)
(thm:sf-preservation-class, [sk-rem-sf-fullcd-scope]).
Chapter 18 (exceptional right adjoints and constructible restrictions):
thm:exc-explicit-preservation for (i),
cor:exc-closed-preservation-datum for (ii) (with
lem:exc-residue-tor-test and lem:exc-open-complement-known);
Chapter 21 for (iii), cor:pur-smooth-admissibility, and for (iv),
cor:pur-general-admissibility-datum, which discharges the open-complement
hypothesis of its affine-base form by lem:exc-open-complement-known,
assembled stage-uniformly in thm:sf-preservation-class.

## Proof

*(i) Open immersions and finite étale morphisms.* For such $f$ the
ambient right adjoint is the exact functor $Lf^*$. Pulling back a finite
constructible stratification gives one again, and
$\mathcal H^q(Lf^*K)\cong f^*\mathcal H^q(K)$, so the constructible interval
is unchanged. Inverse image preserves flatness, so a bounded flat model in
degrees $[a,b]$ pulls back to one, giving the same Tor amplitude; applying
the exact tensor functor $f^*$ to a flat resolution also gives the
finite-level comparison
$(Rf_A^{\times}K)\otimes^{\mathrm L}_AB\cong Rf_B^{\times}(K\otimes^{\mathrm L}_AB)$, with bounds independent of $n$.

*(ii) Closed immersions.* Let $i:Z\hookrightarrow T$ be closed with
quasi-compact open complement $j:V\hookrightarrow T$ and $\dim T\le d$. The
pair $(V,T)$ satisfies the open-complement bound with $c=2d$: the
strict-henselization stalk formula writes $(R^qj_*M)_{\bar t}$ as a filtered
colimit of $H^q(V\times_TU,M)$ over pointed étale neighbourhoods $U$ of
$\bar t$, each an open of a finite-type $k$-scheme of dimension $\le d$, and
over the separably closed $k$ these vanish for $q>2d$
([sk-prop-sf-finiteness]); geometric stalks are conservative, so
$R^qj_*M=0$ there. The localization triangle
[sk-prop-sf-localization] then bounds $Ri^!$ in terms of $Rj_*$, which
produces the shift $2d+1$ on the constructible interval and, by the
residue-field test for Tor amplitude, on the amplitude as well. The bound
cannot be replaced by one depending only on the codimension of $Z$: for
$T=\operatorname{Spec}k[x,y]/(xy)$, $Z=V(y)$ (a component of $T$, so of
codimension $0$), $V=D(y)\cong\mathbf G_m$, which lies in the other component
$V(x)\cong\mathbf A^1$, and $M=\Lambda_T$ with $\Lambda=\mathbf F_\ell$, the
stalk $(R^1j_*\Lambda_V)_{\bar o}$ at the crossing point $o$ is $H^1$ of the
fraction field of the strictly henselian local ring of $\mathbf A^1$ at $0$
([03Q7](https://stacks.math.columbia.edu/tag/03Q7)), which is nonzero (the
Kummer class of $y$, [03PK](https://stacks.math.columbia.edu/tag/03PK)); the
localization triangle gives
$\mathcal H^2(Ri^!\Lambda_T)_{\bar o}\cong(R^1j_*\Lambda_V)_{\bar o}\neq0$,
excluded by $2\operatorname{codim}(Z,T)+1=1$ but allowed by $2\dim T+1=3$.
Even for a regular immersion into a smooth $T$ the codimension controls
$Ri^!$ only when $Z$ is regular as well: for the two axes
$Z=V(xy)\subset T=\mathbf A^2$, support Mayer–Vietoris gives
$\mathcal H^3(Ri^!\Lambda_T)_{\bar 0}\cong\Lambda(-2)\neq0$.

*(iii) Smooth morphisms.* Purity [sk-thm-smooth-purity] identifies
$Rf^!$ with $Lf^*(-)(d)[2d]$. Then $Lf^*$ is exact and preserves bounded
constructibility, the twist does not move degrees, and the shift carries
$[a,b]$ to $[a-2d,b-2d]$. For the Tor amplitude, test against the residue
field: $Rf^!K\otimes^{\mathrm L}_A\kappa\cong Lf^*(K\otimes^{\mathrm L}_A\kappa)(d)[2d]$, so the amplitude of $K$ shifts by
$-2d$ as well. The preservation clauses are thus consequences of purity, not
hypotheses of it.

*(iv) The general case.* For every separated finite-type $f$ the
functor $Rf^!$ of [sk-def-sf-operations] (vi) is defined, and the two
preservation clauses are *proved* as follows; nothing is assumed.
Constructibility and finite Tor amplitude, with given bounds, are local on
$X$. Cover $Y$ by affine opens $V$ and each $f^{-1}(V)$ by affine opens $U$,
with $u:U\hookrightarrow X$ the open immersion; $U\to V$ is affine of finite
type, hence factors as a closed immersion $i_U:U\hookrightarrow\mathbf
A^{d_U}_V$ followed by the smooth projection $\pi_U:\mathbf A^{d_U}_V\to V$.
By [sk-lem-sf-mate] (b), applied to $fu=\pi_Ui_U$ and to the open immersion
$u$ (whose $R(-)_!$ is $u_!$, with right adjoint $Lu^*$),
$Lu^*Rf^!\cong R(fu)^!\cong Ri_U^!\,R\pi_U^!$, so the restriction of $Rf^!L$
to $U$ is $Ri_U^!(R\pi_U^!(L|_V))$. Now compose (iii) with (ii): the smooth
projection shifts $[a,b]$ to $[a-2d_U,b-2d_U]$, and the closed immersion
into the target $\mathbf A^{d_U}_V$ of dimension $\le d_U+\dim Y$ then gives
$[a-2d_U,\,b-2d_U+2(d_U+\dim Y)+1]=[a-2d_U,\,b+2\dim Y+1]$; the maximum over
the finitely many charts is $[a-2D,\,b+2\dim Y+1]$ with $D=\max_Ud_U$, and
the same computation on the residue-field test gives the Tor amplitude. The
open-complement hypothesis of the affine-base form is discharged by the
$c=2d$ bound established in (ii), so it is a theorem here and not an
assumption. The constants depend on the charts and on $\dim Y$ only, not on
$n$, which is what the adic stages need ([sk-thm-sf-ctf-stability] (vii)).

Uses: `\Cref{sk-def-sf-admissible}`, [sk-def-sf-operations], [sk-prop-sf-existence], [sk-lem-sf-mate], `thm-sf-preservation-class`, `cor-pur-general-admissibility-datum`, `cor-pur-general-admissibility-datum`, `cor-pur-smooth-admissibility`, `lem-exc-open-complement-known`, `lem-exc-residue-tor-test`, `thm-exc-explicit-preservation`
