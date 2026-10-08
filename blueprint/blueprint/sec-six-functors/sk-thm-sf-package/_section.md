+++
id = "sk-thm-sf-package"
kind = "section"
title = "The six-operations package"
order = 2232
uses = ["sk-cor-sf-direct-image-ctf", "sk-def-sf-admissible", "sk-def-sf-kv-maps", "sk-def-sf-operations", "sk-lem-sf-flat-model", "sk-lem-sf-mate", "sk-lem-sf-twist-interchange", "sk-prop-cohsm", "sk-prop-nagata-sketch-comp-category", "sk-prop-sf-biduality-general", "sk-prop-sf-cbc", "sk-prop-sf-comp-coherence", "sk-prop-sf-comp-proper", "sk-prop-sf-comparison", "sk-prop-sf-dualizable-biduality", "sk-prop-sf-existence", "sk-prop-sf-finiteness", "sk-prop-sf-kunneth-ordinary", "sk-prop-sf-pf-coherence", "sk-prop-sf-pf-reduction", "sk-prop-sf-rf-shriek-preservation", "sk-rem-sf-matrix", "sk-thm-nagata-compactification", "sk-thm-properbasechange", "sk-thm-purity-transport", "sk-thm-sf-comp-composition", "sk-thm-sf-ctf-stability", "sk-thm-sf-direct-image-tor-amplitude", "sk-thm-sf-dual-perfect", "sk-thm-sf-global-duality", "sk-thm-sf-hom-ctf", "sk-thm-sf-identification", "sk-thm-sf-kunneth-relative", "sk-thm-sf-kunneth-verdier", "sk-thm-sf-pf-adic", "sk-thm-sf-pf-field", "sk-thm-sf-pf-finite", "sk-thm-sf-pf-proetale", "sk-thm-sf-tensor-hom", "sk-thm-sf-verdier-exchange", "sk-thm-smooth-base-change", "sk-thm-smooth-purity"]
lean = ["AlgebraicGeometry.Etale.SixOperationsPackage", "AlgebraicGeometry.Etale.sixOperationsPackage"]
+++
*Theorem (sketch).*

Fix the coefficient stages of [sk-def-sf-setting] and let $f:X\to Y$ be a
separated finite-type morphism of finite-type $k$-schemes. Then the six
operations of [sk-def-sf-operations] exist as functors of the ambient
categories, they descend to the small categories as in [sk-rem-sf-typing],
and they satisfy:

2pt
1. **(1)** *Adjunctions.* The functor $Lf^*$ is exact, hence preserves
bounded-below objects, and its restriction
$Lf^*:D^+(Y,\Lambda)\to D^+(X,\Lambda)$ is left adjoint to
$Rf_*:D^+(X,\Lambda)\to D^+(Y,\Lambda)$:
$\operatorname{Hom}_{D^+(X,\Lambda)}(Lf^*K,L)\cong \operatorname{Hom}_{D^+(Y,\Lambda)}(K,Rf_*L)$, naturally in
$K\in D^+(Y,\Lambda)$ and $L\in D^+(X,\Lambda)$ (both functors typed between
the same pair of categories); the constructible exceptional adjoint
$Rf^!:\Dctf(Y,\Lambda)\to\Dctf(X,\Lambda)$ of [sk-def-sf-operations] (vi) is
right adjoint to $Rf_!:\Dctf(X,\Lambda)\to\Dctf(Y,\Lambda)$,
unconditionally, with units and counits compatible with composition,
refinements and exchanges ([sk-prop-sf-existence] (c),
[sk-prop-sf-rf-shriek-preservation], [sk-lem-sf-mate] (b),
fix-prop-adjunctions); and — an optional ambient statement, used by
nothing below — whenever $f$ carries the ambient datum of
[sk-def-sf-admissible] (1), the ambient functor
$Rf_!:D(X,\Lambda)\to D(Y,\Lambda)$ is left adjoint to the ambient functor
$Rf^{\times}:D(Y,\Lambda)\to D(X,\Lambda)$ of [sk-def-sf-operations] (v),
whose restriction to $\Dctf$ then agrees with $Rf^!$ (that datum fails in
general, [sk-rem-sf-fullcd-scope]).
1. **(2)** *Base change.* For every Cartesian square the exchange
transformation $\operatorname{Ex}_!:Lg^*Rf_!\to Rf'_!Lg'^*$ of
[sk-def-sf-exchanges] is a natural isomorphism with exactly the typing of
[sk-prop-sf-cbc] — at $\Lambda=A_{E,n}$ on $D^+$ of the small étale site
and on the étale-origin complexes of the pro-étale site; at
$\mathcal O_E,E,\Qlb$ only on $\Dbc$ of the adic pro-étale categories, as
the completed exchange, and never on the discrete non-torsion coefficients of
the small étale site, exactly as for $\operatorname{Ex}_*$ below; it is the
identity for the identity square,
compatible with pasting of squares, independent of the compactification
(compatible with the refinement comparisons of [sk-prop-sf-comp-coherence])
and compatible with the composition law of [sk-thm-sf-comp-composition],
the last two on the étale-origin complexes of [sk-def-sf-operations] (iv)
([sk-prop-sf-cbc], fix-lem-exchanges).
The exchange transformation $\operatorname{Ex}_*:Lg^*Rf_*\to Rf'_*Lg'^*$ is a
natural isomorphism for proper $f$ ([sk-thm-properbasechange]) and for
smooth $g$ ([sk-thm-smooth-base-change]), *with the following typing
only*: (a) at a finite stage $\Lambda=A_{E,n}$, as functors
$D^+(X,\Lambda)\to D^+(Y',\Lambda)$ on the small étale site
(thm:weil-pbc-bounded-below,
sbc-thm-bounded-below-derived-smooth-base-change) and on the
étale-origin complexes of the pro-étale site
(thm:weil-pbc-finite-level-proetale; for smooth $g$ on the bounded
constructible ones, sbc-thm-finite-proetale-smooth-base-change); (b) at the stages
$\mathcal O_E$, $E$, $\Qlb$, only on $\Dbc$ of the pro-étale (adic)
categories — derived-complete $\mathcal O_E$-complexes whose reductions are
of étale origin, their rationalizations and the $\Qlb$-colimit, with
$\operatorname{Ex}_*$ the completed exchange — where it is deduced from (a)
by derived limits over the finite reductions and then transported by
rationalization and scalar extension, exactly as the projection formula is in
[sk-thm-sf-pf-adic] and [sk-thm-sf-pf-field]
(cor:weil-pbc-constructible-complete, thm:weil-pbc-finite-extension,
thm:weil-pbc-qbar; sbc-thm-adic-smooth-base-change,
sbc-thm-e-coefficient-smooth-base-change,
sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). No
assertion is made for the discrete non-torsion coefficients $\mathcal O_E,E,\Qlb$
on the small étale site, where $\operatorname{Ex}_*$ is not an isomorphism in
general.
1. **(3)** *Projection formula.* $\operatorname{PF}_{f,K,L}$ is an
isomorphism in $D^+(Y,\Lambda)$ at every coefficient stage, natural and
coherent, including compatible with base change through the
$\operatorname{Ex}_!$ of clause (2) (the base-change clause of
[sk-prop-sf-pf-coherence])
([sk-thm-sf-pf-finite], [sk-prop-sf-pf-reduction],
[sk-thm-sf-pf-adic], [sk-thm-sf-pf-field], [sk-thm-sf-pf-proetale],
[sk-prop-sf-pf-coherence]); the interface
fix-prop-projection-formula is discharged ([sk-rem-sf-pf-done]).
1. **(4)** *Compactifications and proper coincidence.*
$Rf_!=R\bar f_*j_!$ is independent of the compactification with the composition
law $R(gf)_!\cong Rg_!Rf_!$, and $Rf_!\cong Rf_*$ for proper $f$
([sk-prop-sf-comp-coherence], [sk-thm-sf-comp-composition],
[sk-prop-sf-comp-proper]).
1. **(5)** *Orientation.* For smooth $f$ of pure relative dimension $d$
the purity map $\gamma_{f,K}:Lf^*K(d)[2d]\to Rf^!K$ (the orientation of
[sk-def-sf-orientation]) is a natural isomorphism of functors
$\Dctf(Y,\Lambda)\to\Dctf(X,\Lambda)$; in particular
$\omega_f\cong\Lambda_X(d)[2d]$ ([sk-thm-smooth-purity], with
[sk-thm-purity-transport] for the remaining coefficient stages). It is
compatible with composition of smooth morphisms (twist additivity, through
the mate isomorphism $R(gf)^!\cong Rf^!Rg^!$ of [sk-lem-sf-mate]) and with
base change — along arbitrary $g$ at $\Lambda=A_{E,n}$, along étale $g$ at
the other stages — where the base-change isomorphism
$Lg'^*Rf^!\to Rf'^!Lg^*$ of [sk-prop-cohsm] (c) is the mate of
$\operatorname{Ex}_!$ under $Rf_!\dashv Rf^!$ and $Rf'_!\dashv Rf'^!$; under
$\gamma_f,\gamma_{f'}$ it becomes the canonical isomorphism
$Lg'^*Lf^*\cong Lf'^*Lg^*$, i.e. the trace (the exceptional counit read
through $\gamma$) is compatible with $\operatorname{Ex}_!$. At
$\Lambda=A_{E,n}$ it is compatible with the exceptional Künneth map: for
smooth $f_i:X_i\to Y_i$ of pure relative dimensions $d_i$ and
$L_i\in\Dctf(Y_i,\Lambda)$, the map $\alpha$ of [sk-def-sf-kv-maps] (ii)
corresponds under $\gamma_{f_1}\boxtimes\gamma_{f_2}$ and
$\gamma_{f_1\times f_2}$ to the canonical pullback–tensor isomorphism
$Lf_1^*L_1(d_1)[2d_1]\boxtimes Lf_2^*L_2(d_2)[2d_2]\cong
L(f_1\times f_2)^*(L_1\boxtimes L_2)(d_1+d_2)[2d_1+2d_2]$ (the smooth step of
the proof of [sk-thm-sf-kunneth-verdier]; the Künneth–Verdier
isomorphism itself stays outside the package).
1. **(6)** *Duality.* With $\omega_X=Ra_X^!\Lambda$ formed from the
constructible exceptional adjoint of [sk-def-sf-operations](vi) (no
admissibility datum is assumed; [sk-prop-sf-biduality-general] is
unconditional, [sk-rem-sf-ledger]),
$\mathbb D_X:\Dctf(X,\Lambda)\to\Dctf(X,\Lambda)$,
$\mathbb D_X=\RHom_X(-,\omega_X)$ with $\omega_X=Ra_X^!\Lambda$, is a
contravariant exact anti-equivalence,
and the biduality morphism $\delta_K:K\to\mathbb D_X\mathbb D_XK$ (the
tensor–Hom transpose of the evaluation
$K\otimes^L_\Lambda\mathbb D_XK\to\omega_X$) is a natural isomorphism
$\delta:\mathrm{id}\xrightarrow{\sim}\mathbb D_X\mathbb D_X$
([sk-prop-sf-biduality-general]). For every separated finite-type $f$,
the Verdier exchange map
$\varepsilon_{f,M}:\mathbb D_Y(Rf_!M)\to Rf_*\mathbb D_X(M)$ of
[sk-thm-sf-verdier-exchange] — the tensor–Hom isomorphism of
[sk-thm-sf-tensor-hom] at $N=\omega_Y$ followed by
$Rf_*\RHom_X(M,-)$ of the mate isomorphism $Rf^!\omega_Y\cong\omega_X$ —
is a natural isomorphism in $D^+(Y,\Lambda)$ for $M\in\Dctf(X,\Lambda)$; it
is compatible with composition: for $X\xrightarrow{f}Y\xrightarrow{g}Z$,
$\varepsilon_{gf,M}$ agrees, through $\mathbb D_Z(\alpha_{g,f})$ and
$R(gf)_*\cong Rg_*Rf_*$, with
$Rg_*(\varepsilon_{f,M})\circ\varepsilon_{g,Rf_!M}$ (associativity of
$\operatorname{PF}$, [sk-prop-sf-pf-coherence], and the mate calculus
[sk-lem-sf-mate]; fix-prop-coherence). No compatibility of
$\varepsilon$ with base change along an arbitrary $g$ is asserted
($\mathbb D$ does not commute with $Lg^*$ in general).
Unconditionally, for $X$ smooth of pure dimension $d$ and perfect $K$, the
orientation-induced
isomorphism $\theta_K:\mathbb D_XK\xrightarrow{\sim}K^\vee(d)[2d]$ of
[sk-thm-sf-dual-perfect] is natural in $K$
([sk-thm-sf-dual-perfect], [sk-prop-sf-dualizable-biduality]); the
global duality map $\RG_c(X,K)^\vee\to\RG(X,\mathbb D_XK)$ of
[sk-thm-sf-global-duality] is an isomorphism in the point category; and the
derived Poincaré pairing is perfect and is the duality isomorphism
([sk-thm-sf-identification]).
1. **(7)** *Relative product.*
The relative Künneth map
$\kappa^{\mathrm{rel}}_{K,L}:R(f\times_Bg)_!(K\boxtimes L)\to
Rf_!K\otimes^LRg_!L$ of [sk-thm-sf-kunneth-relative] (the composite of the
composition law, the inverse projection transformations for $q$ and $g$ and
the inverse of $\operatorname{Ex}_!$) is a natural isomorphism in
$D^+(B,\Lambda)$, compatible with symmetry, triple products, base change
$B'\to B$ and the projection formula as stated there (the symmetry and
base-change compatibilities rest on the base-change clause of
[sk-prop-sf-pf-coherence], i.e. on clause (3)), with its
compact-support form on closed subschemes ([sk-thm-sf-kunneth-relative]).
1. **(8)** *Stability.* The operations descend to the constructible and
finite-Tor subcategories exactly as typed in [sk-thm-sf-ctf-stability] and
[sk-rem-sf-matrix], with the explicit amplitude shifts
$[a,b+2d]$ for $Rf_*$, $[a+c,b+d]$ for $\otimes^L$, $[c-b-2d,d'-a+2d]$
for $\RHom$ of objects with amplitudes $[a,b],[c,d']$ on a scheme of
dimension $\le d$ ($[c-b,d'-a]$ for a site-perfect first argument), and
for $Rf^!$ the shifts of [sk-prop-sf-rf-shriek-preservation]: $-2d$ for
$f$ smooth of pure relative dimension $d$, $[a,b]\mapsto[a,b+2d+1]$ for a
closed immersion into a target of dimension $\le d$ (a target-dimension
bound; no codimension-only bound is asserted for arbitrary closed
immersions), and $[a,b]\mapsto[a-2D,b+2\dim Y+1]$ in the general case, $D$
the maximal embedding dimension of the affine charts.

## Proof

Every clause is one of the propositions of §§ *What the earlier chapters prove* or
§§ *What this section proves*, with the following assembly.
Clause (1) is fix-prop-adjunctions together with
[sk-prop-sf-existence](a) and (c): the étale adjoint exists
unconditionally on the ordinary étale derived categories and is transported
to the small pro-étale categories along the comparison, the preservation
being [sk-prop-sf-rf-shriek-preservation] — enough for every clause
below, all of which are typed on the small categories
([sk-rem-sf-fullcd-scope]); the ambient half of (1) is conditional on the
ambient datum and is consumed by nothing. Clause (2) is [sk-prop-sf-cbc], [sk-thm-properbasechange] and
[sk-thm-smooth-base-change] respectively: the first is proved in Chapter 17, the second
in §[sec-proper-base-change], the third in §[sec-smooth-base-change],
and none of them uses anything proved
in this section except the definitions. The latter two are statements about
torsion sheaves; their bounded-below forms at $A_{E,n}$ are the truncation
dévissage thm:weil-pbc-bounded-below and
sbc-thm-bounded-below-derived-smooth-base-change, transported to the
pro-étale site along the comparison of [sk-prop-sf-comparison], and the
$\mathcal O_E$, $E$, $\Qlb$ forms on $\Dbc$ of the adic categories are the
derived-limit, rationalization and scalar-extension transports cited in the
clause — the same three steps as [sk-thm-sf-pf-adic] and
[sk-thm-sf-pf-field]. The coherence of $\operatorname{Ex}_!$ is
fix-lem-exchanges. Clause (3) is the projection-formula
chain of §§ *What this section proves*: the finite case [sk-thm-sf-pf-finite] reduces to
the compact-support projection formula of the framework chapter, and
[sk-prop-sf-pf-reduction], [sk-thm-sf-pf-adic], [sk-thm-sf-pf-field] and
[sk-thm-sf-pf-proetale] transport it to the remaining stages, with
[sk-prop-sf-pf-coherence] for the coherence. Clause (4) is
[sk-thm-nagata-compactification] and [sk-prop-nagata-sketch-comp-category]
for the compactifications themselves, and [sk-prop-sf-comp-coherence],
[sk-thm-sf-comp-composition], [sk-prop-sf-comp-proper] of
§§ *What this section proves* for the independence, the composition law and proper
coincidence. Clause (5) is
[sk-thm-smooth-purity] of §[sec-smooth-purity], with
[sk-prop-cohsm] for the tensor form and [sk-thm-purity-transport] for the
$\mathcal O_E$, $E$ and $\Qlb$ stages; it is what makes the orientation of
[sk-def-sf-orientation] a theorem. Its compatibility with composition and
with $\operatorname{Ex}_!$ is the composition and base-change compatibility
of [sk-thm-smooth-purity] and [sk-prop-cohsm] (c), read through
[sk-lem-sf-mate]; its compatibility with $\alpha$ is the smooth step of the
proof of [sk-thm-sf-kunneth-verdier]. Clause (6) is
[sk-prop-sf-biduality-general] (Chapter 1), [sk-thm-sf-verdier-exchange]
and [sk-thm-sf-global-duality] and [sk-thm-sf-identification]
(§§ *What this section proves*, using [sk-thm-sf-tensor-hom]), with
[sk-prop-sf-dualizable-biduality], [sk-lem-sf-twist-interchange] and
[sk-thm-sf-dual-perfect] for the perfect case; the compatibility of
$\varepsilon$ with composition is obtained by pasting the tensor–Hom chain of
[sk-thm-sf-tensor-hom] for $f$ and for $g$, using the associativity pentagon
of [sk-prop-sf-pf-coherence] and [sk-lem-sf-mate]
(fix-prop-coherence). Clause (7) is
[sk-thm-sf-kunneth-relative], whose proof uses clause (2), clause (3)
(with the base-change clause of [sk-prop-sf-pf-coherence] for its
coherence), clause (4) and, for the typing of $\operatorname{PF}_g$, clause
(8)(iv). Clause (8) is [sk-thm-sf-ctf-stability], whose proof uses
[sk-lem-sf-flat-model], [sk-thm-sf-direct-image-tor-amplitude],
[sk-cor-sf-direct-image-ctf], [sk-thm-sf-hom-ctf],
[sk-prop-sf-finiteness], [sk-prop-sf-comparison] and
[sk-prop-sf-rf-shriek-preservation]. No clause assumes a property that is
not proved in the blueprint: the *Conditional on* lines of
[sk-prop-sf-existence], [sk-prop-sf-biduality-general] and
[sk-thm-sf-ctf-stability] are the
complete list of what is conditional, and they are restated in the ledger
below.

Uses: `\Cref{sk-cor-sf-direct-image-ctf}`, `\Cref{lem-sf-flat-model}`, `\Cref{lem-sf-twist-interchange}`, `\Cref{sk-prop-cohsm}`, `\Cref{sk-prop-nagata-sketch-comp-category}`, `\Cref{sk-prop-sf-biduality-general}`, `\Cref{sk-prop-sf-cbc}`, `\Cref{sk-prop-sf-comp-coherence}`, `\Cref{sk-prop-sf-comp-proper}`, `\Cref{sk-prop-sf-comparison}`, `\Cref{sk-prop-sf-dualizable-biduality}`, `\Cref{sk-prop-sf-existence}`, `\Cref{sk-prop-sf-finiteness}`, `\Cref{sk-prop-sf-kunneth-ordinary}`, `\Cref{prop-sf-pf-coherence}`, `\Cref{prop-sf-pf-reduction}`, `\Cref{sk-prop-sf-rf-shriek-preservation}`, `\Cref{sk-rem-sf-matrix}`, `\Cref{thm-nagata-compactification}`, `\Cref{sk-thm-properbasechange}`, `\Cref{sk-thm-purity-transport}`, `\Cref{thm-sf-comp-composition}`, `\Cref{thm-sf-ctf-stability}`, `\Cref{thm-sf-direct-image-tor-amplitude}`, `\Cref{thm-sf-dual-perfect}`, `\Cref{thm-sf-global-duality}`, `\Cref{thm-sf-hom-ctf}`, `\Cref{thm-sf-identification}`, `\Cref{thm-sf-kunneth-relative}`, `\Cref{thm-sf-pf-adic}`, `\Cref{thm-sf-pf-field}`, `\Cref{thm-sf-pf-finite}`, `\Cref{thm-sf-pf-proetale}`, `\Cref{sk-thm-sf-tensor-hom}`, `\Cref{thm-sf-verdier-exchange}`, `\Cref{sk-thm-smooth-base-change}`, `\Cref{sk-thm-smooth-purity}`, `\Cref{lem-sf-mate}`, `\Cref{def-sf-kv-maps}`, `\Cref{sk-thm-sf-kunneth-verdier}`, `\Cref{sk-def-sf-admissible}`
