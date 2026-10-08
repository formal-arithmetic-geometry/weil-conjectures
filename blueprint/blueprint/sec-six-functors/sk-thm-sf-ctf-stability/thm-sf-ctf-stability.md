+++
id = "thm-sf-ctf-stability"
kind = "theorem"
title = "Preservation on the proved finite-Tor domains"
order = 2213
uses = ["cor-coef-finite-verdier", "cor-pur-general-admissibility-datum", "cor-pur-smooth-admissibility", "cor-coef-integral-internal-hom", "cor-sf-direct-image-ctf-proetale", "cor-sf-hom-ctf-proetale-unconditional", "cor-weil-finite-constructible-hom", "def-compact-support-direct-image-detailed", "def-weil-derived-complete-integral-detailed", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-scheme-morphism-properties", "def-weil-site-perfect-complex", "lem-coef-finite-direct-image", "lem-coef-finite-exceptional", "lem-coef-integral-hom-reduction", "lem-coef-integral-residue-tor", "lem-coef-rational-operations", "lem-exc-constant-inverse-image-flat", "lem-fix-operation-reduction", "lem-sf-etale-direct-image-vanishing", "lem-weil-pbc-pullback-preserves-bounded-constructible", "prop-coef-integral-exceptional-adjoint", "prop-exc-closed-tor", "prop-sf-dualizable-hom", "thm-coef-finite-hom", "thm-coef-integral-verdier", "thm-coef-qbar-verdier", "thm-coef-rational-verdier", "thm-fix-general-biduality", "thm-pur-general-admissibility", "thm-pur-open-complement-unconditional", "thm-sf-direct-image-tor-amplitude", "thm-sf-hom-ctf", "thm-sf-preservation-class"]
+++
Fix the finite-field datum,
$A=A_{E,n}$, and separated finite-type morphisms between separated finite-type
$k$-schemes. Use the bounded
constructible categories and their
finite-Tor subcategories.
At this finite coefficient stage the following hold:

1. **(i)** $Lf^*$ carries $D^b_{ctf}(Y,A)$ into
$D^b_{ctf}(X,A)$.
1. **(ii)** Derived tensor carries
$D^b_{ctf}\times D^b_{ctf}$ into $D^b_{ctf}$; if the two inputs have
Tor amplitude in $[a,b]$ and $[c,d]$, the output has Tor amplitude in
$[a+c,b+d]$.
For $K,L\in D^b_{ctf}(X,A)$, internal Hom has this same conclusion.
If $K,L$ have Tor amplitude in $[a,b]$ and $[c,d]$ and
$\dim X\leq m$, then $R\mathcal Hom(K,L)$ has Tor amplitude in
$[c-b-2m,d-a+2m]$; if moreover $K$ is site-perfect, it has Tor
amplitude in the sharper interval $[c-b,d-a]$.
The elementary formula $R\mathcal Hom(K,L)=K^\vee\otimes^L L$
with coefficient dual $K^\vee=R\mathcal Hom(K,A_X)$, and the
dimension-free interval $[c-b,d-a]$, still require
a site-perfect first argument (for the origin
$i:\{0\}\hookrightarrow\mathbf A^1$, both $i_*A$ and $A$ have Tor
amplitude $[0,0]$, while $R\mathcal Hom(i_*A,A)=i_*A(-1)[-2]$ has
cohomology in degree $2$);
the general preservation assertion uses geometric Verdier duality.
1. **(iii)** $Rf_*$ carries $D^b_{ctf}(X,A)$ into
$D^b_{ctf}(Y,A)$; for input Tor amplitude $[a,b]$ and
$\dim X\leq d$, the output has Tor amplitude in $[a,b+2d]$.
1. **(iv)** $Rf_!$ carries $D^b_{ctf}(X,A)$ into
$D^b_{ctf}(Y,A)$.
1. **(v)** The exceptional adjoint on the constructible
coefficient category satisfies $Rf^!=D_Xf^*D_Y$ and carries
$D^b_{ctf}(Y,A)$ into $D^b_{ctf}(X,A)$.
For input Tor interval $[a,b]$, one output interval is
$[a-2\dim X,b+2\dim Y]$.
1. **(vi)** For every separated finite-type $X/k$,
$D_X=R\mathcal Hom_X(-,Ra_X^!A)$ is a contravariant exact
anti-equivalence with $K\simeq D_XD_XK$, by the geometric
Verdier-biduality theorem on this domain.
1. **(vii)** On the finite-Tor constructible domains,
finite coefficient quotients commute with pullback, tensor, both
direct images, general internal Hom, Verdier duality and the
exceptional adjoint, preserving their evaluation and adjunction maps.
For derived-complete
integral objects, $D^b_c(X,\mathcal O_E)=D^b_{ctf}(X,\mathcal O_E)$.
General internal Hom and the exceptional adjoint preserve this
category; Verdier duality is an anti-equivalence on it, with the
canonical finite reductions of these operations. These conclusions
pass to the bounded constructible categories at $E$ and
$\Qlb$, with their specified coefficient-passage operations.
The elementary site-perfect formula in (ii) retains its stated
hypothesis. No unrestricted unbounded pro-etale exceptional
adjunction is asserted here.

## Proof

For (i), bounded constructibility is
[lem-weil-pbc-pullback-preserves-bounded-constructible], and
flat inverse image in [lem-exc-constant-inverse-image-flat]
preserves the Tor interval of
[def-weil-finite-tor-amplitude].
For (ii), the Tor intervals add under derived tensor: with bounded
flat models of $K$ in $[a,b]$ and of $L$ in $[c,d]$, the total tensor
complex is a bounded flat model in $[a+c,b+d]$. Refine the
finite constructible stratifications for the two complexes; the
bounded tensor complexes on each stratum have finite locally constant
cohomology, which gives constructibility. If $K$ is site-perfect
in [def-weil-site-perfect-complex], a bounded finite-projective
local model $P$ in $[a,b]$ computes its dual and identifies
$R\mathcal Hom(K,L)=K^\vee\otimes^L L$ by
[prop-sf-dualizable-hom]. The tensor argument proves Hom
preservation in that case, and since $P^\vee$ is a bounded
finite-projective complex in $[-b,-a]$, the tensor bound gives the
interval $[c-b,d-a]$; this is the sharper assertion of
[thm-sf-hom-ctf], whose argument is local on the site and so applies
on either site; on the pro-étale site this is [cor-sf-hom-ctf-proetale-unconditional]. For a general constructible finite-Tor
first argument, use [cor-weil-finite-constructible-hom], whose
proof uses geometric Verdier biduality and gives the
dimension-dependent interval $[c-b-2m,d-a+2m]$. The displayed
example shows the dimension-free interval fails without
site-perfectness: $R\mathcal Hom(i_*A,A)=i_*Ri^!A$ by adjunction, and
$Ri^!A=A(-1)[-2]$ by purity for the point in the smooth curve.

Clause (iii) is [cor-sf-direct-image-ctf-proetale]: its etale
calculation is [thm-sf-direct-image-tor-amplitude], with the
uniform all-sheaf cohomological bound supplied by
[lem-sf-etale-direct-image-vanishing]. That calculation uses a
bounded-above free resolution of a finite constant coefficient and
the cohomological bound; it does not use a projection formula for an
arbitrary sheaf on the target. For (iv), choose a compactification
$f=pj$ and use [def-compact-support-direct-image-detailed].
Extension by zero $j_!$ is exact and commutes with tensor, as is
seen on stalks, so preserves the Tor interval and constructibility.
Apply (iii) to the proper factor $p$.

Clause (v) is the preservation result for the exceptional inverse
image, assembled from the closed and smooth cases. For a closed immersion
$i:Z\hookrightarrow T$ with $\dim T\leq d$, the open complement satisfies
the open-complement condition with $c=2d$ by
[thm-pur-open-complement-unconditional], so [prop-exc-closed-tor]
carries bounded constructible input of Tor amplitude $[a,b]$ to bounded
constructible output of Tor amplitude $[a,b+2d+1]$. For $f$ smooth of pure
relative dimension $d$, purity identifies $Rf^!$ with $Lf^*(-)(d)[2d]$ and
[cor-pur-smooth-admissibility] gives the shift $-2d$ on both intervals.
A general $f$ is, on affine charts $U\subseteq f^{-1}(V)$, a closed
immersion $U\hookrightarrow\mathbf A^{d_U}_V$ followed by the smooth
projection, and composing the two cases along the charts is
[thm-pur-general-admissibility]; its open-complement hypothesis on the
charts is discharged by [cor-pur-general-admissibility-datum], so it is a
theorem and not an assumption. At the finite stage $A=A_{E,n}$ and for every
separated finite-type $f$ of the statement this is
[thm-sf-preservation-class](2): $Rf^!$ carries $D^b_{ctf}(Y,A)$ into
$D^b_{ctf}(X,A)$, with no ambient datum assumed on that category. With this
preservation, the finite dual formula and adjunction of
[lem-coef-finite-exceptional] identify $Rf^!$ with $D_Xf^*D_Y$ on this
domain; applying the finite duality bound on $Y$, ordinary pullback, and
the finite duality bound on $X$ gives the displayed output interval. Clause (vi) is
[thm-fix-general-biduality] at finite coefficients;
its geometric proof supplies the
anti-equivalence and is not replaced by the site-perfect calculation
in (ii).

For (vii), use [lem-fix-operation-reduction] for pullback,
tensor and compact supports, and [lem-coef-finite-direct-image]
for ordinary direct image. General finite internal-Hom and duality
comparisons are [thm-coef-finite-hom], [cor-coef-finite-verdier];
the exceptional comparison is [lem-coef-finite-exceptional].
Their proofs compare the specified evaluations and adjunction maps.

At integral coefficients, [lem-coef-integral-residue-tor]
identifies the two constructible categories. General internal Hom
and its finite reductions are
[cor-coef-integral-internal-hom], [lem-coef-integral-hom-reduction].
The anti-equivalence and exceptional adjunction are
[thm-coef-integral-verdier], [prop-coef-integral-exceptional-adjoint].
These proofs establish normalized-tower effectivity and the finite
reductions with uniform bounds; they do not infer a common integral
local model merely from levelwise constructibility.
Finally [thm-coef-rational-verdier], [lem-coef-rational-operations]
identify the operations after rationalization, and
[thm-coef-qbar-verdier] transports them to the common-stage
category, including its retracts. Their adjunctions have precisely
the bounded constructible domains stated in those results.
