+++
id = "lem-a1-middle-extension-endpoints"
kind = "lemma"
title = "Degree zero and degree two"
order = 2736
uses = ["def-weil-frobenius-module-weights", "def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "def-wf-fundamental-representation", "def-wf-middle-extension", "lem-a1-affine-hc0", "lem-a1-affine-hc2", "lem-a1-geometric-coinvariants-pure", "lem-wf-tate-twist-frobenius", "lem-zl-affine-curve-range", "prop-a1-curve-boundary-sequence"]
lean = ["AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage", "AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero", "AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two", "AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two"]
+++
Let $j:U_0\hookrightarrow C_0$ be a dense open immersion, with $C_0$ a
smooth geometrically connected affine curve over $k_0=\mathbf F_q$, and
let $\mathcal F$ be a lisse Weil sheaf on $U_0$ with generic geometric
representation $V$ ([def-wf-fundamental-representation]). For the
middle extension $j_*\mathcal F$ of [def-wf-middle-extension], in the
compactly supported cohomology of [def-weil-ordinary-compact-cohomology],

$$
H_c^0(C,j_*\mathcal F)=0,\qquad
H_c^2(C,j_*\mathcal F)\simeq V_{\pi_1(U)}(-1)
$$

Frobenius-equivariantly, and $H_c^r(C,j_*\mathcal F)=0$ for
$r\notin\{0,1,2\}$. If $\mathcal F$ is punctually $\iota$-pure of weight
$w$, then $H_c^2(C,j_*\mathcal F)$ is $\iota$-pure of weight $w+2$
(possibly zero).

## Proof

As a dense open subscheme of the irreducible affine curve $C_0$ (and
likewise after base change to $k$), $U_0$ is a smooth geometrically
connected affine curve: the complement $Z_0=C_0\setminus U_0$ is a
finite set of closed points, and the complement of finitely many closed
points in an affine curve is affine. So the results on affine curves
apply to $(U_0,\mathcal F)$.

*Degree zero.* A class in $H_c^0(C,j_*\mathcal F)$ is a global section
$s$ of $j_*\mathcal F$ over $C$ whose support is proper over $k$. By
definition of the ordinary direct image,
$\Gamma(C,j_*\mathcal F)=\Gamma(U,\mathcal F)$, so $s$ corresponds to a
section $s|_U$ of the lisse sheaf $\mathcal F$ on $U$, and $s=0$ if and
only if $s|_U=0$. If $s\neq0$, then $s|_U$ is a nonzero section of a
lisse sheaf on the connected curve $U$, hence has nonzero germ at every
point of $U$ (as in the proof of [lem-a1-affine-hc0]). The support of
$s$ is closed in $C$ and contains $U$, hence is all of $C$, since $U$ is
dense. But $C$ is an affine curve, so it is not proper over $k$. Thus
$s=0$ and $H_c^0(C,j_*\mathcal F)=0$.

*Degree two and the range.* The boundary localization triangle
[prop-a1-curve-boundary-sequence] for $j$, with $i:Z\hookrightarrow C$,

$$
R\Gamma_c(U,\mathcal F)\longrightarrow
R\Gamma_c(C,j_*\mathcal F)\longrightarrow
R\Gamma_c(Z,i^*j_*\mathcal F)\longrightarrow,
$$

has its third term concentrated in degree zero. Its long exact
sequence therefore gives isomorphisms
$H_c^r(U,\mathcal F)\xrightarrow{\sim}H_c^r(C,j_*\mathcal F)$ for all
$r\geq2$ and for all $r<0$. The lisse sheaf $\mathcal F$ is
constructible, so [lem-zl-affine-curve-range] on the affine curve
$U_0$ gives $H_c^r(U,\mathcal F)=0$ for $r\notin\{0,1,2\}$; hence
$H_c^r(C,j_*\mathcal F)=0$ for $r\notin\{0,1,2\}$. For $r=2$, composing
with the canonical Frobenius-equivariant isomorphism of
[lem-a1-affine-hc2] on $U_0$ gives

$$
H_c^2(C,j_*\mathcal F)\;\simeq\;H_c^2(U,\mathcal F)\;\simeq\;
V_{\pi_1(U)}(-1).
$$

The triangle is formed from Weil complexes over $k_0$, so the
isomorphism $H_c^2(U,\mathcal F)\to H_c^2(C,j_*\mathcal F)$ commutes
with the Frobenius operators, and the composite is
Frobenius-equivariant.

*Purity.* Suppose $\mathcal F$ is punctually $\iota$-pure of weight
$w$. By [lem-a1-geometric-coinvariants-pure] the coinvariant quotient
$W=V_{\pi_1(U)}$ with its induced Frobenius $F_W$ is $\iota$-pure of
weight $w$. On the twist $W(-1)$ the Frobenius is $q\,F_W$, by the
stalk formula of [lem-wf-tate-twist-frobenius] for $E(-1)$ over
$k_0=\mathbf F_q$. So every eigenvalue of Frobenius on $W(-1)$ has
$\iota$-modulus $q\cdot q^{w/2}=q^{(w+2)/2}$, and $W(-1)$, hence
$H_c^2(C,j_*\mathcal F)$, is $\iota$-pure of weight $w+2$ in the sense
of [def-weil-frobenius-module-weights]. It may be zero, which happens
exactly when $V$ has no nonzero geometrically constant quotient.
