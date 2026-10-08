+++
id = "thm-sf-identification"
kind = "theorem"
title = "The pairing is the duality isomorphism"
order = 2186
uses = ["def-sf-cup", "def-sf-orientation", "def-sf-pairing", "def-sf-pf", "lem-sf-detection", "lem-sf-mate", "lem-sf-tensor-hom", "lem-sf-twist-interchange", "thm-sf-global-duality"]
+++
In the setting of [def-sf-pairing] — so $X$ satisfies the hypotheses of
[thm-sf-global-duality]: $X$ is proper, or $X=X_0\times_{k_0}k$ with $X_0$
smooth, separated of finite type and geometrically connected, and no
properness is required in the latter case — suppose in addition that $K$ is
perfect over $\Lambda_X$ and that the orientation of
[def-sf-orientation] is fixed. Then the tensor–internal-Hom adjoint of
$\beta_K$ is the canonical isomorphism

$$
b_K^\sharp:\ R\Gamma\bigl(X,K^\vee(d)\bigr)[2d]\xrightarrow{\ \sim\ }
R\operatorname{Hom}_\Lambda\bigl(R\Gamma_c(X,K),\Lambda\bigr)
$$

in the point category $D^b_c(s,\Lambda)$, and its inverse is the global
duality isomorphism of [thm-sf-global-duality] followed by the
identification $\mathbb D_XK\cong K^\vee(d)[2d]$ induced by the orientation.
In particular $\beta_K$ is perfect. If $X$ is proper and
$\Lambda\in\{A_{E,n},E,\overline{\mathbf Q}_\ell\}$, its degreewise form
gives perfect pairings

$$
\langle-,-\rangle_i:H_c^i(X,K)\times H^{2d-i}\bigl(X,K^\vee(d)\bigr)
\longrightarrow\Lambda\qquad(i\in\mathbf Z),
$$

the line-valued form being $H_c^i(X,K)\times H^{2d-i}(X,K^\vee)\to \Lambda(-d)$.
For nonproper $X$ the degreewise assertion over field coefficients is
recorded separately in the Poincare duality chapter
(thm-pod-degreewise-perfectness-over-a-field).

## Proof

The cup product, the pairing and the orientation used below are those of
[def-sf-cup], [def-sf-pairing] and [def-sf-orientation],
the projection transformation is [def-sf-pf], and the interchange
law is [lem-sf-twist-interchange].
Steps 1–3 use properness of $X$ nowhere: they use only the global duality
isomorphism of [thm-sf-global-duality], which holds under either of its two
hypotheses, the orientation of [def-sf-orientation] for the smooth
morphism $a_X$, and the formal adjunction calculus of the six-functor
datum; so they prove the derived assertion for proper $X$ and for
$X=X_0\times_{k_0}k$ alike.
Step 1: the two maps. By [thm-sf-global-duality] there is a canonical
isomorphism $R\Gamma_c(X,K)^\vee\to R\Gamma(X,\mathbb D_XK)$, and by the
orientation $\mathbb D_XK=R\mathcal H om_X(K,Ra_X^!\Lambda)\cong R\mathcal H om_X(K,\Lambda_X(d)[2d])\cong K^\vee(d)[2d]$; composing gives a
canonical isomorphism
$R\Gamma_c(X,K)^\vee\to R\Gamma(X,K^\vee(d))[2d]$, whose inverse is the map
displayed in the statement. Step 2: the adjoint of the pairing is that
map. The chain of [lem-sf-tensor-hom] with $M=K$, $N=\Lambda$ and
$f=a_X$ is, by [lem-sf-mate] and the definition of the pairing, the
transpose of the composite of cup product, evaluation and trace: taking
$\operatorname{Hom}_s(T,-)$ for $T=\Lambda[-r]$ converts a map $t:T\to R\Gamma(X,K^\vee(d))[2d]$ into $b_K^\sharp\circ t$ after the identifications
of [def-sf-pf]. Step 3: conclude by [lem-sf-detection]: the two
maps agree after applying $\operatorname{Hom}_s(\Lambda[-r],-)$ for all $r$,
hence they are equal. Step 4: the degreewise form (for proper $X$) is the
shift convention $H^r(C[m])=H^{r+m}(C)$ together with the identification
$H^{-i}(C^\vee)\cong\operatorname{Hom}_\Lambda(H^i(C),\Lambda)$ for a
point complex $C$, applied to $C=R\Gamma_c(X,K)$. This identification holds
because $\operatorname{Hom}_\Lambda(-,\Lambda)$ is exact on
$\Lambda$-modules, so that $R\operatorname{Hom}_\Lambda(C,\Lambda)$ is
computed termwise and commutes with taking cohomology: for
$\Lambda=E,\overline{\mathbf Q}_\ell$ this is clear, and
$\Lambda=A_{E,n}=\mathcal O_E/\varpi_E^n$ is self-injective by Baer's
criterion — its ideals are the $\varpi_E^jA_{E,n}$, a homomorphism
$\varphi:\varpi_E^jA_{E,n}\to A_{E,n}$ sends $\varpi_E^j$ to an element
killed by $\varpi_E^{n-j}$, hence to some $\varpi_E^ja$, and
$\varphi$ extends to multiplication by $a$. The adjoint
$H^{2d-i}(X,K^\vee(d))\to\operatorname{Hom}_\Lambda(H^i_c(X,K),\Lambda)$ of
$\langle-,-\rangle_i$ is then $H^{-i}(b_K^\sharp)$, an isomorphism. (For
$\Lambda=\mathcal O_E$ the degreewise statement is false in general: a
torsion class in $H^i_c(X,K)$ pairs to zero with everything, and
$H^{-i}(C^\vee)$ acquires an $\operatorname{Ext}^1$-contribution from the
torsion of $H^{i+1}(C)$.) The line-valued form is obtained by
eliminating the invertible twist $\Lambda_X(d)$ through
$\Lambda(d)\otimes_\Lambda\Lambda(-d)\cong\Lambda$.
