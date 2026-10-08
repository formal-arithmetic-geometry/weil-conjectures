+++
id = "lem-weil-verdier-preservation-strata"
kind = "lemma"
title = "Constructible preservation before biduality"
order = 2070
uses = ["def-weil-finite-torsion-constructibility", "def-weil-open-closed-recollement", "def-weil-site-perfect-complex", "lem-sf-etale-direct-image-vanishing", "lem-weil-bounded-finite-tor-perfect", "lem-weil-stratum-ambient-hom", "thm-asd-smooth-tensor", "thm-sf-direct-image-tor-amplitude"]
+++
Let $X$ be separated of finite type over $k$.
Its ambient dualizing object is $\omega_X=Ra_X^{\times}A$.
Write $D_X=R\mathcal Hom_A(-,\omega_X)$.
Then $D_X$ carries $D^b_{ctf}(X_{\Et},A)$ into itself.
More precisely, if $\dim X\leq d$ and $K$ has Tor amplitude
in $[a,b]$, then $D_XK$ has Tor amplitude in
$[-b-2d,-a]$. This bound is independent of the exponent $n$.
This conclusion is independent of Verdier biduality and of the boundary
exchange $i^*D_X\to D_ZRi^!$.

## Proof

Choose a finite stratification of $X_{\mathrm{red}}$ by smooth
locally closed subschemes $s:S\hookrightarrow X$ on which the
cohomology of $K$ is finite locally constant. Such a stratification
exists by constructibility, Noetherian induction, and the fact that a
reduced scheme over the perfect field $k$ has a dense smooth open in
each irreducible component. Nilpotent thickenings leave the etale site
unchanged. The finite-Tor restriction $P=s^*K$ is site-perfect:
successive local finite-free presentations give a bounded-above free
resolution, and truncation below the Tor bound leaves a finitely
presented flat last syzygy. This is the sheaf-local argument of
[lem-weil-bounded-finite-tor-perfect], with the notion of
[def-weil-site-perfect-complex]; it does not claim that each
cohomology module separately has finite projective dimension.

The open–closed triangles of
[def-weil-open-closed-recollement] build $K$, by finitely many
cones, from the objects $Rs_!P$. Ambient tensor adjunction gives

$$
D_XRs_!P\cong
Rs_*R\mathcal Hom_A(P,Rs^{\times}\omega_X)
=Rs_*D_SP.
$$

This is [lem-weil-stratum-ambient-hom] for the locally closed
immersion, using composition of right adjoints. It is an ambient
identity, so it assumes no constructible preservation by $D_X$.
On a stratum of dimension $r$, the ambient smooth theorem
[thm-asd-smooth-tensor] makes $\omega_S$ an invertible sheaf
shifted by $[2r]$. Thus $D_SP=P^\vee\otimes\omega_S$ is
a site-perfect complex of Tor amplitude
$[-b-2r,-a-2r]$. The direct-image
theorem [thm-sf-direct-image-tor-amplitude], with the uniform
vanishing bound of [lem-sf-etale-direct-image-vanishing], makes
$Rs_*D_SP$ bounded constructible of Tor amplitude
$[-b-2r,-a]$, contained in $[-b-2d,-a]$.
The localization triangles assemble these pieces by extensions;
tensoring such a triangle with any module sheaf preserves the common
vanishing interval. Exactness of internal Hom in its first variable
therefore gives the stated bound for $D_XK$. Taking $K=A_X$ also proves that
$\omega_X$ is bounded constructible of finite Tor amplitude.
