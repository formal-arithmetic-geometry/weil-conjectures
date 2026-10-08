+++
id = "lem-pc-zero-scheme-properties"
kind = "lemma"
title = "Properties of the zero scheme"
order = 826
uses = ["def-pc-base-change", "def-pc-scheme", "def-sc-invertible-module", "lem-pc-divisor-line-bundle-properties", "lem-pc-tensor-dual-invertible"]
lean = ["AlgebraicGeometry.exists_isEffectiveCartierCenter_hilbertPresheaf"]
+++
Let $X$ be a scheme, $\mathcal{M}$ a
invertible $\mathcal{O}_X$-module and
$s\in H^0(X,\mathcal{M})$.

1. $Z(s)$ is a closed subscheme of $X$ (a locally principal closed
subscheme), and affine-locally, for $U=\operatorname{Spec}(A)$ with $\mathcal{M}$ free on
$e$ and $s|_U=a\cdot e$, $Z(s)\cap U=\operatorname{Spec}(A/(a))$.
1. For a flat morphism $g:Y\to X$ with
$s_Y=g^*s\in H^0(Y,g^*\mathcal{M})$: $Z(s_Y)=Z(s)\times_XY$, i.e. $g^*\mathcal{I}_{Z(s)}=\mathcal{I}_{Z(s_Y)}$.
1. $Z(s)=X$ if and only if $s=0$.

## Proof

(1) $\mathcal{I}_{Z(s)}=\operatorname{im}(s^\vee)$ is a quasi-coherent
$\mathcal{O}_X$-module (an image of a quasi-coherent module in a
quasi-coherent module is quasi-coherent) and an ideal sheaf (the image
of $\mathcal{M}^\vee\to\mathcal{O}_X$ is a submodule of $\mathcal{O}_X$), so it defines a closed
subscheme. Locally: $\mathcal{M}|_U=\mathcal{O}_U\cdot e$, $s^\vee$ sends the dual
basis $e^\vee$ to $a$; hence the image is $a\cdot\mathcal{O}_U$ and
$Z(s)\cap U=\operatorname{Spec}(A/(a))$.

(2) $g^*$ is right exact, so
$g^*\mathcal{I}_{Z(s)}=g^*\operatorname{im}(s^\vee)=\operatorname{im}(g^*(s^\vee)) =\operatorname{im}((g^*s)^\vee)=\mathcal{I}_{Z(s_Y)}$, where
$g^*(s^\vee)=(g^*s)^\vee$ is the canonical identification of the pullback
of the dual with the dual of the pullback (valid for $\mathcal{M}$ invertible,
see the local check in [lem-pc-divisor-line-bundle-properties]).

(3) If $s=0$, then $s^\vee=0$ and $\mathcal{I}_{Z(s)}=0$, so $Z(s)=X$. If
$s\neq0$, choose $x\in X$ with $s_x\neq0$ in $\mathcal{M}_x\cong\mathcal{O}_x$ after a
trivialization; then $s_x$ is a unit of $\mathcal{O}_x$ and
$(\mathcal{I}_{Z(s)})_x=\mathcal{O}_x$, so $x otin Z(s)$. (Contrapositive: if
$Z(s)=X$, then $\mathcal{I}=0$, $s^\vee=0$, and $s=0$ because the canonical map
$\mathcal{M}\to\mathcal{M}^{\vee\vee}$ is an isomorphism
([lem-pc-tensor-dual-invertible]) and its
composition with $s^{\vee\vee}$ is the original $s$.)
