+++
id = "lem-per-smooth-pullback-t-exact"
kind = "lemma"
title = "Smooth pullback is perverse up to the shift"
order = 2742
uses = ["cor-pur-adic-and-rational-smooth-dualizing-complexes", "cor-sf-duality-pullback", "def-per-perverse-subcategories", "def-per-support-condition", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions", "fix-cor-verdier-exchange", "lem-per-lisse-tensor-permanence", "prop-functor-package"]
+++
Let $f:X\to Y$ be a smooth
morphism of constant relative dimension $d$ between separated schemes
of finite type over a field $k$. On the constructible
$\overline{\mathbf Q}_\ell$-coefficient categories of
[def-weil-pbc-qbar-category], the functor $Lf^*[d]$ is exact for
the candidate subcategories of [def-per-perverse-subcategories]:

$$
Lf^*[d]\bigl({}^pD^{\le0}(Y)\bigr)\subset{}^pD^{\le0}(X),\qquad
Lf^*[d]\bigl({}^pD^{\ge0}(Y)\bigr)\subset{}^pD^{\ge0}(X).
$$

## Proof

For the $\le$-direction: $Lf^*$ is exact (the cohomology sheaves
of $Lf^*K$ are the pullbacks of those of $K$) and the geometric
fibers of $f$ have dimension $d$, so the support of
$\mathcal H^{-i}(Lf^*K[d])$ has dimension at most the dimension of
the support of $\mathcal H^{-i+d}(K)$ plus $d$ (the pullback of a
constructible sheaf has support the preimage, of dimension raised by
the fibre dimension $d$, and the shift of the cohomology index is
$H^n(C[d])=H^{n+d}(C)$); hence

$$
\dim\operatorname{Supp}\mathcal H^{-i}\bigl(Lf^*K[d]\bigr)
\le\dim\operatorname{Supp}\mathcal H^{-i+d}(K)+d,
$$

and the support inequality for $K$ (applied to the index
$i-d$) gives
$\dim\operatorname{Supp}\mathcal H^{-i+d}(K)\le i-d$, so the
right-hand side is $\le i$, which is the support inequality
for $Lf^*K[d]$: $\operatorname{SuppCon}(Lf^*K[d])$.
For the $\ge$-direction: the cosupport condition of $K$, namely
$\operatorname{SuppCon}(D_YK)$, is transported along the smooth
morphism as follows. By the Verdier exchange of
[fix-cor-verdier-exchange] applied to the smooth morphism $f$
(the identity $D_XLf^*M\cong Rf^!D_YM$ obtained from the exchange
for $f$ and biduality, which is the duality against pullback of
[cor-sf-duality-pullback]) and by the smooth
identity $Rf^!M\cong Lf^*M(d)[2d]$ (the smooth-purity form of the
dualizing complexes of the smooth morphism,
[cor-pur-adic-and-rational-smooth-dualizing-complexes] and [prop-functor-package]),

$$
D_X\bigl(Lf^*[d]K\bigr)
\cong Lf^*\bigl(D_YK\bigr)(d)[d].
$$

The twist $(d)$ is lisse of rank one, hence support-preserving
([lem-per-lisse-tensor-permanence]); the shift by $[d]$ moves
the cohomology index by $d$, i.e. $H^{-i}(Lf^*(D_YK)(d)[d])=H^{-i+d}(Lf^*(D_YK)(d))$, with the same
dimension bookkeeping as in the $\le$-direction; the support
inequality for $D_YK$ therefore implies the one for
$Lf^*D_YK(d)[d]$, i.e. $\operatorname{SuppCon}\bigl(D_X(Lf^*[d]K)\bigr)$, and the
$\ge$-inclusion follows from [def-per-support-condition].
