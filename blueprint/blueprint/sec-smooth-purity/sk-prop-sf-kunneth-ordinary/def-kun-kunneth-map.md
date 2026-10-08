+++
id = "def-kun-kunneth-map"
kind = "definition"
title = "The Kunneth map"
order = 1740
uses = ["def-kun-derived-tensor", "def-weil-pbc-cartesian-square", "def-weil-pbc-inverse-image", "lem-kun-inverse-image-monoidal", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Consider a
cartesian square in the
category of schemes

$$
\begin{array}{ccc}
X\times_SY&\xrightarrow{\;q\;}&Y\\
\Big\downarrow{\scriptstyle p}&&\Big\downarrow{\scriptstyle g}\\
X&\xrightarrow{\;f\;}&S
\end{array}
$$

and set $c=f\circ p=g\circ q$. Let $\Lambda$ be a commutative ring
and let $E\in D(X_{\Et},\Lambda)$, $K\in D(Y_{\Et},\Lambda)$; here
derived direct images are computed by the K-injective resolutions of
[prop-weil-pbc-kinjective-resolutions-exist], so they are defined
on the unbounded derived categories. The *Kunneth map* (or
*external product*) is the morphism

$$
\kappa_{E,K}:\quad
Rf_*E\kunotimes{\Lambda}Rg_*K\longrightarrow
Rc_*\bigl(p^{-1}E\kunotimes{\Lambda}q^{-1}K\bigr)
$$

in $D(S_{\Et},\Lambda)$ which is adjoint (under the adjunction
$c^{-1}\dashv Rc_*$ of [def-weil-pbc-inverse-image]) to the
composite

$$
c^{-1}\bigl(Rf_*E\kunotimes{\Lambda}Rg_*K\bigr)
\;\cong\;
p^{-1}f^{-1}Rf_*E\kunotimes{\Lambda}q^{-1}g^{-1}Rg_*K
\xrightarrow{\ \varepsilon_f\otimes\varepsilon_g\ }
p^{-1}E\kunotimes{\Lambda}q^{-1}K,
$$

where the first isomorphism is the monoidality isomorphism of
[lem-kun-inverse-image-monoidal] for the inverse image functors
together with the canonical identifications
$c^{-1}\cong p^{-1}f^{-1}$ and $c^{-1}\cong q^{-1}g^{-1}$, and
$\varepsilon_f$, $\varepsilon_g$ are the derived counits of
[def-weil-pbc-inverse-image].
