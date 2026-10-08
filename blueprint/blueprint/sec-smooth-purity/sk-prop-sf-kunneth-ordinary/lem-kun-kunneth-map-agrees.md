+++
id = "lem-kun-kunneth-map-agrees"
kind = "lemma"
title = "Compatibility of the Kunneth map with Leray, proper base change and the projection formula"
order = 1743
uses = ["def-kun-derived-tensor", "def-kun-kunneth-map", "def-kun-unbounded-exchange", "def-weil-pbc-inverse-image", "lem-kun-0f0c", "lem-kun-0f0e", "lem-kun-0f0f", "lem-kun-0f0g", "lem-kun-0f10", "lem-kun-0f12", "lem-kun-inverse-image-monoidal", "lem-kun-leray-bdd", "lem-kun-leray-unbdd", "lem-kun-pullback-constant", "lem-kun-tensor-sym", "lem-kun-tensor-unit", "lem-kun-unbounded-exchange-natural", "lem-weil-pbc-exchange-identity-pasting", "thm-weil-pbc-bounded-below"]
+++
Let $k$ be a separably closed field, $X$ a proper scheme over
$k$ and $Y$ a scheme over $k$. Denote $f:X\to\Spec(k)$,
$g:Y\to\Spec(k)$ and $c=f\circ\operatorname{pr}_1=g\circ \operatorname{pr}_2$ on $X\times_kY$.

1. **(a)** Let $E\in\Dplus(X_{\Et})$ have torsion cohomology and
$K\in\Dplus(Y_{\Et})$. Let $\theta$ be the composite
$$
\begin{aligned}
&\RGamma\bigl((X\times_kY)_{\Et},
\pr_1^{-1}E\kunotimes{\mathbf Z}\pr_2^{-1}K\bigr)\\
&\quad\xrightarrow[\Cref{lem-kun-leray-bdd}]{\ \sim\ }
\RGamma\bigl(Y_{\Et},R\operatorname{pr}_{2,*}
(\pr_1^{-1}E\kunotimes{\mathbf Z}\pr_2^{-1}K)\bigr)\\
&\quad\xrightarrow[\Cref{lem-kun-0f0f}]{\ \sim\ }
\RGamma\bigl(Y_{\Et},R\operatorname{pr}_{2,*}\pr_1^{-1}E
\kunotimes{\mathbf Z}K\bigr)\\
&\quad\xrightarrow[\Cref{thm-weil-pbc-bounded-below}]{\ \sim\ }
\RGamma\bigl(Y_{\Et},\underline{\RGamma(X_{\Et},E)}
\kunotimes{\mathbf Z}K\bigr)\\
&\quad\xrightarrow[\Cref{lem-kun-0f0e}]{\ \sim\ }
\RGamma(Y_{\Et},K)\kunotimes{\mathbf Z}\RGamma(X_{\Et},E)\\
&\quad\xrightarrow[\Cref{lem-kun-tensor-sym}]{\ \sim\ }
\RGamma(X_{\Et},E)\kunotimes{\mathbf Z}\RGamma(Y_{\Et},K).
\end{aligned}
$$
Then $\theta\circ\kappa_{E,K}=\mathrm{id}$, where $\kappa_{E,K}$
is the Kunneth map of [def-kun-kunneth-map]; in particular
$\kappa_{E,K}$ is an isomorphism.
1. **(b)** Let $n\ge1$ be invertible in $k$, let $Y$ be of
finite type over $k$, let $E\in D(X_{\Et},\kunZn)$ and
$K\in D(Y_{\Et},\kunZn)$, and let $\theta$ be the same composite
with $\kunotimes{\kunZn}$-products, where the first arrow uses
[lem-kun-leray-unbdd] and [lem-kun-0f10], the second
[lem-kun-0f0g], the third [lem-kun-0f0c], the fourth
[lem-kun-0f12], and the fifth [lem-kun-tensor-sym]. Then
$\theta\circ\kappa_{E,K}=\mathrm{id}$ and $\kappa_{E,K}$ is an
isomorphism.

## Proof

We verify (a); the proof of (b) is identical, replacing
[lem-kun-0f0f] by [lem-kun-0f0g], [thm-weil-pbc-bounded-below]
by [lem-kun-0f0c], [lem-kun-0f0e] by
[lem-kun-0f12] and [lem-kun-leray-bdd] by
[lem-kun-leray-unbdd]. It suffices to compare adjoints under
$c^{-1}\dashv Rc_*$ (writing $c:X\times_kY\to\Spec(k)$). By
[def-kun-kunneth-map] the adjoint of $\kappa_{E,K}$ is
$(\varepsilon_f\otimes\varepsilon_g)\circ\mathrm{mon}$. Each arrow
in the definition of $\theta$ is the mate of an identification
built from the adjunction data of
[def-weil-pbc-inverse-image] and of
[def-kun-derived-tensor]: the first is the comparison
$\RGamma\circ R\operatorname{pr}_{2,*}\cong\RGamma$ (an instance of
the Leray composition [lem-kun-leray-bdd]); the second is the
projection formula map of [lem-kun-0f0f], which is by
definition the mate of the unit–monoidality composite of
[lem-kun-inverse-image-monoidal]; the third is
the inverse of the proper base change map of
[thm-weil-pbc-bounded-below], itself the mate of
$\varepsilon_f$ by [def-kun-unbounded-exchange]; the fourth is
the map of [lem-kun-0f0e], whose mate is
$\mathrm{id}\otimes\eta_g$ for the unit $\eta_g$ of
[def-weil-pbc-inverse-image] (using
[lem-kun-tensor-unit] and [lem-kun-pullback-constant] for
the constant objects); the fifth is the symmetry
[lem-kun-tensor-sym], whose mate is again the symmetry.
Applying $c^{-1}$ to $\theta\circ\kappa_{E,K}$ therefore yields the
composite of the corresponding mates, and an elementary cancellation
of each unit against the adjacent counit – all compatibilities being
instances of the pasting law
[lem-weil-pbc-exchange-identity-pasting] and of the naturality of
[lem-kun-unbounded-exchange-natural] – leaves exactly
$(\varepsilon_f\otimes\varepsilon_g)\circ\mathrm{mon}$, the adjoint
of $\mathrm{id}$. Since the adjunction bijection is injective,
$\theta\circ\kappa_{E,K}=\mathrm{id}$, and as $\theta$ is an
isomorphism so is $\kappa_{E,K}$.
