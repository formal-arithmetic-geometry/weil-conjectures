+++
id = "lem-wf-affine-constructible-open"
kind = "lemma"
title = "Chevalley constructibility and open pieces of constructible sets"
order = 2486
uses = ["lem-wf-affine-noetherian-components"]
+++
Let $k$ be a field.

1. (Chevalley.) If $f:X\to Y$ is a morphism of affine schemes of
   finite type over $k$, then the image of every constructible subset of
   $X$ is a constructible subset of $Y$. In particular $f(X)$ is
   constructible.
2. If $S$ is a nonempty constructible subset of an affine scheme $Y$ of
   finite type over $k$, then $S$ contains a nonempty open subset of its
   closure $\overline S$. In particular, a dense constructible subset of
   $Y$ contains a nonempty open subset of $Y$.

## Proof

(1) The coordinate map $k[Y]\to k[X]$ is of finite type, hence of
finite presentation because $k[Y]$ is Noetherian
([lem-wf-affine-noetherian-components]). Chevalley's theorem says that
for a ring map of finite presentation the induced map on spectra sends
constructible subsets to constructible subsets (in Mathlib:
`PrimeSpectrum.isConstructible_comap_image`). On the Noetherian space
$Y$, constructible in this sense is the same as a finite union of
intersections of an open and a closed subset.

(2) Write $S=\bigcup_{i=1}^rS_i$ with $S_i=U_i\cap F_i$, $U_i$ open and
$F_i$ closed, all $S_i$ nonempty. Put $Z=\overline S$; then
$Z=\bigcup_i\overline{S_i}$. The space $Z$ is a closed subset of $Y$,
hence has finitely many irreducible components
([lem-wf-affine-noetherian-components], applied to
$\operatorname{Spec}$ of the corresponding quotient of $k[Y]$), and it
is nonempty. Choose one, $C$. Since $C=\bigcup_i(C\cap\overline{S_i})$
is irreducible, $C\subseteq\overline{S_i}$ for some $i$. Let $\Omega$ be
the complement in $Z$ of the union of the other irreducible components.
It is open in $Z$, contained in $C$, and nonempty because $C$ is not
contained in the union of finitely many other components (it would lie
in one of them, contradicting maximality). So $\Omega$ is a nonempty
open subset of $Z$ with $\Omega\subseteq\overline{S_i}$; in particular
it is open in $\overline{S_i}$ and therefore meets the dense subset
$S_i$ of $\overline{S_i}$.

As $\overline{S_i}\subseteq F_i$, we have
$S_i=U_i\cap\overline{S_i}$, so
$S_i\cap\Omega=U_i\cap\Omega$, which is open in $Z$. It is nonempty by
the previous paragraph and contained in $S$. This is the required
nonempty open subset of $\overline S$. When $S$ is dense, $\overline
S=Y$.
