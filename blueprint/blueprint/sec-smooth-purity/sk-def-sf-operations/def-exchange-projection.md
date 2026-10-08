+++
id = "def-exchange-projection"
kind = "definition"
title = "Exchange and projection transformations"
order = 1487
uses = ["def-compact-support-direct-image-detailed", "def-weil-compactifications-refinements", "def-weil-constructible-intervals", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-extension-by-zero", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-scheme-morphism-properties", "prop-compactification-coherence-detailed"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$. Let $S$ be a scheme on which $\ell$ is
invertible, let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $S$-schemes, and let every morphism
below be an $S$-morphism. Let $\Lambda\in\{A,\mathcal O_E,E,\Qlb\}$, where
the finite-level coefficient category is the finite-torsion constructible
category [def-weil-finite-torsion-constructibility]; the latter coefficient
categories are obtained by derived completion, rationalization, and the
common-stage construction. Use the derived pullback, tensor, and
internal-Hom operations [def-weil-derived-pullback-tensor-hom], the derived
direct image [def-weil-derived-direct-image], and the compact-support direct
image [def-compact-support-direct-image-detailed]. The finite-Tor and
interval conditions are the finite-Tor
[def-weil-finite-tor-amplitude] and constructible-interval
[def-weil-constructible-intervals] conditions. Let $f:X\to Y$ be separated
and of finite type, let $Y'$ be a finite-type $S$-scheme and let $g:Y'\to Y$
be separated and of finite type, and set $X'=X\times_Y Y'$, with projections
$g':X'\to X$ and $f':X'\to Y'$. Consider the resulting Cartesian square

$$
\begin{array}{ccc}
 X' & \xrightarrow{g'} & X\\
 f'\downarrow && \downarrow f\\
 Y' & \xrightarrow{g} & Y
\end{array}
$$

The direct-image exchange transformation

$$
 \operatorname{Ex}_*:\;Lg^*Rf_*\longrightarrow Rf'_*Lg'^*
$$

is adjoint to the composite

$$
 Lf'^*Lg^*Rf_*\xrightarrow{\sim}Lg'^*Lf^*Rf_*
 \longrightarrow Lg'^*,
$$

whose second arrow is the counit of $Lf^*\dashv Rf_*$. If $f=\bar f\circ j$
is a compactification [def-weil-compactifications-refinements], the
compact-support exchange map

$$
 \operatorname{Ex}_!:\;Lg^*Rf_!\longrightarrow Rf'_!Lg'^*
$$

is represented by $\operatorname{Ex}_*$ for $\bar f$, followed by the
canonical identification $L\bar g'^*j_!\cong j'_!Lg'^*$, where $\bar f':\bar
X'\to Y'$ and $\bar g':\bar X'\to\bar X$ are the base changes of $\bar f$,
and $j':X'\hookrightarrow\bar X'$ is the base change of $j$; the independence
of this map from the compactification is the compactification-coherence
proposition.

For $K\in D^b_c(X,\Lambda)$ and $L\in D^b_{ctf}(Y,\Lambda)$, the projection
transformation is

$$
 \operatorname{PF}_{f,K,L}:Rf_!K\otimes^L L
 \longrightarrow Rf_!(K\otimes^L Lf^*L).
$$

For this compactification it is the direct-image projection transformation
for $\bar f$, followed by $j_!K\otimes^LL\bar f^*L\cong j_!(K\otimes^LLf^*L)$.
These are natural transformations with the displayed sources and targets.
