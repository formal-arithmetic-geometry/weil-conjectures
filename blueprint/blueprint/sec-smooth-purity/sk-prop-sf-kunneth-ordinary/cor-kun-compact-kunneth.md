+++
id = "cor-kun-compact-kunneth"
kind = "theorem"
title = "Künneth formula for compactly supported cohomology"
order = 1786
tags = ["latex:corollary"]
uses = ["def-compact-support-direct-image-detailed", "def-kun-kunneth-map", "def-weil-extension-by-zero", "thm-kun-0f1p"]
+++
Let $k$ be a separably closed
field, let $X$ and $Y$ be schemes of finite type over $k$, let
$n\ge1$ be an integer invertible in $k$, and let
$E\in D(X_{\Et},\kunZn)$, $K\in D(Y_{\Et},\kunZn)$. Choose
compactifications $j_X:X\hookrightarrow\overline X$ and
$j_Y:Y\hookrightarrow\overline Y$ over $k$, with $\overline X,\overline Y$
proper over $k$, and put
$R\Gamma_c(X_{\Et},E)=R\Gamma(\overline X_{\Et},j_{X,!}E)$ and similarly
for $Y$. Then the composite

$$
\begin{gathered}
R\Gamma_c(X_{\Et},E)\kunotimes{\kunZn}R\Gamma_c(Y_{\Et},K)
\\
\xrightarrow{\ \sim\ }
R\Gamma\bigl((X\times_kY)_{\Et},
\pr_1^{-1}j_{X,!}E\kunotimes{\kunZn}\pr_2^{-1}j_{Y,!}K\bigr)
\\
\xrightarrow{\ \sim\ }
R\Gamma_c\bigl((X\times_kY)_{\Et},
\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K\bigr)
\end{gathered}
$$

of the Künneth map of [thm-kun-0f1p] applied to $j_{X,!}E$ and
$j_{Y,!}K$ with the identification of the second line is an isomorphism;
the second arrow identifies
$\pr_1^{-1}j_{X,!}E\kunotimes{\kunZn}\pr_2^{-1}j_{Y,!}K$ with
$j_{X\times_kY,!}(\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K)$ along the
compactification $j_X\times_kj_Y$.

## Proof

The first arrow is an isomorphism by [thm-kun-0f1p], applied to the
complexes $j_{X,!}E\in D(\overline X_{\Et},\kunZn)$ and
$j_{Y,!}K\in D(\overline Y_{\Et},\kunZn)$ and to the isomorphism
$R\Gamma(\overline X_{\Et},j_{X,!}E)\cong R\Gamma_c(X_{\Et},E)$ which is
the definition of compact support
([def-compact-support-direct-image-detailed]). For the second arrow: the
product of the two open immersions $j_X,j_Y$ is the open immersion
$j_X\times_kj_Y$ of $X\times_kY$ into
$\overline X\times_k\overline Y$, which is proper over $k$ because
properness is stable under products, so
$j_{X\times_kY,!}=j_{X,!}\boxtimes j_{Y,!}$ is the extension by zero along
the compactification, and the identity
$\pr_1^{-1}j_{X,!}E\kunotimes{\kunZn}\pr_2^{-1}j_{Y,!}K\cong (j_X\times_kj_Y)_!(\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K)$ is the compatibility
of the extension by zero with the tensor product and the inverse image
([def-weil-extension-by-zero]). The independence of the two
isomorphisms of the chosen compactifications is the coherence recorded in
[def-compact-support-direct-image-detailed].
