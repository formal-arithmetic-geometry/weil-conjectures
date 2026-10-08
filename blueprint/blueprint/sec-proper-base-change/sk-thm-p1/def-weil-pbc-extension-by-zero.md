+++
id = "def-weil-pbc-extension-by-zero"
kind = "definition"
title = "Extension by zero for open immersions"
order = 1173
uses = ["def-cbc-open-immersion-square", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions"]
+++
For an open immersion $j:U\hookrightarrow X$, extension by zero is the exact
functor

$$
 j_!:\Ab(U_{\Et})\longrightarrow\Ab(X_{\Et})
$$

left adjoint to $j^{-1}$. It is characterized on geometric stalks by

$$
 (j_!F)_{\bar x}=
 \begin{cases}
 F_{\bar x},&\bar x\text{ lies in }U,\\
 0,&\bar x\text{ lies in }X\setminus U.
 \end{cases}
$$

## Detailed form

For an open immersion
$j:U\hookrightarrow X$, *extension by zero* is the

$$
j_!:\Ab(U_{\Et})\longrightarrow\Ab(X_{\Et})
$$

of [def-weil-pbc-extension-by-zero]: the exact functor left
adjoint to $j^{-1}$, acting by

$$
(j_!F)_{\bar x}=
\begin{cases}
F_{\bar x_U},&\bar x\text{ lies in }U,\\
0,&\bar x\text{ lies in }X\setminus U,
\end{cases}
$$

on geometric stalks, and
exact, hence acting degreewise on complexes. For a finite
commutative ring $\Lambda$ the same construction is used for sheaves
of $\Lambda$-modules.
