+++
id = "def-trf-weil-extension-zero"
kind = "definition"
title = "Weil extension by zero"
order = 2369
uses = ["def-trf-strict-weil-complex", "def-weil-extension-by-zero", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties", "lem-trf-frobenius-open-square", "lem-trf-open-square-exchange"]
+++
Let $j_0:X_0\hookrightarrow Y_0$ be an
open immersion of
separated finite-type schemes over the
finite field $k_0$, with
base change $j:X\hookrightarrow Y$. For a
strict Weil complex
$(K,\varphi)$ on $X$, set

$$
\bar K=j_!K,\qquad
\bar\varphi:
Lg_Y^*j_!K\xrightarrow{b_{g_Y}}
j_!Lg_X^*K\xrightarrow{j_!\varphi}j_!K.
$$

Here $j_!$ is extension by
zero ([def-weil-extension-by-zero]), and $b_{g_Y}$ is the comparison
isomorphism of [lem-trf-open-square-exchange] for the Cartesian square
of [lem-trf-frobenius-open-square].
