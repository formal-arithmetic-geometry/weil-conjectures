+++
id = "lem-trf-frobenius-open-square"
kind = "lemma"
title = "Frobenius preserves an open subscheme defined over the finite field"
order = 2368
uses = ["def-trf-scheme-frobenius", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
Fix the finite-field datum.
Let $j_0:X_0\hookrightarrow Y_0$ be an
open immersion
over $k_0=\mathbf F_q$, and let $j:X\hookrightarrow Y$
be its base change to $k$. For the
scheme and Galois Frobenii,
each square

$$
\begin{array}{ccc}
X&\xrightarrow{h}&X\\
{\scriptstyle j}\downarrow&&\downarrow{\scriptstyle j}\\
Y&\xrightarrow{\bar h}&Y
\end{array}
$$

is Cartesian, where $(h,\bar h)=(\Phi_X^m,\Phi_Y^m)$ or
$(g_X^m,g_Y^m)$, and $m\geq0$. With
$s=\Spec k$, $g_s=\Spec(\gamma)$, and structure maps $a_X,a_Y$,

$$
a_Xg_X^m=g_s^ma_X,\qquad a_Yg_Y^m=g_s^ma_Y.
$$

In particular these Galois maps are not asserted to be $k$-morphisms.

## Proof

The absolute $q^m$-power map on a characteristic-$p$ ring sends
each prime ideal to itself. Hence the scheme Frobenius of $Y_0$
has inverse image $X_0$ on the underlying open subset, and its
restriction is the Frobenius of $X_0$. For open immersions,
pullback is exactly the inverse-image open with the restricted
structure sheaf ([def-weil-scheme-morphism-properties]).
Thus the open square over $k_0$ is Cartesian. Base changing gives
the scheme-Frobenius square in the statement, with the definitions
of [def-trf-scheme-frobenius].

The maps $g_Y^m=\operatorname{id}_{Y_0}\times\Spec(\gamma^m)$
preserve $X_0\times_{k_0}k$; their restrictions there are $g_X^m$.
They are isomorphisms, so the same inverse-image description of
opens gives the second Cartesian square. Finally, the structure
map of the geometric fiber of [def-weil-finite-field-fiber]
is the second projection. Composing it with the displayed product
automorphism gives $\Spec(\gamma^m)a_Y$, and the same computation
applies to $X$. This proves the two asserted equalities.
