+++
id = "lem-kun-kunneth-via-0f1n"
kind = "lemma"
title = "Compatibility of the Kunneth map with the projection-formula variant"
order = 1780
uses = ["def-kun-kunneth-map", "def-kun-separably-closed", "def-kun-unbounded-exchange", "lem-kun-03qu-sep-closed", "lem-kun-0f12", "lem-kun-0f1n", "lem-kun-inverse-image-monoidal", "lem-kun-leray-unbdd"]
+++
Let $k$ be a separably closed
field, $n\ge1$ invertible in $k$, and let $X$
and $Y$ be schemes of finite type over $k$. Let
$E\in D(X_{\Et},\kunZn)$ and $K\in D(Y_{\Et},\kunZn)$. Then
the Kunneth map $\kappa_{E,K}$ of
[def-kun-kunneth-map] for the product square is equal to the
composite

$$
\begin{aligned}
&\RGamma(X_{\Et},E)\kunotimes{\kunZn}\RGamma(Y_{\Et},K)\\
&\quad\xrightarrow[\Cref{lem-kun-0f12}]{\ \sim\ }
\RGamma\bigl(X_{\Et},E\kunotimes{\kunZn}\underline{\RGamma(Y_{\Et},K)}\bigr)\\
&\quad\xrightarrow{\ \RGamma(X_{\Et},\varphi)\ }
\RGamma\bigl((X\times_kY)_{\Et},
\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K\bigr),
\end{aligned}
$$

where $\varphi$ is the map of [lem-kun-0f1n] for the
diagram

$$
\begin{array}{ccccc}
X&\xleftarrow{\;=\;}&X&\xleftarrow{\;\pr_1\;}&X\times_kY\\
\Big\downarrow{}&&\Big\downarrow{}&&\Big\downarrow{\scriptstyle \pr_2}\\
\Spec(k)&\longleftarrow&\Spec(k)&\xleftarrow{\;=\;}&Y
\end{array}
$$

and the last arrow uses the Leray identification of
[lem-kun-leray-unbdd].

## Proof

Denote $a:X\times_kY\to\Spec(k)$, $b:X\to\Spec(k)$ and
$c:Y\to\Spec(k)$. The description of the etale site of a
separably closed point in [lem-kun-03qu-sep-closed] identifies
its sheaves with modules and $Rc_*K$ with $\RGamma(Y_{\Et},K)$.
Put $P=\RGamma(X_{\Et},E)$, $Q=\RGamma(Y_{\Et},K)$, and write
$\varepsilon_b:b^{-1}P\to E$ and
$\varepsilon_c:c^{-1}Q\to K$ for the counits.
By [def-kun-kunneth-map], the adjoint of $\kappa_{E,K}$
under $a^{-1}\dashv Ra_*$ is the tensor product of the pulled-back
counits. We compute the adjoint of the asserted composite.

The projection-formula map of [lem-kun-0f12] is adjoint to

$$
b^{-1}(P\kunotimes{\kunZn}Q)
\cong b^{-1}P\kunotimes{\kunZn}b^{-1}Q
\xrightarrow{\ \varepsilon_b\otimes1\ }
E\kunotimes{\kunZn}b^{-1}Q,
$$

the isomorphism being that of [lem-kun-inverse-image-monoidal].
By its construction from the exchange morphism of
[def-kun-unbounded-exchange], the map $\varphi$ of
[lem-kun-0f1n] is adjoint under
$\pr_1^{-1}\dashv R\pr_{1,*}$ to

$$
\pr_1^{-1}E\kunotimes{\kunZn}a^{-1}Q
\xrightarrow{\ 1\otimes\pr_2^{-1}\varepsilon_c\ }
\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K,
$$

where $a=c\pr_2=b\pr_1$. Composing adjunctions, using the
Leray identification of [lem-kun-leray-unbdd], therefore gives
the adjoint

$$
a^{-1}(P\kunotimes{\kunZn}Q)
\xrightarrow{\ \pr_1^{-1}\varepsilon_b\otimes
\pr_2^{-1}\varepsilon_c\ }
\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K.
$$

This is exactly the defining adjoint of $\kappa_{E,K}$; the
adjunction bijection proves equality of the two maps.
