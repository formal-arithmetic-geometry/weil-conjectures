+++
id = "lem-weil-local-frobenius-conjugacy-class"
kind = "lemma"
title = "Independence of the local Frobenius operator from the embedding"
order = 2429
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-frobenius-detailed", "def-weil-local-frobenius-trace", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex"]
+++
Fix the finite-field datum $p,a,q,k_0,k$, a prime $\ell\neq p$, a finite
extension $E/\Ql$, a finite-type $k_0$-scheme $Y_0$ with
$Y=Y_0\times_{k_0}k$, a Weil complex $K\in D^b_{c,\mathrm W}(Y,E)$, a closed
point $y\in|Y_0|$ of degree $r=[\kappa(y):\Fq]$, and an integer $j\in\mathbf
Z$. For two embeddings $\kappa(y)\hookrightarrow k$ with associated geometric
points $\bar y,\bar y'\to Y$, the local operators $F_y$ and $F'_y$ on the
stalks of the cohomology sheaf $\mathcal H^j(\operatorname{For}K)$
constructed in [def-weil-local-frobenius-trace] are conjugate: there is an
isomorphism $\mathcal H^j(\operatorname{For}K)_{\bar y}\cong \mathcal
H^j(\operatorname{For}K)_{\bar y'}$ carrying $F_y$ to $F'_y$.

## Proof

Two embeddings $\kappa(y)\hookrightarrow k$ differ by an element of
$\operatorname{Gal}(k/k_0)$, because $k$ is the fixed algebraic closure of the
finite field $k_0$ and $\kappa(y)$ is a finite field; the associated
geometric points $\bar y$ and $\bar y'$ of $Y$ are therefore related by a
power of the geometric-Frobenius automorphism $g_Y$ of
[def-weil-frobenius-detailed]. That automorphism induces an isomorphism between the
stalks of the cohomology sheaf $\mathcal H^j(\operatorname{For}K)$ at the two
points, and the Weil isomorphism is an isomorphism
$Lg_Y^*\operatorname{For}(K)\xrightarrow{\sim}\operatorname{For}(K)$, which
intertwines the local operator built at $\bar y$ with the one built at its
translate. Iterating this and using the $r$-fold return prescribed in
[def-weil-local-frobenius-trace] transports $F_y$ to $F'_y$, which is the
conjugacy asserted.
