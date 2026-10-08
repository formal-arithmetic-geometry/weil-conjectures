+++
id = "def-weil-complex-weights"
kind = "definition"
title = "Weights of a Weil complex"
order = 2787
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-punctual-weights", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex"]
+++
Fix a prime $p$, an integer $a\in\mathbf Z_{\geq1}$, put $q=p^a$, $k_0=\Fq$,
and let $k=\Fbar$ be the fixed algebraic closure of $k_0$. Fix a prime
$\ell\neq p$, write $\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$
of $\Ql$, a separated finite-type $k_0$-scheme $Y_0$, and
$Y=Y_0\times_{k_0}k$. Put

$$
 g_Y=\operatorname{id}_{Y_0}\times\operatorname{Spec}(\operatorname{Frob}_q):
 Y\longrightarrow Y
$$

for the geometric-Frobenius automorphism [def-weil-frobenius-detailed]. Fix
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$, $w\in\mathbf R$, and let $K\in
D^b_{c,\mathrm W}(Y,\Qlb)$ be a Weil complex. Let $a_Y:Y\to\Spec k$ be the structure morphism, with $Ra_Y^!$ its
constructible exceptional inverse image [def-weil-exceptional-inverse-image]
at $\Qlb$ (defined for every separated finite-type morphism; no admissibility
hypothesis in the ambient sense of
[def-weil-exceptional-adjoint-admissibility] is imposed). Choose a
dualizing Weil complex $(\omega_Y,\theta_{\omega_Y})$ and require

$$
 \operatorname{For}(\omega_Y)=Ra_Y^!\Qlb,
$$

where $Ra_Y^!$ denotes the exceptional inverse image for the structure
morphism. Require
$\theta_{\omega_Y}:Lg_Y^*\operatorname{For}(\omega_Y)
\xrightarrow{\sim}\operatorname{For}(\omega_Y)$ to be the canonical
functorial Weil lift induced by geometric-Frobenius base change and the
adjunction units and counits, rather than an arbitrary Weil lift. The
internal derived Hom is the derived pullback/tensor/Hom operation. Define
$D_YK$ to be the Weil complex whose underlying complex is

$$
 \operatorname{For}(D_YK)=
 R\mathcal Hom_{\Qlb}\bigl(\operatorname{For}(K),\operatorname{For}(\omega_Y)\bigr),
$$

with the Weil structure induced by $\theta_K$ and $\theta_{\omega_Y}$. For
every $j\in\mathbf Z$, the cohomology sheaf $\mathcal
H^j(\operatorname{For}K)$ is assigned the punctual-weight notion
[def-weil-punctual-weights]. Define

$$
 \Wt_{\iota,\leq w}(K)
 \Longleftrightarrow
 \bigl(\mathcal H^j(\operatorname{For}K)
 \text{ is \(\iota\)-mixed of weights at most \(w+j\) for every }
 j\in\mathbf Z\bigr),
$$

$$
 \Wt_{\iota,\geq w}(K)\Longleftrightarrow
 \Wt_{\iota,\leq-w}(D_YK).
$$

The complex $K$ is $\iota$-pure of weight $w$ if both predicates hold.
