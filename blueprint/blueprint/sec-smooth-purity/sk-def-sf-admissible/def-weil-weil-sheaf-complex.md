+++
id = "def-weil-weil-sheaf-complex"
kind = "definition"
title = "Weil sheaf and Weil complex"
order = 1507
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-constructible-heart", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-finite-torsion-constructibility", "def-weil-frobenius-detailed", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Fix the finite-field datum [def-weil-finite-field-fiber] $p,a,q,k_0,k$, where
$q=p^a$, and a prime $\ell\neq p$. Write $\Ql=\mathbf Q_\ell$, choose an
algebraic closure $\Qlb$ of $\Ql$, and choose a finite extension $E/\Ql$
contained in $\Qlb$. Let $Y_0$ be a finite-type
[def-weil-scheme-morphism-properties] $k_0$-scheme, put
$Y=Y_0\times_{k_0}k$, and let $g_Y:Y\to Y$ be the geometric-Frobenius
automorphism from the geometric Frobenius convention
[def-weil-frobenius-detailed]. The category $\Sh_c(Y,E)$ is the
constructible heart [def-weil-constructible-heart]. On the small pro-etale
site [def-weil-pbc-proetale-site], its underlying constructibility
uses the finite-torsion constructibility convention
[def-weil-finite-torsion-constructibility]; a constructible $E$-Weil sheaf is
an object $\mathcal F\in\Sh_c(Y,E)$ together with an isomorphism formed using
the derived pullback [def-weil-derived-pullback-tensor-hom]

$$
 \theta:Lg_Y^*\mathcal F\xrightarrow{\sim}\mathcal F.
$$

Morphisms commute with $\theta$, and $D^b_{c,\mathrm W}(Y,E)$ is the
localization of bounded complexes of such sheaves at equivariant
quasi-isomorphisms; it is an ordinary triangulated category. Let $\mathcal
E_\ell$ be the directed set of finite extensions of $\Ql$ contained in
$\Qlb$. Define

$$
 D^b_{c,\mathrm W}(Y,\Qlb)=
 \underset{E\in\mathcal E_\ell}{\operatorname{2-colim}}
 D^b_{c,\mathrm W}(Y,E)
$$

with the common-stage coefficient construction
[def-weil-algebraically-closed-coefficients]. For each
$\Lambda\in\{E,\Qlb\}$ there is an exact forgetful functor

$$
 \operatorname{For}:D^b_{c,\mathrm W}(Y,\Lambda)
 \longrightarrow D^b_c(Y,\Lambda).
$$

An object $K$ carries, in addition to $\operatorname{For}(K)$, the derived
Frobenius isomorphism

$$
 \theta_K:Lg_Y^*\operatorname{For}(K)
 \xrightarrow{\sim}\operatorname{For}(K),
$$

represented termwise at a finite coefficient stage.
