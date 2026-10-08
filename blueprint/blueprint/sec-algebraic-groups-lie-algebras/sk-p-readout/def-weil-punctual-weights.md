+++
id = "def-weil-punctual-weights"
kind = "definition"
title = "Punctual weights"
order = 2554
uses = ["def-weil-constructible-heart", "def-weil-finite-field-fiber", "def-weil-local-frobenius-trace", "def-weil-point-counts-zeta", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex", "lem-weil-local-frobenius-conjugacy-class"]
+++
Fix a prime $p$, an integer $a\in\mathbf Z_{\geq1}$, put $q=p^a$, $k_0=\Fq$,
and let $k=\Fbar$ be the fixed algebraic closure of $k_0$. Fix a prime
$\ell\neq p$, write $\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$
of $\Ql$, and fix an isomorphism $\iota:\Qlb\xrightarrow{\sim}\mathbf C$. Let
$Y_0$ be a finite-type $k_0$-scheme, put $Y=Y_0\times_{k_0}k$, and let
$\mathcal F$ be a constructible $\Qlb$-sheaf in the constructible heart,
carrying the Weil-sheaf structure. For each closed point $y\in|Y_0|$, use the
closed-point notation [def-weil-point-counts-zeta], set $q_y=\#\kappa(y)$,
choose an embedding $\kappa(y)\hookrightarrow k$, and choose a geometric
point $\bar y\to Y$ above $y$ (the eigenvalues of $F_y$ do not depend on these choices, by [lem-weil-local-frobenius-conjugacy-class]). Let $F_y$ be the local geometric-Frobenius
operator [def-weil-local-frobenius-trace] on $\mathcal F_{\bar y}$. For
$w\in\mathbf R$, call $\mathcal F$ punctually $\iota$-pure of weight $w$ if
every eigenvalue $\alpha$ of every $F_y$ satisfies

$$
 |\iota(\alpha)|=q_y^{w/2}.
$$

Call $\mathcal F$ $\iota$-mixed of weights at most $w$ if there are an
integer $m\geq0$, constructible $\Qlb$-Weil subsheaves

$$
 0=\mathcal F_0\subset\mathcal F_1\subset\cdots\subset\mathcal F_m=\mathcal F,
 \qquad w_1,\ldots,w_m\in\mathbf R,\quad w_r\leq w,
$$

such that each quotient $\mathcal F_r/\mathcal F_{r-1}$ is punctually
$\iota$-pure of weight $w_r$.
