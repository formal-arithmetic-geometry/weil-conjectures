+++
id = "def-weil-frobenius-module-weights"
kind = "definition"
title = "Weights of finite-dimensional Frobenius modules"
order = 2651
uses = ["def-weil-finite-field-fiber"]
+++
Fix a prime $p$, an integer $a\in\mathbf Z_{\geq1}$, and let $q=p^a$ be the
fixed prime power. Fix a prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$,
choose an algebraic closure $\Qlb$ of $\Ql$, and fix an isomorphism
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$. For a finite-dimensional
$\Qlb$-vector space $V$, an automorphism $F$, and $w\in\mathbf R$, call
$(V,F)$ $\iota$-pure of weight $w$ if every eigenvalue $\alpha$ of $F$
satisfies $|\iota(\alpha)|=q^{w/2}$. Call $(V,F)$ $\iota$-mixed of weights at
most $w$ if there are an integer $m\geq0$, an $F$-stable filtration

$$
 0=V_0\subset V_1\subset\cdots\subset V_m=V
$$

and real numbers $w_1,\ldots,w_m\leq w$ such that each $(V_r/V_{r-1},F)$ is
$\iota$-pure of weight $w_r$.
