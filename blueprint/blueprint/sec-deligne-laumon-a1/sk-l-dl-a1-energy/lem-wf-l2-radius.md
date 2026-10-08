+++
id = "lem-wf-l2-radius"
kind = "lemma"
title = "Radius of the $L^2$-series"
order = 2759
uses = ["def-wf-l2-norm", "def-wf-l2-series"]
+++
In the setting of [def-wf-l2-norm], [def-wf-l2-series], the radius of
convergence $r_{\mathcal F}$ of the power series
$\varphi_{\mathcal F}$ satisfies

$$
r_{\mathcal F}=q^{-\|\mathcal F\|-1},
\qquad\text{equivalently}\qquad
\|\mathcal F\|=-1-\log_q(r_{\mathcal F}).
$$

## Proof

Write $b_m=\|f_{\mathcal F}\|_m^2\geq0$ for the coefficients of the
series of [def-wf-l2-series]. By the root test its radius of
convergence is $r_{\mathcal F}=1/\limsup_mb_m^{1/m}$, while

$$
\|\mathcal F\|=\sup\bigl\{\beta\in\mathbf R:
\limsup_m b_mq^{-m(\beta+1)}>0\bigr\}
$$

by [def-wf-l2-norm]. Put $L=\limsup_mb_m^{1/m}$, so that
$r_{\mathcal F}=1/L$ in $\mathbf R_{>0}\cup\{+\infty\}$. If $L=0$,
then every $b_m$ vanishes, the radius is $+\infty$ and the defining
set of $\beta$'s is empty, so
$\|\mathcal F\|=-\infty=-1-\log_q(r_{\mathcal F})$. Assume therefore
$L>0$, and let $\beta\in\mathbf R$. If
$\beta<-1-\log_qL$, then $L>q^{\beta+1}$ and along a subsequence
$b_m^{1/m}/q^{\beta+1}$ tends to a limit strictly larger than $1$, so
the terms $(b_mq^{-m(\beta+1)})_m$ are unbounded and the defining
$\limsup$ is positive. If $\beta>-1-\log_qL$, then
$L<q^{\beta+1}$ and all but finitely many terms satisfy
$b_m^{1/m}/q^{\beta+1}<\rho$ for a fixed $\rho<1$, so the defining
$\limsup$ is $0$. Hence the supremum is attained exactly at
$\beta=-1-\log_qL=-1-\log_q(1/r_{\mathcal F})$, which is the assertion.
