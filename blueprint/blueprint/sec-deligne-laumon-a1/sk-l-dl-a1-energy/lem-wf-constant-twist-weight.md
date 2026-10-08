+++
id = "lem-wf-constant-twist-weight"
kind = "lemma"
title = "Weight of a constant twist"
order = 2763
uses = ["def-weil-punctual-weights", "def-wf-constant-weil-twist"]
+++
If $\mathcal F$ is lisse and punctually $\iota$-pure of weight
$w$, and $2\log_q|\iota(b)|=c$, then
$\mathcal F\otimes\mathcal B_b$ is punctually $\iota$-pure of weight
$w+c$.

## Proof

At a closed point $y$ of degree $m$, the twist
[def-wf-constant-weil-twist] multiplies every eigenvalue of
$F_y$ by $b^m$, so every eigenvalue $\alpha$ of
$\mathcal F_{\bar y}$ becomes $b^m\alpha$, and

$$
|\iota(b^m\alpha)|=|\iota(b)|^m\,q_y^{w/2}=q^{mc/2}q^{mw/2}
=q_y^{(w+c)/2},
$$

which is the punctual purity of weight $w+c$ of
[def-weil-punctual-weights].
