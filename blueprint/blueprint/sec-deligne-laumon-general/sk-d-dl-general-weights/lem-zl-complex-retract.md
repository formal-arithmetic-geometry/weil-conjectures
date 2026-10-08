+++
id = "lem-zl-complex-retract"
kind = "lemma"
title = "Retract stability of complex weights"
order = 2813
uses = ["def-weil-complex-weights", "def-weil-derived-cohomology-sheaves", "def-weil-punctual-weights", "lem-a1-mixed-direct-summand"]
+++
Every direct summand of an object of $D_{\le w}(X_0)$ again belongs to
$D_{\le w}(X_0)$.

## Proof

If $K=K'\oplus K''$, then
$\mathcal H^j(K)=\mathcal H^j(K')\oplus\mathcal H^j(K'')$ (cohomology
of a direct sum), so each cohomology sheaf of the summand is a direct
summand of a cohomology sheaf of $K$, which is $\iota$-mixed of
weights at most $w+j$ by [def-weil-complex-weights]; by the
mixedness for direct summands of [lem-a1-mixed-direct-summand],
$\mathcal H^j(K')$ is $\iota$-mixed of weights at most $w+j$ in the
sense of [def-weil-punctual-weights], i.e. $K'\in D_{\le w}(X_0)$.
