+++
id = "lem-a1-lisse-middle-extension"
kind = "lemma"
title = "Recovery from a dense lisse open"
order = 2645
uses = ["def-wf-middle-extension", "lem-wf-boundary-stalk-invariants"]
+++
If $\mathcal F$ is lisse on a smooth curve $C_0$ and
$j:U_0\hookrightarrow C_0$ is dense, then the adjunction map

$$
\mathcal F\xrightarrow{\sim}j_*j^*\mathcal F
$$

is an isomorphism.

## Proof

The assertion is clear on $U_0$. At a removed point, lissity on
$C_0$ makes the local inertia action trivial, so the invariant-stalk
formula of [lem-wf-boundary-stalk-invariants] identifies the
target stalk with the original stalk: $(j_*j^*\mathcal F)_{\bar x}= ((j^*\mathcal F)_{\bar\eta})^{I_x}=(\mathcal F_{\bar x})^{I_x}= \mathcal F_{\bar x}$, the last equality because $I_x$ acts trivially
on the stalk of a lisse sheaf. The map is the naturality of the
adjunction at every geometric point, hence an isomorphism.
