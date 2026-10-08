+++
id = "lem-mg-determinant-monodromy-morphism"
kind = "lemma"
title = "The determinant morphism of arithmetic monodromy"
order = 2521
uses = ["def-mg-determinant-line", "def-wf-arithmetic-monodromy-extension", "def-wf-degree-components", "lem-mg-degree-component-functoriality"]
+++
For a rank-$r$ Weil representation $\rho$, taking the
determinant line induces a
degree-preserving, componentwise regular homomorphism

$$
\Delta_\rho:\hyperref[def-wf-arithmetic-monodromy-extension]{G_{\mathrm{arith}}(\rho)}\longrightarrow
G_{\mathrm{arith}}(\det\rho),
\qquad (h,m)\longmapsto(\det h,m),
$$

whose image is dense on every degree
component. This is the determinant instance of the functoriality in
[lem-mg-degree-component-functoriality], and it sends central elements
to central elements.

## Proof

The determinant line of [def-mg-determinant-line] is the exterior
power $\bigwedge^rV$. Apply
[lem-mg-degree-component-functoriality] with $Q=\bigwedge^rV$.
On the geometric group its induced operator is $h\mapsto\det h$, so
the component formula is the one displayed. The multiplication rule in
[def-wf-arithmetic-monodromy-extension] also verifies it directly:
determinants are multiplicative and are unchanged by conjugation. Density
and preservation of centrality are the final assertions of
[lem-mg-degree-component-functoriality].
