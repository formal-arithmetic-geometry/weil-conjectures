+++
id = "def-weil-pbc-projection-formula-map"
kind = "definition"
title = "Projection-formula map"
order = 1252
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-proetale-operations"]
+++
For $f:X\to Y$, $K\in D(X_{\Proet},A)$, and $P\in D(Y_{\Proet},A)$, define

$$
 \pi_{f,K,P}:(Rf_*K)\otimes_A^LP
 \longrightarrow Rf_*(K\otimes_A^LLf^*P)
$$

as the adjoint of the tensor product of the counit $Lf^*Rf_*K\to K$ with
$Lf^*P$, using the operations of [def-weil-pbc-proetale-operations].

(*Source:* the morphism is Stacks Project, Cohomology on Sites, Equation
21.50.0.1 (Tag [0B56](https://stacks.math.columbia.edu/tag/0B56)), the map
$Rf_*E\otimes^L_{\mathcal O_{\mathcal D}}K\to Rf_*(E\otimes^L_{\mathcal
O_{\mathcal C}}Lf^*K)$ of Section 21.50 (Tag
[0943](https://stacks.math.columbia.edu/tag/0943), Projection formula), which
is defined there as the adjoint of the canonical map $Lf^*(Rf_*E\otimes^L_{
\mathcal O_{\mathcal D}}K)= Lf^*Rf_*E\otimes^L_{\mathcal O_{\mathcal
C}}Lf^*K\to E\otimes^L_{\mathcal O_{\mathcal C}}Lf^*K$ coming from the map
$Lf^*Rf_*E\to E$. The blueprint's $\pi_{f,K,P}$ is this map for the ambient
pro-etale ringed topoi with $E=K$ and $K=P$, and its description as the
adjoint of the tensor product of the counit $Lf^*Rf_*K\to K$ with $Lf^*P$ is
Stacks' description. Difference of generality: Stacks states the map for a
morphism of ringed topoi with coefficients in the structure sheaves $\mathcal
O_{\mathcal C}$, $\mathcal O_{\mathcal D}$, with no completeness hypothesis
and no coefficient tower, whereas the blueprint forms it for the operations
of [def-weil-pbc-proetale-operations] inside the adic coefficient datum of
[def-weil-pbc-adic-coefficient-datum]; no statement about the map itself
differs.)
