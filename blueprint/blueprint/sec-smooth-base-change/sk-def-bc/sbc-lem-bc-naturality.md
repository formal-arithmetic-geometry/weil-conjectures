+++
id = "sbc-lem-bc-naturality"
kind = "lemma"
title = "Naturality of the base-change map"
order = 1369
uses = ["sbc-def-base-change-map", "sbc-def-base-change-square"]
+++
For a base-change square the
derived base-change maps $\operatorname{BC}_{f,g}(K)$ of
[sbc-def-base-change-map] are natural in $K$: for every morphism
$u:K\to K'$ in $D(T_{\Et},\Lambda)$ the square

$$
\begin{array}{ccc}
Lf^*Rg_*K & \xrightarrow{\ \operatorname{BC}_{f,g}(K)\ } & Rh_*Le^*K\\
\big\downarrow{\scriptstyle Lf^*Rg_*u} & & \big\downarrow{\scriptstyle Rh_*Le^*u}\\
Lf^*Rg_*K' & \xrightarrow{\ \operatorname{BC}_{f,g}(K')\ } & Rh_*Le^*K'
\end{array}
$$

is commutative.

## Proof

By [sbc-def-base-change-map] the map
$\operatorname{BC}_{f,g}$ is the composite of the unit $\eta_e$ of the
adjunction $Le^*\dashv Re_*$, the two canonical identifications of the
composite functors coming from $ge=fh$, and the counit $\varepsilon_f$
of $Lf^*\dashv Rf_*$. Units and counits of adjunctions are natural
transformations, the canonical identifications of composite functors
are natural in the argument, and a composite of natural transformations
is natural; hence $\operatorname{BC}_{f,g}(-)$ is a natural
transformation of functors $D(T_{\Et},\Lambda)\to D(X_{\Et},\Lambda)$,
which is the commutativity of the displayed square.
