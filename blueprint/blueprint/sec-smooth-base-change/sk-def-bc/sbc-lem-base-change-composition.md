+++
id = "sbc-lem-base-change-composition"
kind = "lemma"
title = "Base change for a composite square"
order = 1371
uses = ["lem-weil-pbc-exchange-identity-pasting", "sbc-def-base-change-map", "sbc-def-base-change-square"]
+++
Consider a tower of Cartesian diagrams of schemes

$$
\begin{array}{ccc}
W & \xrightarrow{j} & Z\\
i\big\downarrow & & \big\downarrow k\\
X & \xrightarrow{h} & Y\\
f\big\downarrow & & \big\downarrow e\\
S & \xrightarrow{g} & T
\end{array}
$$

and let $K\in D(T_{\Et})$. If

$$
f^{-1}Rg_*K\xrightarrow{\ \sim\ }Rh_*e^{-1}K
\quad\text{and}\quad
i^{-1}Rh_*e^{-1}K\xrightarrow{\ \sim\ }Rj_*k^{-1}e^{-1}K
$$

are isomorphisms, then
$(f\circ i)^{-1}Rg_*K\to Rj_*(e\circ k)^{-1}K$ is an isomorphism
(``the outer rectangle'') and the analogous statement holds
degreewise for an abelian sheaf $\mathcal F$ on $T_{\Et}$ and the maps
$R^q$.
(*Stacks Project, Lemma 59.86.2, [Tag `0EZS`](https://stacks.math.columbia.edu/tag/0EZS).*)

## Proof

The composites of the two base-change maps of
[sbc-def-base-change-map] are the mates of the same composite of
the identification isomorphisms $\theta_\square$ of the two pasted
squares; the associativity and triangle identities for the
inverse-image–direct-image adjunctions (the identity and pasting laws
recorded in [lem-weil-pbc-exchange-identity-pasting], applied with
the roles of the vertical and horizontal sides interchanged) show that
this mate is exactly the base-change map of the outer rectangle, so the
composite of the two isomorphisms is the required isomorphism.
