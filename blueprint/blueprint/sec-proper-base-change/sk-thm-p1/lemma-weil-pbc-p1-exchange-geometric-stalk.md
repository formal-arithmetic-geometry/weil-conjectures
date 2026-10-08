+++
id = "lemma-weil-pbc-p1-exchange-geometric-stalk"
kind = "lemma"
title = "Exchange on a geometric stalk"
order = 1149
uses = ["def-weil-pbc-derived-exchange", "def-weil-pbc-etale-sheaves", "prop-weil-pbc-p1-strict-henselian-comparison", "prop-weil-pbc-strict-henselization-stalk-formula", "prop-weil-pbc-strict-local-exchange"]
+++
For $p:\mathbf P^1_S\to S$, a base change $g:T\to S$, and
$\bar t\to T$ with image $\bar s\to S$, the stalk of
$\operatorname{Ex}_{\square,F}$ is the restriction map

$$
H^q(\mathbf P^1_{\kappa(\bar s)},F|)
\longrightarrow H^q(\mathbf P^1_{\kappa(\bar t)},F|).
$$

## Proof

Let $\bar t\to T$ be represented by an algebraically closed field $\Omega$,
and let $\bar s\to S$ be its composite. Put
$S^{\mathrm{sh}}=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{S,\bar s}$ and
$T^{\mathrm{sh}}=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{T,\bar t}$.
The map $T\to S$ induces a local map $T^{\mathrm{sh}}\to S^{\mathrm{sh}}$
and a separably closed residue-field extension
$\kappa(\bar s)\hookrightarrow\kappa(\bar t)$. For an injective
resolution $F\to I^\bullet$, the strict-henselization construction gives
the following diagram in $D^+(\mathbf{Ab})$:

$$
\begin{CD}
(g^{-1}Rp_*F)_{\bar t}
@>{(\operatorname{Ex}_{\square,F})_{\bar t}}>>
(Rp'_*g'^{-1}F)_{\bar t}\\
@V{\Phi_S}V{\sim}V @VV{\Phi_T}V{\sim}V\\
R\Gamma(\mathbf P^1_{S^{\mathrm{sh}}},I|)
@>{\lambda}>>
R\Gamma(\mathbf P^1_{T^{\mathrm{sh}}},I|)\\
@V{\rho_S}V{\sim}V @VV{\rho_T}V{\sim}V\\
R\Gamma(\mathbf P^1_{\kappa(\bar s)},I_{\bar s})
@>{\kappa(\bar s)\subset\kappa(\bar t)}>>
R\Gamma(\mathbf P^1_{\kappa(\bar t)},I_{\bar t}).
\end{CD}
$$

The maps $\Phi_S$ and $\Phi_T$ are the stalk-to-strict-local maps from the
strict-henselization formula. The maps $\rho_S$ and $\rho_T$ are the S4
restriction quasi-isomorphisms, applied after replacing $\mathbf P^1$ by its
base change to the indicated strict local ring. The bottom arrow is induced
by the residue-field map.

To check the upper square, take a representative section of $I^r$ on an
affine pointed etale neighbourhood $V\to S$. The left route first applies
the unit $I^r\to g'_*g'^{-1}I^r$ and then restricts along
$\mathbf P^1_T\times_T(V\times_ST)$. The right route first restricts to
$\mathbf P^1_{S^{\mathrm{sh}}}$ and then along $T^{\mathrm{sh}}\to S^{\mathrm{sh}}$. Both are the same section on
$\mathbf P^1_{T^{\mathrm{sh}}}\times_{T^{\mathrm{sh}}}V$, so the square
commutes degree by degree and hence in the derived category. The lower
square is the identical calculation after passing to the closed geometric
fibres. Therefore the stalk of the named S0 exchange is exactly the field
extension map displayed in the bottom row, not an abstract replacement.

## Detailed form

Let $p:\mathbf P^1_S\to S$, let $g:T\to S$, and let $\bar t\to T$ have image
$\bar s\to S$. For a torsion sheaf $F$ and every $q$, the stalk of the
exchange morphism [def-weil-pbc-derived-exchange] is the canonical restriction

$$
 H^q(\mathbf P^1_{\kappa(\bar s)},F|)
 \longrightarrow
 H^q(\mathbf P^1_{\kappa(\bar t)},F|),
$$

where both residue fields are separably closed.

## Proof

The strict-henselization stalk formula
[prop-weil-pbc-strict-henselization-stalk-formula] identifies the source and
target stalks with cohomology over the two strict local bases, and the
strict-local comparison of [prop-weil-pbc-strict-local-exchange] identifies
those with the cohomologies of the closed fibres displayed above; expanding
the unit--$\theta_\square$--counit composite of
[def-weil-pbc-derived-exchange] shows that the induced map is the
field-extension pullback.
