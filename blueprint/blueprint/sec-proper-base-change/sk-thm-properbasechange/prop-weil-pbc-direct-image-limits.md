+++
id = "prop-weil-pbc-direct-image-limits"
kind = "theorem"
title = "Direct image, derived limits, and completeness"
order = 1276
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit", "def-weil-pbc-projection-formula-map", "lemma-weil-pbc-perfect-projection-formula", "prop-weil-pbc-roos-triangle"]
tags = ["latex:proposition"]
+++
Levelwise direct image on tower categories has a total right derived functor

$$
 Rf_*^{\operatorname{Tow}}:
 D(\operatorname{Tow}_{A}(X))
 \longrightarrow D(\operatorname{Tow}_{A}(Y)),
$$

with $\operatorname{ev}_nRf_*^{\operatorname{Tow}}M_\bullet\simeq Rf_*M_n$.
For every $M_\bullet$ the canonical map

$$
 Rf_*\Rlim M_\bullet
 \xrightarrow{\sim}
 \Rlim\bigl(Rf_*^{\operatorname{Tow}}M_\bullet\bigr)
$$

is an isomorphism. Under the two canonical Roos triangles associated with the
derived inverse-limit [def-weil-pbc-derived-inverse-limit] construction, it
is induced by the canonical isomorphisms

$$
 Rf_*R\!\prod_nM_n\xrightarrow{\sim}
 R\!\prod_nRf_*M_n
$$

and their commutation with $(1-s)$. If $K\in D(X_{\Proet},A)$ is derived
$I$-complete, then $Rf_*K$ is derived $I$-complete. For every $n\geq1$, the
projection-formula morphism

$$
 (Rf_*K)\otimes_A^LP_n\longrightarrow Rf_*(K\otimes_A^LP_n)
$$

is a functorial isomorphism

$$
 (Rf_*K)\otimes_A^LP_n
 \xrightarrow{\sim}Rf_*(K\otimes_A^LP_n)=Rf_*K_n,
$$

and these isomorphisms commute with $P_{n+1}\to P_n$. Under them, the
completion map for $Rf_*K$ is the composite

$$
 Rf_*K\xrightarrow{\sim}Rf_*\Rlim K_\bullet
 \xrightarrow{\sim}\Rlim Rf_*^{\operatorname{Tow}}K_\bullet.
$$

The commutation $Rf_*\Rlim\xrightarrow{\sim}\Rlim Rf_*^{\operatorname{Tow}}$
and the completeness of $Rf_*K$ for derived complete $K$ are clauses (1), (3)
and (4) of Stacks Project, Lemma 61.20.2 (Tag
[099N](https://stacks.math.columbia.edu/tag/099N), Section 61.20, Tag
[099L](https://stacks.math.columbia.edu/tag/099L)): the Stacks entry assumes
a Noetherian ring $\Lambda$, an ideal $I\subset\Lambda$ and a morphism of
topoi, and states that $Rf_*$ sends $D_{comp}$ into $D_{comp}$ and that
$Rf_*K=\Rlim Rf_*(K\otimes^L_\Lambda\underline{\Lambda/I^n})$; the form used
here is its tower-level refinement over $T_{\Proet}$, and the finite-level
projection-formula isomorphisms coming from
[lemma-weil-pbc-perfect-projection-formula] are not part of the Stacks
statement.

## Proof

The tower category of [def-weil-pbc-adic-coefficient-datum] is Grothendieck
abelian with exact evaluation functors, so levelwise K-injective resolutions
(also with respect to the K-injective presentation of
[def-weil-pbc-derived-inverse-limit]) give the total right derived functor
$Rf_*^{\operatorname{Tow}}$ with
$\operatorname{ev}_nRf_*^{\operatorname{Tow}}M_\bullet\simeq Rf_*M_n$.
Applying $Rf_*$ to the canonical Roos triangle of
[prop-weil-pbc-roos-triangle] for $M_\bullet$ and comparing with the Roos
triangle for $Rf_*^{\operatorname{Tow}}M_\bullet$, using that the derived
products commute with $Rf_*$ (they are the products of the levelwise
K-injective resolutions and direct image is a right adjoint, hence
product-preserving) and with $(1-s)$, identifies the two triangles and gives
the displayed isomorphism $Rf_*\Rlim M_\bullet\xrightarrow{\sim}
\Rlim(Rf_*^{\operatorname{Tow}}M_\bullet)$. If $K$ is derived $I$-complete
then, applied to the tower $K_\bullet$, this shows $Rf_*K\xrightarrow{\sim}
\Rlim Rf_*^{\operatorname{Tow}}K_\bullet$, so $Rf_*K$ is derived
$I$-complete; [lemma-weil-pbc-perfect-projection-formula] supplies the
projection-formula isomorphisms
$(Rf_*K)\otimes_A^LP_n\xrightarrow{\sim}Rf_*(K\otimes_A^LP_n)=Rf_*K_n$ of
[def-weil-pbc-projection-formula-map], commuting with $P_{n+1}\to P_n$ by the
normalization data of [def-weil-pbc-adic-coefficient-datum]; under them the
completion map for $Rf_*K$ is the displayed composite.
