+++
id = "lem-sc-translation-automorphism"
kind = "lemma"
title = "Translations are automorphisms"
order = 1965
uses = ["def-sc-group-scheme", "def-sc-group-scheme-translate"]
+++
In the situation of [def-sc-group-scheme-translate], for every
$g\in G(k)$ the morphisms $L_g$ and $R_g$ are isomorphisms of
$k$-schemes with $L_g^{-1}=L_{g^{-1}}$ and $R_g^{-1}=R_{g^{-1}}$,
and $c_g$ is an automorphism of the group scheme $G$:

$$
c_g\circ m=m\circ(c_g\times c_g),\qquad c_g\circ e=e,\qquad
c_g\circ i=i\circ c_g .
$$

## Proof

On $R$-points the definitions of
[def-sc-group-scheme-translate] give $L_g(R)(x)=\tilde gx$ and
$R_g(R)(x)=x\tilde g$, where $\tilde g\in G(R)$ is the image of
$g$. By the inverse axiom for the group $G(R)$
([def-sc-group-scheme]), $L_{g^{-1}}(R)L_g(R)$ and
$L_g(R)L_{g^{-1}}(R)$ are the identity on $G(R)$, and similarly on
the right. Since the functor of points $R\mapsto G(R)$ is faithful
(it is the restriction of $\mathrm{Hom}_k(-,G)$), these identities of
morphisms follow. For conjugation,
$c_g(R)(x)=\tilde gx\tilde g^{-1}$, and
$\tilde g(xy)\tilde g^{-1}=(\tilde gx\tilde g^{-1})(\tilde gy\tilde g^{-1})$, $\tilde ge\tilde g^{-1}=e$ and
$\tilde gx^{-1}\tilde g^{-1}=(\tilde gx\tilde g^{-1})^{-1}$ are
instances of the group axioms in $G(R)$; faithfulness gives the three
displayed identities.
