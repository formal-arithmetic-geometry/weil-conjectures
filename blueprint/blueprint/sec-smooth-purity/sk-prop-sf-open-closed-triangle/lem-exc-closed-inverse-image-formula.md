+++
id = "lem-exc-closed-inverse-image-formula"
kind = "lemma"
title = "A presheaf formula for closed inverse image"
order = 1845
uses = ["def-exc-closed-site-lift", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-operations", "lem-exc-closed-site-adjunction", "lem-weil-pbc-ind-etale-basis"]
+++
For an affine closed immersion $i:Z\hookrightarrow X$ and a pro-etale
$\Lambda$-module sheaf $F$, with $\Lambda$ finite, $i^*F$ is the
sheafification on $\mathcal B_Z$ of
$$
 P_F(V)=F(v(V)).
$$
The formula includes sheafification; it does not presume the presheaf is
already a sheaf.

## Proof

Work with sheaves on the bases by [lem-weil-pbc-ind-etale-basis]. Underived
direct image is $(i_*G)(W)=G(u(W))$. A morphism $F\to i_*G$ therefore gives
$F(v(V))\to G(u(v(V)))=G(V)$, hence $P_F\to G$. Conversely $P_F\to G$
defines
$$
 F(W)\longrightarrow F(v(u(W)))\longrightarrow G(u(W)),
$$
where the first arrow is restriction along the counit $v(u(W))\to W$ of
[def-exc-closed-site-lift], [lem-exc-closed-site-adjunction]. The triangle
identities, or evaluation of these formulas, show that the two constructions
are inverse. Sheafification does not change maps to $G$. Thus $P_F^a$ has
the adjunction that defines $i^*$ in the pro-etale operations, proving the
formula.
