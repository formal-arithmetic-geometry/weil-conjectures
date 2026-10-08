+++
id = "thm-sc-finite-type-torsion-cd"
kind = "theorem"
title = "Torsion cohomological dimension of a finite-type scheme"
order = 1558
uses = ["def-sc-etale-torsion-cd", "def-sc-zariski-cohomology", "def-sc-zariski-site", "def-weil-pbc-scheme-conventions", "lem-sc-zariski-dimension-bound", "thm-sc-affine-torsion-cd", "thm-sp-grothendieck"]
+++
Let $K$ be a field with $\operatorname{cd}_{\rm tor}(K)\leq c$,
and let $X$ be a finite-type
$K$-scheme of dimension $d$.
Then $\operatorname{cd}_{\rm tor}(X)\leq2d+c$, in the sense of
[def-sc-etale-torsion-cd].

## Proof

Restrict etale sheaves to Zariski opens to obtain the direct
image $\epsilon_*:\operatorname{Ab}(X_{\rm et})\to \operatorname{Ab}(X_{\rm Zar})$, using [def-sc-zariski-site].
Its inverse image is exact: the geometric stalk of
$\epsilon^{-1}G$ over $x$ is the ordinary Zariski stalk
$G_x$, an exact functor. Thus $\epsilon_*$ preserves
injectives, and [thm-sp-grothendieck] gives

$$
H^p(X_{\rm Zar},R^q\epsilon_*F)
\ \Longrightarrow\ H^{p+q}(X_{\rm et},F).
$$

This is the composite of the two ordinary section functors
of [def-sc-zariski-cohomology].

The Zariski stalk of $R^q\epsilon_*F$ at $x$ is
$\varinjlim_{x\in V}H^q(V_{\rm et},F|_V)$.
To see this, restrict an injective etale resolution to
each open $V$; it remains injective because extension
by zero from an open is exact. Then take the exact
filtered colimit over $V$.
Affine opens are cofinal among neighborhoods of $x$.
They have dimension at most $d$, so
[thm-sc-affine-torsion-cd] makes the stalk zero for
$q>d+c$. Hence $R^q\epsilon_*F=0$ in these degrees.
On the other hand
[lem-sc-zariski-dimension-bound] kills the spectral
sequence for $p>d$, without needing its entries to be
constructible or torsion. All surviving total degrees
are at most $d+(d+c)=2d+c$.
This proves the ordinary etale bound for every torsion $F$;
no identification with compactly supported cohomology is used.
