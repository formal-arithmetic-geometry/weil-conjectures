+++
id = "lem-mg-common-positive-central-element"
kind = "lemma"
title = "A common positive-degree central element"
order = 2528
uses = ["d-central", "d-monodromy", "def-wf-arithmetic-monodromy-extension", "def-wf-degree-components", "def-wf-semisimple-module", "lem-mg-degree-component-functoriality", "lem-mg-normal-restriction-semisimple", "lem-wf-degree-component-image", "p-central"]
+++
Let $\mathcal F^{(1)}_0,\ldots,\mathcal F^{(a)}_0$ be lisse
Weil sheaves on the same normal geometrically connected curve
whose Weil representations are semisimple
([def-wf-semisimple-module]; such sheaves are geometrically semisimple
by [lem-mg-normal-restriction-semisimple]),
and let $\rho=\bigoplus_i\rho_i$. There are an integer $m>0$ and

$$
z\in Z\bigl(G_{\mathrm{arith}}(\rho)\bigr)\cap G^{[m]}.
$$

Thus all Weil subquotients of all the $\mathcal F^{(i)}_0$ may be
measured using images of one and the same degree-$m$ element, via the
functoriality of [lem-mg-degree-component-functoriality].

## Proof

The direct sum $\rho$ of semisimple Weil representations is a
semisimple Weil representation, so its monodromy data form a semisimple
represented degree datum in the sense of [d-monodromy], with
$H=H_{\mathrm{geom}}$ and $F=\rho(s)$ for the chosen degree-one $s$.
By [p-central] there is a positive central pair ([d-central]), i.e. $N>0$ and

$$
z_{\mathrm{mat}}=hF^N\in Z(G_{\mathrm{Zar}}),\qquad h\in H_{\mathrm{geom}}.
$$

Put $m=N$ and $z=(h,m)\in G^{[m]}$ in the notation of
[def-wf-degree-components]. The matrix map
$(h',n)\mapsto h'\rho(s)^n$ of
[def-wf-arithmetic-monodromy-extension] is a group homomorphism with
values in $G_{\mathrm{Zar}}$ ([lem-wf-degree-component-image]), and it
sends $z$ to $z_{\mathrm{mat}}$. For $x\in H_{\mathrm{geom}}$, the
commutator of $z$ with $(x,0)$ has degree $0$ and matrix
$z_{\mathrm{mat}}xz_{\mathrm{mat}}^{-1}x^{-1}=1$; the commutator of $z$
with $s=(1,1)$ has degree $0$ and matrix
$z_{\mathrm{mat}}Fz_{\mathrm{mat}}^{-1}F^{-1}=1$. On the degree-zero
component the matrix map $(h',0)\mapsto h'$ is injective, so both
commutators are trivial. Since $G_{\mathrm{arith}}(\rho)$ is generated
by $H_{\mathrm{geom}}\times\{0\}$ and $s$, the element $z$ is central.
Its image on every subquotient has the same
degree and remains central by the functoriality of
[lem-mg-degree-component-functoriality].
