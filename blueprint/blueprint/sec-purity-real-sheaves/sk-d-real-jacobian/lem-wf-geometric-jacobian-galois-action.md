+++
id = "lem-wf-geometric-jacobian-galois-action"
kind = "lemma"
title = "Canonical semilinear Galois action on the geometric Jacobian"
order = 2609
uses = ["def-sc-jacobian", "def-sc-picard-functor", "def-wf-abelian-tate-module", "lem-pc-representable-unique", "lem-sc-jacobian-unique", "thm-pd-jacobian-general-field", "thm-sc-jacobian-representability"]
+++
Let $C_0/k_0$ be a smooth projective geometrically connected curve, put
$C=C_0\times_{k_0}\overline{k}_0$, and let $J$ be the
Jacobian of $C$, which exists by
[thm-sc-jacobian-representability] because $C$ is a smooth projective
curve over the separably closed field $\overline{k}_0$ and is geometrically
integral ($C_0$ is smooth, hence geometrically reduced, and geometrically
connected by hypothesis). For every
$\sigma\in\operatorname{Gal}(\overline{k}_0/k_0)$ there is a canonical
isomorphism

$$
\sigma_J:\;J\longrightarrow J
\qquad\text{over}\qquad
\sigma:\operatorname{Spec}\overline{k}_0\longrightarrow
\operatorname{Spec}\overline{k}_0,
$$

which preserves the group laws and is compatible with the identification
$\operatorname{Pic}^0(C)=J(\overline{k}_0)$; the assignment
$\sigma\mapsto\sigma_J$ is an action of
$\operatorname{Gal}(\overline{k}_0/k_0)$, so that $J(\overline{k}_0)$ is a
Galois module and $T_\ell J$ a
$\mathbf Z_\ell[\operatorname{Gal}(\overline{k}_0/k_0)]$-module for the Tate
module of [def-wf-abelian-tate-module]. Moreover, if $J_0$ is the
Jacobian of $C_0$ over $k_0$ of [thm-pd-jacobian-general-field], then
under the isomorphism $J\cong J_0\times_{k_0}\overline{k}_0$ of that
theorem one has $\sigma_J=\mathrm{id}_{J_0}\times\sigma$; hence the action
on $J(\overline{k}_0)=J_0(\overline{k}_0)$ is the one through the
$k_0$-structure of $J_0$, and the identification
$J_0[\ell^n](\overline{k}_0)\cong\operatorname{Pic}^0(C)[\ell^n]$ is
$\operatorname{Gal}(\overline{k}_0/k_0)$-equivariant for every $\ell$ and
$n$.

## Proof

The automorphism $\sigma$ of $\overline{k}_0$ over $k_0$ defines the
automorphism $\sigma_C:=\mathrm{id}_{C_0}\times\sigma$ of $C$ over
$\sigma$, hence an isomorphism of functors
$\sigma_C^*:\operatorname{Pic}^0_{C/\overline{k}_0}\to \operatorname{Pic}^0_{C/\overline{k}_0}$ on
$(\mathit{Sch}/\overline{k}_0)_{fppf}$
([def-sc-picard-functor]). Since $J$ represents
$\operatorname{Pic}^0_{C/\overline{k}_0}$
([thm-sc-jacobian-representability], [def-sc-jacobian]), this
isomorphism of functors is induced by a unique isomorphism $\sigma_J:J\to J$
over $\sigma$, by Yoneda together with the uniqueness of representing
objects ([lem-pc-representable-unique],
[lem-sc-jacobian-unique]); it preserves the group laws because
$\sigma_C^*$ is an isomorphism of group-valued functors. Functoriality of
base change gives $(\sigma\tau)_C^*=\sigma_C^*\tau_C^*$ and
$\mathrm{id}_C^*=\mathrm{id}$, so $\sigma\mapsto\sigma_J$ is an action;
passing to geometric points and to torsion gives the Galois module structure
on $J(\overline{k}_0)$ and on the Tate module of
[def-wf-abelian-tate-module].

For the comparison with $J_0$: by [thm-pd-jacobian-general-field] the
scheme $J_0\times_{k_0}\overline{k}_0$ represents
$\operatorname{Pic}^0_{C_0/k_0}\times_{k_0}\overline{k}_0=
\operatorname{Pic}^0_{C/\overline{k}_0}$, through the base change of the
isomorphism $h_{J_0}\cong\operatorname{Pic}^0_{C_0/k_0}$. That isomorphism
is a natural transformation of functors on $k_0$-schemes, and
$\mathrm{id}_{C_0}\times\sigma$ and $\mathrm{id}_{J_0}\times\sigma$ are the
maps induced on the base changes by the $k_0$-morphism
$\sigma:\operatorname{Spec}\overline{k}_0\to\operatorname{Spec}\overline{k}_0$;
hence $\mathrm{id}_{J_0}\times\sigma$ is an isomorphism over $\sigma$
inducing $\sigma_C^*$ on the represented functor. By the uniqueness in
the Yoneda argument above it equals $\sigma_J$ (after transport along
$J\cong J_0\times_{k_0}\overline{k}_0$, which is compatible with the
representing isomorphisms by [lem-sc-jacobian-unique]). On
$\overline{k}_0$-points, $\mathrm{id}_{J_0}\times\sigma$ acts on
$J_0(\overline{k}_0)=\operatorname{Hom}_{k_0}(\operatorname{Spec}\overline{k}_0,J_0)$
through the $k_0$-structure of $J_0$, and the equivariance of the torsion
identification is the torsion clause of [thm-pd-jacobian-general-field].
