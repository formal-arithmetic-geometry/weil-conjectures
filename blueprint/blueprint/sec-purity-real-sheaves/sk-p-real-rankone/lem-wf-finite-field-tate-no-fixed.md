+++
id = "lem-wf-finite-field-tate-no-fixed"
kind = "lemma"
title = "Arithmetic Frobenius has no fixed vector on the Jacobian Tate module"
order = 2622
uses = ["d-ab-field", "def-sc-jacobian", "def-tate-module-abelian-group", "def-wf-abelian-tate-module", "lem-wf-geometric-jacobian-galois-action", "prop-av-tate-no-frobenius-fixed", "thm-av-final", "thm-pd-jacobian-general-field"]
+++
Let $C_0/\mathbf F_Q$ be a smooth projective geometrically connected curve,
put $C=C_0\times_{\mathbf F_Q}\overline{\mathbf F}_Q$, and let $J$ be its
Jacobian, equipped with the canonical semilinear
action of arithmetic Frobenius $\sigma_Q:z\mapsto z^Q$
([lem-wf-geometric-jacobian-galois-action]). If $\ell\nmid Q$, then

$$
(T_\ell J)^{\sigma_Q=1}=0,
$$

and $\sigma_Q-1$ is an automorphism of the
rational Tate module $V_\ell J$.

## Proof

Let $J_0$ be the Jacobian of $C_0$ over $\mathbf F_Q$ given by
[thm-pd-jacobian-general-field] (which applies since $C_0$ is smooth,
projective and geometrically connected), so that
$J\cong J_0\times_{\mathbf F_Q}\overline{\mathbf F}_Q$. We check that $J_0$ is an
abelian variety over $k_0=\mathbf F_Q$ in the sense of [d-ab-field], with
$q=Q$ and $p$ the characteristic, so that $\ell\ne p$ as $\ell\nmid Q$. By
[thm-pd-jacobian-general-field] it is an abelian variety over $\mathbf F_Q$,
hence a proper (in particular finite-type) group scheme. It is commutative:
it represents the group-valued functor $\operatorname{Pic}^0_{C_0/\mathbf F_Q}$,
whose values are abelian groups, so by Yoneda its group law is commutative.
Its base change $J_0\times_{\mathbf F_Q}\overline{\mathbf F}_Q\cong J$ is an
abelian variety over $\overline{\mathbf F}_Q$ ([def-sc-jacobian]), hence
connected and smooth, so its local rings are regular; thus $J_0$ is smooth and
geometrically connected in the sense of [d-ab-field].

By [lem-wf-geometric-jacobian-galois-action], under
$J\cong J_0\times_{\mathbf F_Q}\overline{\mathbf F}_Q$ the canonical action of
$\sigma_Q$ is $\mathrm{id}_{J_0}\times\sigma_Q$, which on
$J(\overline{\mathbf F}_Q)=J_0(\overline{\mathbf F}_Q)$ is the action through the
$\mathbf F_Q$-structure of $J_0$, i.e. by coordinates. Thus $\sigma_Q$ acts on
$A:=J_0(\overline{\mathbf F}_Q)$ as the arithmetic Frobenius $\sigma$ of
[d-ab-field] or as its inverse $F$ (according to the convention for composing
points with $\operatorname{Spec}\sigma_Q$); either way it has the same fixed
vectors as $\sigma$ and as $F$. The Tate module of [def-wf-abelian-tate-module]
is the Tate module of the abelian group $J(\overline{\mathbf F}_Q)=A$
([def-tate-module-abelian-group]), and the action is componentwise. Hence
[prop-av-tate-no-frobenius-fixed], applied to the abelian variety $J_0/\mathbf F_Q$,
gives $(T_\ell J)^{\sigma_Q=1}=(T_\ell A)^\sigma=0$, proving the first
assertion.

By [thm-av-final](c),
$J[\ell^n](\overline{\mathbf F}_Q)\cong (\mathbf Z/\ell^n\mathbf Z)^{2\dim J}$; with the multiplication-by-$\ell$
transition maps this makes $T_\ell J$ finite free ([thm-av-final](d)) and $V_\ell J$
finite-dimensional. If a vector of $V_\ell J$ is killed by $\sigma_Q-1$,
multiplying it by a power of $\ell$ puts it in $T_\ell J$, where the first
assertion kills it. Hence $\sigma_Q-1$ is injective on the
finite-dimensional vector space $V_\ell J$, and elementary linear algebra
makes it surjective as well.
