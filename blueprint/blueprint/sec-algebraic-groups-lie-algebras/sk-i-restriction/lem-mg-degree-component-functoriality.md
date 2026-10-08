+++
id = "lem-mg-degree-component-functoriality"
kind = "lemma"
title = "Degree components under subquotients and tensor constructions"
order = 2520
uses = ["def-wf-degree-components", "def-wf-monodromy-data", "lem-wf-arith-extension-group", "lem-wf-stabilizer-density"]
+++
Let $\rho:W(X_0)\to\operatorname{GL}(V)$ have the monodromy data of
[def-wf-monodromy-data]. Let each $Q_i$ be a Weil-stable
subquotient $U_i/U'_i$ of $V$, or an iterated subquotient of one of
the constructions below, and let $Q$ be one of

$$
Q_i,\qquad Q_1\otimes\cdots\otimes Q_a,
\qquad \bigwedge\nolimits^b Q_i.
$$

The closed-stabilizer fact of [lem-wf-stabilizer-density] makes the
induced action algebraic. The action on $Q$ induces a homomorphism

$$
\Phi_Q:G_{\mathrm{arith}}(\rho)\longrightarrow
G_{\mathrm{arith}}(\rho_Q)
$$

which is regular on every degree component, preserves the degree, and has
Zariski-dense image on every degree component. In particular, the image
of a central element is central.

## Proof

Use the monodromy data of [def-wf-monodromy-data]. Every $U_i$
and $U'_i$ is stable under $\rho(\Pi)$. Its stabilizer
is closed by [lem-wf-stabilizer-density], so it is stable under
$H_{\mathrm{geom}}=\overline{\rho(\Pi)}$ as well. Thus an element
$h\in H_{\mathrm{geom}}$ induces an operator on every $Q_i$, hence on
the displayed tensor product or exterior power. Denote that operator by
$R(h)$. In bases adapted to $U'_i\subseteq U_i\subseteq V$, its
matrix entries are polynomial expressions in the entries of $h$ and
$\det(h)^{-1}$; hence $R$ is a regular homomorphism.

Choose the same degree-one element $s$ for $\rho$ and $\rho_Q$.
Because all subspaces are Weil-stable, $\rho(s)$ preserves them, and

$$
R\bigl(\rho(s)h\rho(s)^{-1}\bigr)
=\rho_Q(s)R(h)\rho_Q(s)^{-1}.
$$

Consequently the componentwise formula

$$
\Phi_Q(h,m)=(R(h),m)
$$

respects the semidirect-product multiplication of
[lem-wf-arith-extension-group] and the degree components
of [def-wf-degree-components]. To see that it lands in the target
geometric group, take any closed subset of $\operatorname{GL}(Q)$
containing $R(\rho(\Pi))=\rho_Q(\Pi)$. Its inverse image under $R$
is closed and contains $\rho(\Pi)$, hence contains
$H_{\mathrm{geom}}$; therefore it contains $R(H_{\mathrm{geom}})$.
This proves
$R(H_{\mathrm{geom}})\subseteq H_{\mathrm{geom}}(\rho_Q)$, and the
reverse inclusion after taking Zariski closures follows from
$R(\rho(\Pi))=\rho_Q(\Pi)$. Thus the image is dense in degree zero,
and translation by the degree-$m$ element gives density in every degree.

If $z$ is central in the source, $\Phi_Q(z)$ commutes with the image
of every source component. Commuting with a fixed matrix is a closed
condition on matrix entries, so density makes $\Phi_Q(z)$ commute with
every target component. The commutator has degree zero, and on the
degree-zero component the matrix map $(h,0)\mapsto h$ is injective;
therefore this matrix commutation is equality in the graded target group,
so $\Phi_Q(z)$ is central. For an iterated
subquotient, repeat the construction at each stage; the resulting
morphisms compose and retain all the properties just proved.
