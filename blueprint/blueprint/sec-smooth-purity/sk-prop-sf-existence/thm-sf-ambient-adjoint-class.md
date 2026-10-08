+++
id = "thm-sf-ambient-adjoint-class"
kind = "theorem"
title = "The exceptional adjoint on the bounded comparison class"
order = 1807
uses = ["def-sf-fullcd-class", "def-weil-pbc-site-comparison-morphism", "lem-amb-etale-compact-comparisons", "lem-sf-class-compact-support-comparison", "thm-amb-etale-exceptional-adjoint", "thm-sf-fullcd-class", "thm-weil-pbc-site-comparison"]
+++
Let $f:X\to Y$ be separated of finite type over $\Fbar$, with a
compactification of dimension at most $d$, and let $A=A_{E,n}$.
Then the following statements hold:

1. The class-restricted dimension datum
[def-sf-fullcd-class] holds with bound $2d$.
1. Let $f^\times$ be the right adjoint of the étale
compact-support functor. On bounded-below pro-étale coefficients put
$$
Rf_n^\times L=\nu_X^* f^\times R\nu_{Y,*}L.
$$
For every bounded-below $K$ of étale origin and every bounded-below
$L$, there is a natural bijection
$$
\operatorname{Hom}(Rf_{!,n}K,L)
\cong\operatorname{Hom}(K,Rf_n^\times L).
$$
Thus this formula is the right adjoint relative to the bounded-below
comparison class. It applies in particular to the bounded constructible
inputs used here.
1. Compactification comparisons of these functors are canonical and
satisfy the cocycle condition.

No adjunction on arbitrary unbounded pro-étale objects is asserted.

## Proof

Clause (1) is [thm-sf-fullcd-class]. Write $K=\nu_X^*G$ with
$G$ bounded below. The finite cohomological dimension of compact
support implies that its right adjoint $f^\times$ takes bounded-below
objects to bounded-below objects: a bound
$Rf_!D^{\leq0}\subseteq D^{\leq N}$ gives
$f^\times D^{\geq0}\subseteq D^{\geq-N}$ by adjunction and
orthogonality. Hence all étale objects in the following comparison
are in the domain of the fully faithful functor of
[thm-weil-pbc-site-comparison]. Using
[lem-sf-class-compact-support-comparison] and the adjoint of
[thm-amb-etale-exceptional-adjoint] gives

$$
\operatorname{Hom}(Rf_{!,n}\nu_X^*G,L)
\cong\operatorname{Hom}(Rf_!^{\Et}G,R\nu_{Y,*}L)
\cong\operatorname{Hom}(G,f^\times R\nu_{Y,*}L)
\cong\operatorname{Hom}(\nu_X^*G,\nu_X^*f^\times R\nu_{Y,*}L).
$$

The last step is full faithfulness, not an adjunction with a second
$R\nu_{X,*}$; the latter would have the wrong source category.
The bijection is natural and independent of the witness. The coherent
compactification comparisons follow by applying the fixed functors
$\nu_X^*$ and $R\nu_{Y,*}$ to the étale comparisons of
[lem-amb-etale-compact-comparisons] and using uniqueness of the
étale right adjoints. This proves (2) and (3).
