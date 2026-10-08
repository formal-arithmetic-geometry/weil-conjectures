+++
id = "sk-p-trace"
kind = "section"
title = "Trace on perfect complexes"
order = 2302
uses = ["sk-d-trace"]
lean = ["DerivedCategory.trace_eq_sum_negOnePow_trace"]
+++
*Proposition (sketch).*

For a commutative ring $R$, a bounded finite-projective complex $P^\bullet$,
and a chain endomorphism $v$, the categorical trace is

$$
\tr_R(v\mid P^\bullet)=\sum_i(-1)^i\Tr_R(v^i\mid P^i).
$$

## Proof

Choose finite dual frames $(p_{ia},\lambda_{ia})_a$ with
$\sum_a p_{ia}\lambda_{ia}=1_{P^i}$, by splitting a finite free module.
In [sk-d-trace], coevaluation is $\sum_{i,a}p_{ia}\otimes\lambda_{ia}$.
Under $P\otimes P^\vee\simeq\operatorname{Hom}^\bullet(P,P)$ this is
$1_P$, hence a closed tensor; the dual-frame identity gives the triangle
identities. The dual factor has degree $-i$, so symmetry gives $(-1)^i$,
and evaluation gives $\sum_{i,a}(-1)^i\lambda_{ia}(v^ip_{ia})$.
This is the asserted sum. The evaluation composite is unchanged when
duality is transported along an isomorphism, by the triangle identities;
in particular traces are invariant under conjugacy.

Uses: [sk-d-trace]
