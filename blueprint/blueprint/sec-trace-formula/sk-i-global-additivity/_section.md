+++
id = "sk-i-global-additivity"
kind = "section"
title = "Compact trace additivity"
order = 2372
uses = ["sk-d-operator", "sk-d-six", "sk-d-trace", "sk-d-weil", "sk-p-trace", "sk-prop-sf-open-closed-triangle", "sk-thm-sf-package"]
lean = ["AlgebraicGeometry.ProEtale.trace_globalOperator_add"]
+++
*Proposition (sketch).*

For a closed immersion $i_0:Z_0\hookrightarrow X_0$ and its open
complement $j_0:U_0\hookrightarrow X_0$, the induced
Frobenius coefficient morphisms on the functorial
compact localization triangle satisfy

$$
\tr_A(F_{c,m},R\Gamma_c(X,K))=
\tr_A(F_{c,m},R\Gamma_c(U,j^*K))+
\tr_A(F_{c,m},R\Gamma_c(Z,i^*K)).
$$

These are traces of perfect complexes; invertibility
of the coefficient morphism is unnecessary.

## Proof

Applying compact cohomology to [sk-prop-sf-open-closed-triangle] gives a
functorial compact localization triangle, and compact cohomology of a
finite-Tor constructible complex is perfect, so the three global operators
form an endomorphism of a distinguished triangle of perfect complexes. This
alone does not suffice: the trace is *not* additive on arbitrary
endomorphisms of distinguished triangles of perfect complexes in the
Verdier derived category (Ferrand's example, cf.
[Stacks, Tag 087J](https://stacks.math.columbia.edu/tag/087J): over
$R=\mathbf Z/4$ the short exact sequence
$0\to R[-1]\to[R\xrightarrow{2}R]\to R\to0$ with the endomorphism
$(0,(0,2),0)$, whose squares commute up to homotopy, has
$\tr=-2\ne0=0+0$). What is used is that the three operators have a common
filtered origin. The localization triangle is the cofibre sequence of
$j_!j^*K\to K$ in the category of pairs $(K,u)$ of [sk-d-weil]: the
coefficient morphisms on the pieces are the induced maps $u^U=j_!j^*u$
(after open $!$-base change) and $u^Z=i_*i^*u$ (after closed base change),
so $(j_!j^*K,u^U)\to(K,u)$ is a two-step filtered object with a filtered
endomorphism, i.e. an endomorphism in the filtered derived category, with
graded pieces $(j_!j^*K,u^U)$ and $(i_*i^*K,u^Z)$. The global operator of
[sk-d-operator] is a natural transformation of exact functors, built from
the unit of $\Phi_m^*$, the identification $R\Phi_{m!}=R\Phi_{m*}$ for the
finite map $\Phi_m$, the composition law $a_X\Phi_m=a_X$ and the
coefficient morphism; applying $R\Gamma_c$ therefore yields an endomorphism
of a filtered perfect complex in the filtered derived category $DF(A)$,
with graded pieces $R\Gamma_c(U,j^*K)$ and $R\Gamma_c(Z,i^*K)$ carrying
their operators. For such filtered endomorphisms the trace is additive over
the graded pieces ([Stacks, Tag 03TJ](https://stacks.math.columbia.edu/tag/03TJ)):
a filtered endomorphism is represented by a strict endomorphism of a
filtered bounded complex of finite projectives, block triangular with
respect to the filtration, and the off-diagonal block does not contribute
to the supertrace of [sk-p-trace]. This gives the displayed identity. Only
exactness of the global operator, its functorial origin and the formal laws
of the trace are used; no trace of an individual, possibly nonperfect,
cohomology module occurs, and the coefficient morphism need not be
invertible.

Uses: [sk-d-operator], [sk-d-six], [sk-d-trace], [sk-d-weil], [sk-p-trace], [sk-prop-sf-open-closed-triangle], [sk-thm-sf-package]
