+++
id = "lem-pur-support-restriction-triangle"
kind = "lemma"
title = "Restriction triangle inside a closed support"
order = 1936
uses = ["def-pur-flasque-support", "def-pur-support-cohomology", "def-weil-open-closed-recollement", "def-weil-pbc-derived-categories", "def-weil-pbc-etale-site", "def-weil-pbc-kinjective-resolutions", "def-weil-scheme-morphism-properties"]
+++
Let $T$ be a scheme, let $B,C\subseteq T$ be
closed subschemes, and
put $V=T\setminus C$, with open immersion $v:V\hookrightarrow T$.
Let $F$ be a bounded-below complex of module sheaves on the
small etale site.
Write $R\Gamma_B(T,F)$ for the derived functor of the
sections supported on $B$,
whose cohomology is the
cohomology with support.
There is a natural distinguished triangle in the
derived category of modules:

$$
R\Gamma_{B\cap C}(T,F)\longrightarrow R\Gamma_B(T,F)
\longrightarrow R\Gamma_{B\cap V}(V,v^*F)\longrightarrow
R\Gamma_{B\cap C}(T,F)[1].
$$

The third support is closed in $V$; its ambient scheme is $V$.

## Proof

Choose a bounded-below injective resolution $F\to I^\bullet$
as in [def-weil-pbc-kinjective-resolutions].
For the closed immersion $i:B\hookrightarrow T$, the
[def-pur-flasque-support] functor $i^!$ is right adjoint to
the exact functor $i_*$; hence $i^!$ preserves injectives.
The functor $i_*$ also preserves injectives, since it is right
adjoint to the exact restriction $i^*$.
Consequently $\mathcal G_BI=i_*i^!I$ is injective whenever $I$
is injective. An injective sheaf has surjective restriction of
sections to an open subset: apply its lifting property to the
monomorphism from the free module sheaf of that open subset to
the constant free module sheaf.
Restriction to $V$ is exact and commutes with the support kernel,
so

$$
(\mathcal G_BI)|_V=\mathcal G_{B\cap V}(I|_V).
$$

The kernel of the resulting surjection
$\Gamma_B(T,I)\to\Gamma_{B\cap V}(V,I|_V)$ consists precisely of
sections supported on both $B$ and $C$, namely
$\Gamma_{B\cap C}(T,I)$.
This gives a short exact sequence of complexes of sections.
By the exactness of extension by zero in
[def-weil-open-closed-recollement], the restriction $v^*$
preserves injectives. Thus all three complexes compute the
derived support functors of [def-pur-support-cohomology].
The cone triangle of the short exact sequence proves the assertion.
All maps come from support inclusion and restriction, so the
comparison theorem for injective resolutions makes the triangle
natural in $F$.
