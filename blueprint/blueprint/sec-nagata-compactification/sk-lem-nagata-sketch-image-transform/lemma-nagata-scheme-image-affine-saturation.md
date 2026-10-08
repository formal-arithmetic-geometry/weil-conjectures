+++
id = "lemma-nagata-scheme-image-affine-saturation"
kind = "lemma"
title = "Affine scheme-image saturation"
order = 231
uses = ["def-nagata-power-torsion", "lemma-nagata-power-torsion-kernel-localization", "lemma-nagata-strict-transform-closure-characterization"]
+++
Let $C\to B$ be a ring map, let $K=\ker(C\to B)$, and let $a\in C$ map
to a unit of $B$. Put $C_a=C[1/a]$. If $C/K\to B$ is injective, then

$$
\ker(C\longrightarrow C_a\longrightarrow B)
=\{c\in C\mid \exists n,\ a^nc\in K\},
$$

and this kernel is the inverse image of
$\Gamma_{(a)}(C/K)$ under $C\to C/K$.
Consequently the scheme-theoretic image of the induced map from $B$ on an
$a$-chart is the quotient by the $a$-power torsion, i.e. the strict-transform
chart of the scheme-theoretic image of $\operatorname{Spec}(B)\to \operatorname{Spec}(C)$.

## Proof

If $c$ maps to zero in $B$, then its image in $C_a/KC_a$ is zero because
$C/K\to B$ is injective. The localization criterion gives
$a^nc\in K$ for some $n$. Conversely, such an equality maps to zero in $B$
because $a$ is a unit there. This proves the displayed kernel equality.
On a standard blow-up chart replace $C$ by $C_a(A,B,I)$ and $a$ by the
chart equation. The quotient by the displayed kernel is exactly the
quotient by $\Gamma_{(a)}$; the affine strict-transform formula and the
closure characterization identify it with the strict-transform chart.
