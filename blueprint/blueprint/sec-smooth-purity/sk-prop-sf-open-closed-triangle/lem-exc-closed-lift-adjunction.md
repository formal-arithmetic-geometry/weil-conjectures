+++
id = "lem-exc-closed-lift-adjunction"
kind = "lemma"
title = "Adjunction for the ind-etale closed lift"
order = 1842
uses = ["def-exc-ind-etale-closed-lift", "def-weil-pbc-ind-etale-algebra", "lem-exc-closed-lift-filtered", "lem-exc-closed-lift-reduction"]
+++
For every ind-etale $A$-algebra $D$, reduction induces a natural bijection
$$
 \operatorname{Hom}_A(D,H_A(\overline C))
 \xrightarrow{\sim}
 \operatorname{Hom}_{A/I}(D/ID,\overline C).
$$
This identifies $H_A$ as right adjoint to reduction on ind-etale algebras.

## Proof

First let $D$ be etale of finite presentation. A map $D/ID\to\overline C$
makes $D$ an object of [def-exc-ind-etale-closed-lift], hence gives its
canonical map to the colimit. Conversely any $D\to H_A(\overline C)$ factors
through a stage $B$, by finite presentation and
[lem-exc-closed-lift-filtered]. If its reduction is the specified map, this
factorization $D\to B$ is a morphism in the indexing category. The colimit
relation then identifies it with the canonical map from the object $D$. This
proves uniqueness as well as existence.

For general $D=\varinjlim D_a$, apply this bijection to every $D_a$. The
unique lifts commute with all transition maps, so pass to a unique map from
$D$. This proves the bijection and its naturality. The reduction isomorphism
of [lem-exc-closed-lift-reduction] is its adjunction counit. This supplies
the adjunction, including uniqueness, in [Stacks Project, Tag
097P](https://stacks.math.columbia.edu/tag/097P).
