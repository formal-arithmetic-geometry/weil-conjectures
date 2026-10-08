+++
id = "lem-weil-pbc-cech-criterion"
kind = "lemma"
title = "Injectives and the Cech acyclicity criterion"
order = 1282
uses = ["def-weil-pbc-cover-cech", "def-weil-pbc-etale-cohomology"]
+++
On a site with a basis closed under fibre products, suppose every covering of
a basis object has a finite basis refinement. An injective module sheaf has
vanishing positive Cech cohomology [def-weil-pbc-cover-cech] for every finite
basis covering. If a module sheaf $M$ has this same vanishing for every such
covering, then $H^q(U,M)=0$ for every basis object $U$ and $q>0$, where
cohomology is derived sections.

## Proof

For a covering $V=\coprod_aV_a\to U$, form the augmented complex of free
module sheaves on $V^{p+1}_U$, ending in the free module sheaf on $U$. It is
exact: locally on a test object mapping to $U$, the cover has a lift to $V$.
Insert that lift as first coordinate. The alternating-face differential
satisfies $\partial h+h\partial=1$, since adjacent inserted faces cancel. A
local chain has finite support, so one common cover suffices for all its
generators. Applying $\operatorname{Hom}(-,I)$ for an injective sheaf $I$
gives the augmented complex of [def-weil-pbc-cover-cech], which is
consequently exact. This argument uses local lifts, not a choice of points of
the topos.

Embed $M$ into an injective $I$ and put $Q=I/M$. A section of $Q(U)$ lifts to
$I$ on a finite basis cover. Differences of these lifts form a Cech
one-cocycle in $M$. Its vanishing in $\check H^1$ lets us adjust the lifts by
sections of $M$ so that they agree. They then glue in $I$. Thus $I(U)\to
Q(U)$ is surjective for every basis object. This yields a short exact
sequence of Cech complexes on every basis covering, including all its
intersections. The first paragraph and the assumed vanishing for $M$ imply
the same positive Cech vanishing for $Q$. Repeat with an injective embedding
of $Q$. The long exact sequences for derived sections give $H^1(U,M)=0$ and
$H^q(U,M)=H^{q-1}(U,Q)$ for $q>1$. Iteration proves the assertion in every
finite degree. This is the Cech acyclicity criterion of
[Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9), with
its dimension-shifting proof included.
