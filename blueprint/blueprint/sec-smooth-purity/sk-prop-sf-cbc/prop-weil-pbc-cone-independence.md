+++
id = "prop-weil-pbc-cone-independence"
kind = "theorem"
title = "Compatibility and independence of common-stage cones"
order = 1539
uses = ["def-weil-pbc-common-stage-cones", "def-weil-pbc-finite-stage-pair-category", "prop-weil-pbc-common-stage-calculus", "prop-weil-pbc-scalar-extension"]
tags = ["latex:proposition"]
+++
If $M\subset N$, exactness of $T_{N/M}$ identifies the scalar extension of a
cone triangle for $u$ with a cone triangle for $u_N$. If two representatives
define the same morphism of $\mathcal P_T$, their cone triangles become
isomorphic after passage to a field where the representatives agree. Any two
cone triangles selected for one finite-stage morphism are isomorphic by a
morphism of triangles whose first two components are identities. Thus
distinguishedness in [def-weil-pbc-common-stage-cones] is independent of
every representative, common field, and cone choice.

*Source note:* no Stacks Project entry states this independence: the
blueprint adds the proof that distinguishedness of a common-stage triangle
is independent of the representative, the common field and the chosen cone,
which is what makes the pair category a triangulated category below. The
fixed-category input is Stacks': Lemma 13.4.7 ([Tag
014B](https://stacks.math.columbia.edu/tag/014B), fetched and quoted) states
that a morphism $f:X\to Y$ of a pre-triangulated category has a
distinguished triangle $(X,Y,Z,f,g,h)$ unique up to (nonunique) isomorphism
of triangles, more precisely that a second such triangle is related to the
first by an isomorphism $(1,1,c)$ — exactly the assertion that two cone
triangles are isomorphic by a morphism of triangles with identity on source
and target — with Lemma 13.4.3 ([Tag
014A](https://stacks.math.columbia.edu/tag/014A), if two of the three
components of a morphism of distinguished triangles are isomorphisms so is
the third). Difference: 014B is internal to one pre-triangulated category,
whereas the blueprint must also compare the cone triangles of the scalar
extensions $T_{N/M}$ and of different representatives of one morphism of
$\mathcal P_T$.

## Proof

For $M\subset N$, the functor $T_{N/M}$ of
[prop-weil-pbc-scalar-extension] is exact and its shift comparison carries
the cone triangle for $u$ in $\mathcal C_M$ to a distinguished triangle of
$\mathcal C_N$ which is a cone triangle for $u_N$, identifying the scalar
extension of the first with a cone triangle of the second. If
$(M,u)\sim(N,v)$, then $u_P=v_P$ for some finite $P$, and transporting the
two cone triangles to $P$ via the transport of
[prop-weil-pbc-common-stage-calculus] and the $\sigma$-comparisons of
[prop-weil-pbc-scalar-extension] makes them isomorphic over $P$ by the
finite-stage axiom TR3, with identity components on the common source and
target; any two cone triangles selected for one finite-stage morphism are
isomorphic by a morphism of triangles whose first two components are
identities (the finite-stage uniqueness of cones up to noncanonical
isomorphism). Combining these facts, distinguishedness in
[def-weil-pbc-common-stage-cones] is independent of the representative, of
the common field and of the cone choice, in the sense of the category of
[def-weil-pbc-finite-stage-pair-category].
