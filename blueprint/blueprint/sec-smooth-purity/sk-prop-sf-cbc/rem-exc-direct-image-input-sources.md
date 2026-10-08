+++
id = "rem-exc-direct-image-input-sources"
kind = "remark"
title = "Sources of the direct-image input, and its proof here"
order = 1646
uses = ["lem-kun-cd-sep-closed-point", "obl-fin-comparison", "sbc-thm-finiteness-finite-type", "thm-dg-finite-type-constructibility", "thm-sc-finite-type-torsion-cd"]
+++
Clause (1) is the classical finiteness theorem for the higher direct
images of a constructible sheaf under a morphism of finite type of
Noetherian schemes, SGA IV, Exposé XIV, Th. 1.1 (Stacks Project, Theorem 63.14.5, [Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0), the proper case being $Rf_!=Rf_*$); its compact-support
form for a separated morphism of finite presentation is Stacks Project,
More Etale Cohomology, Theorem 63.14.5,
[Tag `0GL0`](https://stacks.math.columbia.edu/tag/0GL0). It
is proved in this blueprint as
[thm-dg-finite-type-constructibility] of the constructibility chapter, by Deligne's
finite-boundary induction: the open-immersion case is reduced to smooth
morphisms with locally constant coefficients, which are treated by duality
from the compact-support theory and not by an appeal to constructibility of
the ordinary direct image itself, and the general finite-type case is
assembled from the open-immersion and proper cases by a finite alternating
Cech resolution. The proper case is the comparison theorem
[obl-fin-comparison], and the resulting finite-type statement is
[sbc-thm-finiteness-finite-type], whose earlier circular
open-immersion argument is thereby superseded.

Clause (2) is the cohomological-dimension bound of a finite-type scheme
over a separably closed field: the affine case is Stacks Project, Etale
Cohomology, Proposition 59.95.6,
[Tag `0F0V`](https://stacks.math.columbia.edu/tag/0F0V), and
the general case Stacks Project, Etale Cohomology, Section 59.95,
[Tag `0F0P`](https://stacks.math.columbia.edu/tag/0F0P). It is
proved in this blueprint as [thm-sc-finite-type-torsion-cd] of
the Jacobian chapter, from the affine bound for arbitrary torsion sheaves and the
comparison of the etale and Zariski topologies, with the vanishing of the
torsion cohomological dimension of a separably closed field as the base
case ([lem-kun-cd-sep-closed-point]).

Consequently both clauses hold over every separably closed field, which is
the form used below: [thm-exc-direct-image-input-holds].
