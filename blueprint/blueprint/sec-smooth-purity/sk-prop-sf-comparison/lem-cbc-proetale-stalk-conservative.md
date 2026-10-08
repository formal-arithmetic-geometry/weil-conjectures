+++
id = "lem-cbc-proetale-stalk-conservative"
kind = "lemma"
title = "Detecting isomorphisms on the pro-etale site"
order = 1650
uses = ["def-weil-pbc-ind-etale-basis", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-site", "def-weil-pbc-site-comparison-morphism", "lem-weil-pbc-ind-etale-basis", "lemma-weil-pbc-geometric-stalk-conservative", "thm-weil-pbc-site-comparison"]
+++
Let $\Lambda$ be a finite discrete ring and let $T$ be a scheme.

1. *locality for covering families.* A morphism
$F\to G$ of complexes of $\Lambda$-module sheaves on
$T_{\Proet}$ is an isomorphism if and only if its inverse image
along every member of one
pro-etale covering family
of $T$ is an isomorphism. Equivalently: a complex on
$T_{\Proet}$ is acyclic if and only if its cohomology sheaves
vanish, and a sheaf on $T_{\Proet}$ vanishes if and only if it
vanishes after inverse image along the members of a covering family.
1. *detection on the affine ind-etale basis.* For affine
$T$, a sheaf on $T_{\Proet}$ vanishes if and only if its sections
on every object of the affine ind-etale basis
[def-weil-pbc-ind-etale-basis] vanish; consequently a morphism
of complexes on $T_{\Proet}$ is an isomorphism if and only if it
induces a quasi-isomorphism of sections on every object of that
basis. For general $T$ the same holds with the bases of the
members of an affine open cover.
1. *complexes of etale origin.* Let
$\nu_T:T_{\Proet}\to T_{\Et}$ be the comparison morphism of
[def-weil-pbc-site-comparison-morphism] and let
$F'\to G'$ be a morphism of bounded-below complexes of etale
$\Lambda$-sheaves. Then $\nu_T^*F'\to\nu_T^*G'$ is an
isomorphism if and only if it is an isomorphism at every geometric
point of $T$. In particular the geometric-point stalks are
jointly conservative on the bounded constructible objects
$\Dbc(T_{\Proet},\Lambda)$, which are of etale origin by
[def-weil-pbc-proetale-modules].
1. *warning.* None of this extends to arbitrary pro-etale
sheaves: the collection of geometric-point stalks is *not*
conservative on $\Sh(T_{\Proet})$. For
$T=\operatorname{Spec}k$ with $k$ algebraically closed and a
nonzero abelian group $A$, the sheafified quotient of functions
modulo locally constant functions, $\mathcal F(U)=\{\text{functions } U\to A\}/\{\text{locally constant functions}\}$, has
$\mathcal F(T)=0$ while $\mathcal F\neq0$, the site
$T_{\Proet}$ containing affine objects with infinitely many points
(Stacks Project, Pro-étale Cohomology, Section 61.18,
[Tag 0991](https://stacks.math.columbia.edu/tag/0991)).

## Proof

*Step 1 (clause (1)).* A morphism of complexes is an
isomorphism if and only if its cone is acyclic, and a complex is
acyclic if and only if all its cohomology sheaves vanish: this is the
definition of the derived category of
[def-weil-pbc-proetale-modules] as the localization at the
quasi-isomorphisms. Vanishing of a sheaf is a local condition for the
topology. Indeed, if $\mathcal H$ is a sheaf on $T_{\Proet}$ whose
inverse images along the members of a covering family vanish, then for
every object $V$ the sheaf axiom presents $\mathcal H(V)$ as the
equalizer of two maps between products of groups
$\mathcal H(V\times_TU_i)$ that are zero, the family being a
covering; hence $\mathcal H(V)=0$, and the converse is functoriality
of inverse image. Applying this to the cohomology sheaves of the cone
gives the equivalence of the first sentence.

*Step 2 (clause (2)).* This is
[lem-weil-pbc-ind-etale-basis]: restriction to the affine
ind-etale basis of [def-weil-pbc-ind-etale-basis] determines a
sheaf and its morphisms uniquely and detects isomorphisms of sheaves.
Restriction of a complex is exact and degreewise, so a morphism of
complexes is a quasi-isomorphism if and only if its restriction is
one. A general $T$ is covered by its affine opens, and clause (1)
reduces the statement to the affine case.

*Step 3 (clause (3)).* Let $\mathcal G'$ be a bounded-below
complex of etale $\Lambda$-sheaves. The etale neighbourhoods of a
geometric point $\bar t$ of $T$ are cofinal among its weakly etale
neighbourhoods, by [def-weil-pbc-proetale-site] and
[def-weil-pbc-site-comparison-morphism], the inverse image of the
comparison morphism being computed on the common objects; hence
$(\nu_T^*\mathcal G')_{\bar t}=\mathcal G'_{\bar t}$, naturally in
$\mathcal G'$. If $\nu_T^*F'\to\nu_T^*G'$ is an isomorphism at
every geometric point, then $F'\to G'$ is an isomorphism at every
geometric point, hence an isomorphism by
[lemma-weil-pbc-geometric-stalk-conservative]; applying the functor
$\nu_T^*$ exhibits $\nu_T^*F'\to\nu_T^*G'$ as an isomorphism. The
converse follows from functoriality. For bounded-below complexes one
applies this degreewise to the cohomology sheaves, inverse image being
exact and the identification of stalks being natural. The final
assertion of the clause is the definition: the bounded constructible
objects of [def-weil-pbc-proetale-modules] are by definition the
pullbacks of the bounded constructible etale objects. Full
faithfulness of $\nu_T^*$ on bounded-below complexes,
[thm-weil-pbc-site-comparison], is not needed for this argument,
but it shows that the etale model of a morphism of etale origin is
unique.

*Step 4 (clause (4)).* The replacement for the false general
statement is the displayed reference. Concretely, on
$T=\operatorname{Spec}k$ the single geometric point of $T$ is the
only point of the small pro-etale site that comes from a strictly
henselian local ring, while the site contains the affine objects
$U=\operatorname{Spec}(\operatorname{colim}\operatorname{Map}(E_n,k))$
for $E=\varprojlim E_n$ an inverse limit of finite sets with
surjective transition maps; such a $U$ is ind-Zariski, hence weakly
etale, over $k$ and has infinitely many points, so the sheaf
$\mathcal F$ of the statement has a nonzero value there while
$\mathcal F(T)=0$. No clause of this lemma asserts conservativity
of geometric-point stalks beyond clause (3), and clause (3) confines
the failure to complexes that are not of etale origin.
