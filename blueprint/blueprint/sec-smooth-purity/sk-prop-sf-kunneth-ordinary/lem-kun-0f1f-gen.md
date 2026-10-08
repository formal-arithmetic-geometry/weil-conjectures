+++
id = "lem-kun-0f1f-gen"
kind = "lemma"
title = "Global generation for sheaves supported on closed points"
order = 1767
uses = ["def-kun-global-generated", "def-kun-separably-closed", "def-weil-pbc-direct-image", "lem-kun-03qu-global-generation", "lem-kun-04ca", "lem-kun-closed-point-field", "lem-kun-colim-gbl-gen", "lem-kun-cp-approximation", "lem-kun-global-generated-stalkwise", "lemma-weil-pbc-finite-stalk-formula"]
+++
Let $K$ be a separably closed
field and $X$ a scheme of finite type over $K$. Let $F$ be an
abelian sheaf on $X_{\Et}$ whose support is contained in the set of
closed points of $X$. Then $F$ is
globally generated.
(*Source:* Stacks Project, Tag
[0F1F](https://stacks.math.columbia.edu/tag/0F1F), second
assertion.)

## Proof

As in the preceding proof, $X$ is Noetherian and
[lem-kun-cp-approximation] gives a presentation
$F=\varinjlim_iF_i$ by finitely generated subsheaves, the support of
$F_i$ being a finite set $Z_i$ of closed points of $X$; after
giving $Z_i$ its reduced structure, [lem-kun-04ca] writes
$F_i=i_*\mathcal G_i$ for the finite closed immersion
$i:Z_i\to X$.

We claim the evaluation map

$$
\operatorname{ev}_i:\bigoplus_{s\in H^0(X_{\Et},F_i)}
\underline{\mathbf Z}\longrightarrow F_i
$$

of [def-kun-global-generated] is surjective. A geometric stalk
away from $Z_i$ is zero. At a geometric point over
$z\in Z_i$, the finite-direct-image stalk formula
[lemma-weil-pbc-finite-stalk-formula] identifies the target with
the corresponding stalk of $\mathcal G_i$ on
$\Spec(\kappa(z))$. The residue field $\kappa(z)$ is a finite
purely inseparable extension of the separably closed field $K$,
hence is separably closed by
[lem-kun-closed-point-field]; therefore
[lem-kun-03qu-global-generation] identifies the sections over
the component $\Spec(\kappa(z))$ with that stalk. Since
$H^0(X_{\Et},F_i)=H^0((Z_i)_{\Et},\mathcal G_i)$ by
[def-weil-pbc-direct-image] (and $\Gamma$ of a disjoint union
is the product of the global sections), every element of the target
stalk is the germ of a global section, so
$(\operatorname{ev}_i)_{\bar z}$ is surjective. Thus $F_i$ is
globally generated in the sense of
[lem-kun-global-generated-stalkwise]. Finally
[lem-kun-colim-gbl-gen] shows that the filtered colimit $F$ is
globally generated.
