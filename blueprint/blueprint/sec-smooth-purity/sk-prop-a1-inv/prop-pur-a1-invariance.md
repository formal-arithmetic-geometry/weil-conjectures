+++
id = "prop-pur-a1-invariance"
kind = "theorem"
title = "Invariance along the affine line"
order = 1961
tags = ["latex:proposition"]
uses = ["def-pur-conventions", "def-weil-derived-cohomology-sheaves", "def-weil-derived-pullback-tensor-hom", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-pur-a1-components", "lem-pur-lisse-uniqueness"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $Y$ be a separated finite-type $k$-scheme, let
$a:\mathbf A^1_Y\to Y$ be the projection, and let
$i_0,i_1:Y\to\mathbf A^1_Y$ be the sections $t=0$ and $t=1$, so that
$a\circ i_0=a\circ i_1=\operatorname{id}_Y$ and hence
$i_0^*a^*\cong\operatorname{id}\cong i_1^*a^*$. Let
$F\in D^b_{ctf}(\mathbf A^1_Y,\Lambda)$ and
$C\in D^b_{ctf}(Y,\Lambda)$, and let
$\theta:i_1^*F\xrightarrow{\sim}C$ be an isomorphism. Suppose given an
etale covering family $\{u_\alpha:Y_\alpha\to Y\}$ by separated
finite-type schemes such that:

- *local shape.* for every $\alpha$ the restriction
$F|_{\mathbf A^1_{Y_\alpha}}$ is a shift and twist
$\mathcal L_\alpha(m_\alpha)[n_\alpha]$ of a finite locally
constant $\Lambda$-sheaf $\mathcal L_\alpha$ of rank one on
$\mathbf A^1_{Y_\alpha}$;
- *normalized local comparisons.* for every $\alpha$ there is an
isomorphism
$\kappa_\alpha:F|_{\mathbf A^1_{Y_\alpha}}\xrightarrow{\sim}
a^*C|_{\mathbf A^1_{Y_\alpha}}$ whose restriction along the section
$t=1$ is $\theta|_{Y_\alpha}$, i.e.
$i_1^*\kappa_\alpha=\theta|_{Y_\alpha}$ under
$i_1^*a^*C\cong C$.

Then:

1. *gluing.* There is a unique isomorphism
$\kappa:F\xrightarrow{\sim}a^*C$ with
$\kappa|_{\mathbf A^1_{Y_\alpha}}=\kappa_\alpha$ for every
$\alpha$.
1. *uniqueness.* $\kappa$ is the unique isomorphism
$F\xrightarrow{\sim}a^*C$ with $i_1^*\kappa=\theta$; in
particular it does not depend on the cover or on the local
comparisons $\kappa_\alpha$.
1. *constancy.* Restriction along $i_0$ and $i_1$ gives a
canonical identification
$$
i_0^*F\xrightarrow{\ i_0^*\kappa\ }i_0^*a^*C\cong C
\cong i_1^*a^*C\xleftarrow{\ i_1^*\kappa\ }i_1^*F,
$$
the right-hand map being $\theta$: the object $F$ is constant
along the $\mathbf A^1$-direction, its values at $t=0$ and
$t=1$ agreeing.

## Proof

Throughout, pullback along an etale morphism, restriction to an
open subscheme, and the pullbacks $i_0^*,i_1^*,a^*$ are the exact
derived pullbacks of [def-weil-derived-pullback-tensor-hom]; they
commute with the cohomology sheaves of
[def-weil-derived-cohomology-sheaves] and with one another up to the
canonical isomorphisms, which are used without comment. The base
changes $\{\mathbf A^1_{Y_\alpha}\to\mathbf A^1_Y\}$ of the given
cover form again an etale covering family, hence a covering family
of the site of [def-weil-pbc-proetale-site], etale morphisms being
weakly etale ([def-weil-scheme-morphism-properties]).

Step 1: reduction to one shift. For a point $y\in Y$ and an index
$\alpha$ with $y$ in the image of $u_\alpha$, the object $F$ has, at
every geometric point of $\mathbf A^1_Y$ over $y$, nonzero
cohomology in exactly the degree $-n_\alpha$, because
$\mathcal L_\alpha(m_\alpha)$ is a sheaf with nonzero stalks
(rank one, and a twist of a finite locally constant rank-one sheaf
is again one, as $\Lambda(m)$ is invertible in the conventions of
[def-pur-conventions]). Hence $n(y):=n_\alpha$ is independent of
$\alpha$, and it is constant on the image of each connected component
of $Y_\alpha$, an open subset of $Y$ since etale morphisms are open.
So $n:Y\to\mathbf Z$ is locally constant. The scheme $Y$ is Noetherian,
so it is the finite disjoint union of its connected components $Y_c$,
which are open and closed, and $n$ is constant on each of them; by
[lem-pur-a1-components](1) the connected components of
$\mathbf A^1_Y$ are the $\mathbf A^1_{Y_c}$. All data in the statement
restrict to each $Y_c$, and a morphism over $\mathbf A^1_Y$ (resp.
$Y$) is the same as a family of morphisms over the open and closed
pieces $\mathbf A^1_{Y_c}$ (resp. $Y_c$). We may therefore assume
that $n_\alpha=n$ for all $\alpha$ and a fixed integer $n$.

Step 2: reduction to sheaves. With $n$ fixed, the cohomology sheaves
$\mathcal H^q(F)$ vanish for $q\neq-n$ after restriction to every
member of a covering family, hence vanish, a sheaf which vanishes
locally being zero; and
$\mathcal L:=\mathcal H^{-n}(F)$ restricts on
$\mathbf A^1_{Y_\alpha}$ to $\mathcal L_\alpha(m_\alpha)$, so it is a
finite locally constant sheaf of rank one. The truncations of
the standard t-structure of [def-weil-derived-cohomology-sheaves]
then identify $F$ with $\mathcal L[n]$, a complex with a single
nonzero cohomology sheaf being isomorphic to that sheaf placed in its
degree. Likewise $C|_{Y_\alpha}\cong i_1^*a^*C|_{Y_\alpha}
\cong i_1^*F|_{Y_\alpha}$ via $\kappa_\alpha$ and $\theta$, so $C$
has the single nonzero cohomology sheaf
$\mathcal M:=\mathcal H^{-n}(C)$, again finite locally constant of
rank one, and $C\cong\mathcal M[n]$,
$a^*C\cong(a^*\mathcal M)[n]$. Morphisms in the derived category
between two objects concentrated in the single degree $-n$ are the
morphisms of the corresponding sheaves, the heart of the standard
t-structure being the abelian category of sheaves. Thus
$\kappa_\alpha$ and $\theta$ are, after the shift $[n]$ is removed,
isomorphisms of finite locally constant sheaves
$$
\kappa_\alpha:\mathcal L|_{\mathbf A^1_{Y_\alpha}}\xrightarrow{\sim}
a^*\mathcal M|_{\mathbf A^1_{Y_\alpha}},
\qquad
\theta:i_1^*\mathcal L\xrightarrow{\sim}\mathcal M,
$$
and everything to be proved is a statement about morphisms of
sheaves; no descent of objects or morphisms of a derived category
is used.

Step 3: agreement on the overlaps. Put
$Y_{\alpha\beta}=Y_\alpha\times_YY_\beta$, a separated finite-type
$k$-scheme, and restrict $\kappa_\alpha$ and $\kappa_\beta$ to
$\mathbf A^1_{Y_{\alpha\beta}}$. Their restrictions along the unit
section both equal $\theta|_{Y_{\alpha\beta}}$. By the second
assertion of [lem-pur-lisse-uniqueness], applied over the base
$Y_{\alpha\beta}$ to the restrictions of the two sheaf morphisms to
$\mathbf G_{m,Y_{\alpha\beta}}$, through which the unit section
factors, they agree on $\mathbf G_{m,Y_{\alpha\beta}}$; by the first
assertion of the same lemma they then agree on all of
$\mathbf A^1_{Y_{\alpha\beta}}$.

Step 4: gluing, and (1). Morphisms of sheaves form a sheaf
$\mathcal Hom(\mathcal L,a^*\mathcal M)$ on the site, so by Step 3
the $\kappa_\alpha$ glue to a unique morphism
$\kappa:\mathcal L\to a^*\mathcal M$ restricting to each
$\kappa_\alpha$. The inverses $\kappa_\alpha^{-1}$ agree on overlaps
as well, and glue to a two-sided inverse of $\kappa$, since the
composites restrict to identities on every member of the cover. Hence
$\kappa$ is an isomorphism; shifting back by $[n]$ gives (1).

Step 5: (2) and (3). The restriction $i_1^*\kappa$ and $\theta$ are
two morphisms $i_1^*\mathcal L\to\mathcal M$ of sheaves on $Y$ which
agree after restriction to every $Y_\alpha$, by the normalization of
$\kappa_\alpha$; hence they are equal. If
$\kappa':F\xrightarrow{\sim}a^*C$ is another isomorphism with
$i_1^*\kappa'=\theta$, then, by Step 2 applied to $\kappa'$, both are
sheaf morphisms $\mathcal L\to a^*\mathcal M$ after the shift is
removed; their restrictions to $\mathbf G_{m,Y}$ agree along the unit
section, hence agree by the second assertion of
[lem-pur-lisse-uniqueness], and then $\kappa'=\kappa$ by its first
assertion. This proves (2); in particular two covers with normalized
local comparisons produce the same $\kappa$, both having restriction
$\theta$ at $t=1$. For (3), apply $i_0^*$ and $i_1^*$ to $\kappa$
and use $a\circ i_0=a\circ i_1=\operatorname{id}_Y$; the resulting
identification $i_0^*F\cong C\cong i_1^*F$ is canonical because
$\kappa$ is, by (2).
