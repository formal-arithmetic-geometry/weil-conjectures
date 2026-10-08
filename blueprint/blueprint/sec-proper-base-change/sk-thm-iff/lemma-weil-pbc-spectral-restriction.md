+++
id = "lemma-weil-pbc-spectral-restriction"
kind = "lemma"
title = "Zariski restriction on a spectral space"
order = 1075
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions"]
+++
If $T$ is spectral, $T_0\subseteq T$ is closed, and every irreducible closed
subset $C\subseteq T$ has $C\cap T_0$ connected and nonempty, then for every
abelian sheaf $F$ on $T$ the restriction $\Gamma(T,F)\to\Gamma(T_0,F|)$ is a
bijective map.

## Proof

Injectivity is pointwise. If $s\in\Gamma(T,F)$ restricts to zero, its germ
vanishes at every point of $T_0$. The zero-germ locus is open and stable under
generization. If its complement contained $x$, then the irreducible closed
$C=\overline{\{x\}}$ would meet $T_0$; the specialization map from the germ
at the generic point of $C$ to the germ at $x$ would force the latter to be
zero, a contradiction.

For surjectivity, write $F$ as the filtered colimit of subsheaves generated
by finitely many sections on quasi-compact opens. Restriction to $T_0$ and
both section functors commute with this filtered colimit, so it is enough to
handle one finitely generated subsheaf. Such a subsheaf embeds into a finite
product

$$
F\hookrightarrow\prod_{b=1}^r(i_b)_*\underline{M_b},
$$

with $i_b:C_b\hookrightarrow T$ closed and $M_b$ finite: the finite germs of
the chosen generators determine finitely many closed equalizer loci, and the
corresponding finite value sets give the displayed embedding. If $F\subseteq G$, the injectivity already proved gives

$$
\Gamma(T,F)=\Gamma(T_0,F|_{T_0})\cap\Gamma(T,G)
\subseteq\Gamma(T_0,G|_{T_0}).
$$

Thus it suffices to extend sections of one finite constant pushforward.

For $i:C\hookrightarrow T$ closed, the condition on irreducible closures is
inherited by $C$. A section of $\underline M$ on $C\cap T_0$ is constant on
each connected component. Every component of $C$ meets its closed subset,
and that intersection is connected by hypothesis, so the same constant gives
a unique section on the component. These componentwise sections agree on
quasi-compact overlaps and glue by the sheaf equalizer; pushing forward gives
the extension on $T$. Finite products, subobjects, and the filtered colimit
then give an extension for $F$. The stalkwise injectivity proves uniqueness,
so restriction is bijective. This is the expanded spectral argument at Tag
`09ZG`; no etale lifting is used.

## Detailed form

Let $T$ be spectral [def-weil-pbc-scheme-conventions] and $T_0\subset T$
closed. Suppose every irreducible closed subset $C\subset T$ meets $T_0$ in a
nonempty connected subset. Then restriction is a bijection

$$
  \Gamma(T,F)\xrightarrow{\sim}\Gamma(T_0,F|_{T_0})
$$

for every sheaf of abelian groups $F$ on the Zariski space $T$ which is
locally constant [def-weil-pbc-etale-sheaves], i.e. locally isomorphic to a
constant sheaf. The hypothesis on $F$ cannot be dropped: for $T=\mathbf
A^1_k$, $T_0=\{0\}$ and $F$ the skyscraper sheaf at a closed point $y\neq0$
one has $\Gamma(T,F)\neq0$ and $\Gamma(T_0,F|_{T_0})=0$.

## Proof

*Step 1: the zero locus of a section is clopen.* Let $s\in\Gamma(T,F)$ and
let $Z(s)\subseteq T$ be the set of points at which the germ of $s$ vanishes.
On an open $V$ on which $F$ is isomorphic to a constant sheaf the section
$s|_V$ corresponds to a locally constant function $V\to A$, whose zero locus
is therefore open and closed in $V$; since $T$ is covered by such $V$, the
set $Z(s)$ is open and closed in $T$.

*Step 2: injectivity.* If $s|_{T_0}=0$, then $T_0\subseteq Z(s)$. Let
$C\subseteq T$ be an irreducible closed subset. Then $C\cap Z(s)$ and
$C\setminus Z(s)$ are open in $C$ and disjoint, and $C\cap T_0\neq\emptyset$
with $C\cap T_0\subseteq C\cap Z(s)$ shows that $C\cap Z(s)\neq\emptyset$; by
irreducibility of $C$ one of the two open subsets is empty, so $C\subseteq
Z(s)$. Every point of $T$ lies in the irreducible closed set
$\overline{\{x\}}$, so $Z(s)=T$ and $s=0$.

*Step 3: surjectivity.* Let $t\in\Gamma(T_0,F|_{T_0})$. By Step 1 applied to
the locally constant sheaf $F$, each point of $T_0$ has an open neighbourhood
$V$ with $F|_V\cong\underline A$ and, after shrinking, with $t|_{V\cap T_0}$
the restriction of the constant section of $\underline A$ determined by the
germ of $t$ at a point of $V\cap T_0$; such a point exists because
$\overline{\{y\}}$ meets $T_0$ for every $y\in V$, by the hypothesis applied
to the irreducible closed set $\overline{\{y\}}$. The neighbourhoods $V$ so
obtained and the open set $T\setminus T_0$ cover $T$; on an intersection of
two of them the two extending sections agree on the part lying over $T_0$,
and by Step 1 applied to the difference of the two extensions they agree
everywhere on the intersection, because the difference vanishes on a closed
set meeting every irreducible closed subset of the intersection. The
extensions therefore glue to a section $s\in\Gamma(T,F)$ with $s|_{T_0}=t$.

*Step 4: constants.* For a constant sheaf $\underline A$ the statement is
immediate, since a nonempty spectral space has global sections $A$ and $T_0$
is nonempty by the hypothesis applied to $T$ itself. This is the case used in
the applications below.
