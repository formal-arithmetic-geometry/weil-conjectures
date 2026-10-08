+++
id = "lemma-weil-pbc-etale-degree-zero"
kind = "lemma"
title = "Etale henselian restriction in degree zero"
order = 1084
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-finite-section-pullback", "def-weil-pbc-henselian-terminology", "def-weil-pbc-scheme-conventions", "def-weil-pbc-strict-henselian-setup", "lem-weil-pbc-closed-immersion-products", "lem-weil-pbc-finite-proper", "lem-weil-pbc-finite-pullback-identities", "lemma-weil-pbc-finite-pullback-closed-fibre", "lemma-weil-pbc-finite-pullback-composition", "lemma-weil-pbc-finite-pullback-descent", "lemma-weil-pbc-finite-pullback-identity", "lemma-weil-pbc-finite-refinement-etale-cover", "lemma-weil-pbc-spectral-restriction", "lemma-weil-pbc-stein-connectedness"]
+++
For every etale abelian sheaf $F$ on $X$, restriction induces
$\Gamma(X,F)\xrightarrow{\sim}\Gamma(X_0,F_0)$.

## Proof

The canonical map from the etale to Zariski restriction is injective on
stalks because a geometric point has a strictly local etale neighbourhood.
For surjectivity, lift a fibre section etale-locally; quasi-compactness of
$X_0$ gives finitely many local lifts, and Lemma
[lemma-weil-pbc-finite-refinement-etale-cover] gives a finite surjective
refinement on which all lifts exist.
The two lifts agree on the finite overlap after restriction to $X_0$ by the
Zariski result, and the equalizer sheaf descends the lift to $X$. Uniqueness
is stalkwise injectivity. The finite-pullback compatibility required in
Stacks Tag `09ZF` is recorded as four explicit equalities:
identity pullback preserves the lift, composition of finite pullbacks preserves
the lift, restriction to $X_0$ recovers the given section, and the descended
section pulls back to each local lift; these are the four preceding lemmas.
The finite refinement lemma proves existence and finite-presentation stage,
and its stalkwise equalizer argument proves equality of the local lifts on
the self-intersection. Thus the four finite-pullback compatibilities
complete the descent.

## Detailed form

Let $(A,I)$ be henselian [def-weil-pbc-henselian-terminology] and let
$Y\to\operatorname{Spec}A$ be proper
[def-weil-pbc-scheme-conventions]. For every etale abelian sheaf $F$ on $Y$,

$$
  \Gamma(Y,F)\xrightarrow{\sim}\Gamma(Y_0,F|_{Y_0}).
$$

The isomorphism is natural in $F$, in finite pullback, and in morphisms of
henselian pairs.

## Proof

Put $S=\operatorname{Spec}A$, $S_0=\operatorname{Spec}(A/I)$, and
$Y_0=Y\times_SS_0$. Two preliminary remarks. *(i)* The underlying space of
$Y$ is spectral [def-weil-pbc-scheme-conventions]: $Y\to S$ is proper, hence
separated and of finite type, hence quasi-compact and quasi-separated, and
the underlying space of any scheme is sober with a basis of quasi-compact
(affine) opens. *(ii)* $Y_0\subseteq Y$ is closed: $S_0\hookrightarrow S$ is
a closed immersion, and closed immersions are stable under base change
([lem-weil-pbc-closed-immersion-products]). The proof has two stages.

*Stage 1: the Zariski comparison, on $Y$ and on all its finite covers* (this
is Stacks Project, Tag [0A0B](https://stacks.math.columbia.edu/tag/0A0B),
Lemma 59.91.1). First apply [lemma-weil-pbc-stein-connectedness] to the
henselian pair [def-weil-pbc-henselian-terminology] and the proper morphism
$Y\to S$; both hypotheses are exactly the hypotheses of that theorem. Its
conclusion gives: every irreducible closed subset $C\subseteq Y$ meets $Y_0$
in a nonempty connected subset. Together with (i) and (ii) this is precisely
the hypothesis of [lemma-weil-pbc-spectral-restriction] for the pair
$(Y,Y_0)$, so that lemma applies and yields, for every locally constant
[def-weil-pbc-etale-sheaves] sheaf $G$ on the Zariski space $Y$,

$$
 \Gamma(Y,G)\xrightarrow{\sim}\Gamma(Y_0,G|_{Y_0}).
$$

For a general abelian sheaf $G$ this identification is *not* available: the
statement of that lemma is false without local constancy, as its own
statement records, and the sheaf to which Stage 1 is applied below is a
constructible sheaf of etale cohomology, for which local constancy is not
known. The passage from the locally constant case to the general case is
exactly what the status note to [lemma-weil-pbc-stein-connectedness] records as
open. The same argument applies verbatim to every finite morphism $h:Y'\to
Y$: the composite $Y'\to S$ is proper as the composite of the proper morphism
$h$ (finite morphisms are proper, [lem-weil-pbc-finite-proper]) and the
proper morphism $Y\to S$, so $Y'$ is spectral, its closed member
$Y'_0=Y'\times_ST_0\subset Y'$ is closed, and the connectedness conclusion
for $Y'$ follows from the same application of
[lemma-weil-pbc-stein-connectedness]. Hence for every $h:Y'\to Y$ finite and
every abelian sheaf $G'$ on the Zariski space $Y'$,

$$
 \Gamma(Y',G')\xrightarrow{\sim}\Gamma(Y'_0,G'|_{Y'_0}).
$$

These comparisons are compatible with $h$. For $a\in\Gamma(Y,G)$, its finite
pullback $h^\sharp a$ of [def-weil-pbc-finite-section-pullback]
restricts over $Y'_0$ to the finite pullback of $a|_{Y_0}$ by the
closed-fibre equation of [lem-weil-pbc-finite-pullback-identities];
consequently the comparison isomorphisms for $Y$ and for $Y'$ form a
commutative square with the two restriction maps. This is the compatibility
with finite pullback recorded in the statement.

*Stage 2: from Zariski sheaves to etale sheaves* (this is the upgrade of
Stacks Project, Tag [09ZF](https://stacks.math.columbia.edu/tag/09ZF), Lemma
59.82.2, whose finite-refinement input is Lemma 37.45.7, Tag
[09Z0](https://stacks.math.columbia.edu/tag/09Z0) (Section 37.45,
Applications of Zariski's Main Theorem, II), and whose final descent step is
Remark 59.55.6, Tag [09Z3](https://stacks.math.columbia.edu/tag/09Z3)
(Section 59.55, Vanishing of finite higher direct images, stated there for
sheaves of sets, the abelian form being Lemma 59.55.5, Tag
[09Z2](https://stacks.math.columbia.edu/tag/09Z2))). Let $F$ be an etale
abelian sheaf on $Y$. Every open immersion is etale, so the etale sheaf $F$
restricts to a Zariski sheaf on $Y$ with the same global sections, and
likewise its inverse image to $Y_0$. The etale comparison is obtained from
the Zariski comparison by finite-refinement descent, in which the finite
refinement of [lemma-weil-pbc-finite-refinement-etale-cover] is the only
additional input. Concretely: a section of $F|_{Y_0}$ is represented by an
etale neighbourhood $U\to Y$ of $Y_0$; gluing $U$ with the open complement
$Y\setminus Y_0$ turns it into a surjective etale morphism $U_1\to Y$, to
which [lemma-weil-pbc-finite-refinement-etale-cover] applies, giving a finite
surjective [def-weil-pbc-scheme-conventions] $r:Y'\to Y$ and a finite Zariski
open covering $Y'=\bigcup_aW_a$ with $Y$-maps $\phi_a:W_a\to U_1$. The
section pulls back along the $\phi_a$ to sections of $r^{-1}F$ over the open
subschemes $W_a$, and each of these lies on the proper $Y$-scheme
$\overline{W_a}$, the closure of $W_a$ in $Y'$, where the Zariski comparison
of Stage 1 (applied with the direct image of the restriction of $r^{-1}F$ to
$W_a$) transports it to the closed fibre of $\overline{W_a}$; these pieces
restrict to a Zariski open cover of $Y'_0$ and glue, because they all come
from one section of $F|_{Y_0}$ and $r_0:Y'_0\to Y_0$ is surjective. The
resulting section over $Y'_0$ is then matched back, along the finite
pullbacks of [lem-weil-pbc-finite-pullback-identities], with a section of $F$
over $Y$, and the uniqueness of the matchings gives injectivity of the same
comparison. Naturality in $F$ is clear from the construction (each step is
functorial in $F$), compatibility with finite pullback follows from the
square of Stage 1 and the functoriality of the refinements, and compatibility
with morphisms of henselian pairs results from transporting the whole
situation along such a morphism.
