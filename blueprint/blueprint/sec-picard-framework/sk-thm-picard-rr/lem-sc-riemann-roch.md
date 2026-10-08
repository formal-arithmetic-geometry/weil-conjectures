+++
id = "lem-sc-riemann-roch"
kind = "lemma"
title = "Riemann–Roch on a proper smooth curve"
order = 706
uses = ["def-sc-curves", "def-sc-function-field", "def-sc-genus", "def-sc-invertible-module", "def-sc-pic0"]
lean = ["AlgebraicGeometry.Scheme.eulerChar_free_eq", "AlgebraicGeometry.Scheme.eulerChar_unit_eq"]
+++
Let $k$ be algebraically closed and $C$ a
proper smooth connected curve of genus $g$ ([def-sc-genus]) over
$k$, with generic point $\eta$ and function field $k(C)$
([def-sc-function-field]). For a coherent $\mathcal O_C$-module
$\mathcal F$ put
$\chi(C,\mathcal F):=\sum_q(-1)^q\dim_kH^q(C,\mathcal F)$, let
$\mathcal T\subseteq\mathcal F$ be its torsion subsheaf (the kernel of
$\mathcal F\to\mathcal F_\eta$), and define the *rank* and the
*degree* of $\mathcal F$ by

$$
\operatorname{rk}\mathcal F:=\dim_{k(C)}\mathcal F_\eta,\qquad
\deg\mathcal F:=\dim_kH^0(C,\mathcal T)+\deg\det(\mathcal F/\mathcal T),
$$

where $\mathcal F/\mathcal T$ is locally free of rank
$\operatorname{rk}\mathcal F$ (see the proof),
$\det$ is its top exterior power (with $\det=\mathcal O_C$ in rank
$0$) and $\deg$ on line bundles is that of [def-sc-pic0]; for a line
bundle $\mathcal L$ this is $\operatorname{rk}\mathcal L=1$ and
$\deg\mathcal L$ as in [def-sc-pic0]. Then:

1. (*Riemann–Roch for line bundles.*) For every line bundle
$\mathcal L$ on $C$,

$$
\chi(C,\mathcal L)=\deg\mathcal L+1-g.
$$

(*Stacks Project, Algebraic Curves, Lemma 53.5.2,
[Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6).*)
In particular $\chi(C,\mathcal O_C)=1-g$.

2. (*Riemann–Roch for coherent modules.*) For every coherent
$\mathcal O_C$-module $\mathcal F$,

$$
\chi(C,\mathcal F)=\deg\mathcal F+\operatorname{rk}(\mathcal F)\,(1-g).
$$

## Proof

*Preliminaries.* $C$ is integral (its local rings are regular, hence
domains, so its irreducible components are disjoint and connectedness
leaves one), of dimension one, and its local rings at closed points are
discrete valuation rings with residue field $k$. For a coherent
$\mathcal F$ the spaces $H^q(C,\mathcal F)$ are finite-dimensional
(coherent cohomology of a proper scheme over a field, Stacks Project,
Cohomology of Schemes, Proposition 30.19.1,
[Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)) and vanish for
$q\ge2$ (Grothendieck vanishing on the one-dimensional Noetherian space
$C$; Stacks Project, Cohomology of Sheaves), so $\chi$ is a finite sum,
and a short exact sequence
$0\to\mathcal F_1\to\mathcal F_2\to\mathcal F_3\to0$ of coherent
modules gives
$\chi(\mathcal F_2)=\chi(\mathcal F_1)+\chi(\mathcal F_3)$: its long
exact cohomology sequence is a finite exact sequence of
finite-dimensional $k$-vector spaces, whose alternating sum of
dimensions vanishes.

*Part (1).* This is the recorded classical input of the statement, Stacks Project,
Algebraic Curves, Lemma 53.5.2
([Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)), used in the
displayed form $\chi(C,\mathcal L)=\deg\mathcal L+1-g$, where
$\chi(C,\mathcal L)=\dim H^0(C,\mathcal L)-\dim H^1(C,\mathcal L)$ and
$g=\dim H^1(C,\mathcal O_C)$ ([def-sc-genus]); no separate proof
is given. Applied to $\mathcal L=\mathcal O_C$, whose degree is $0$
($\deg$ is a homomorphism, [def-sc-pic0]), it gives
$\chi(C,\mathcal O_C)=1-g$.

*The torsion part.* The torsion subsheaf $\mathcal T$ is the kernel of
$\mathcal F\to j_*\mathcal F_\eta$ ($j:\operatorname{Spec}k(C)\to C$
the generic point, $j_*\mathcal F_\eta$ quasi-coherent), hence
quasi-coherent, and coherent as a submodule of the coherent
$\mathcal F$ on the Noetherian scheme $C$. Its stalk
$\mathcal T_x$ is the torsion submodule of $\mathcal F_x$ (localization
is exact, and an element of $\mathcal F_x$ dies in $\mathcal F_\eta$ iff
it is killed by a nonzero element of $\mathcal O_{C,x}$). As
$\mathcal T_\eta=0$, the support of $\mathcal T$ is a closed subset
not containing $\eta$, hence a finite set $Z$ of closed points of the
irreducible one-dimensional Noetherian space $C$. A sheaf supported on
the finite discrete closed set $Z$ is the direct sum
$\bigoplus_{x\in Z}i_{x,*}\mathcal T_x$ of skyscraper sheaves, which are
flasque; hence $H^q(C,\mathcal T)=0$ for $q>0$ and

$$
\chi(C,\mathcal T)=\dim_kH^0(C,\mathcal T)
=\sum_{x\in Z}\dim_k\mathcal T_x
$$

(finite, each $\mathcal T_x$ being a finitely generated torsion module
over the discrete valuation ring $\mathcal O_{C,x}$ with residue field
$k$). Moreover $\operatorname{rk}\mathcal T=0$ and
$\deg\mathcal T=\dim_kH^0(C,\mathcal T)$, so (2) holds for $\mathcal T$.

*The torsion-free quotient.* $\mathcal E:=\mathcal F/\mathcal T$ is
coherent with stalks $\mathcal E_x=\mathcal F_x/(\mathcal F_x)_{\rm tors}$,
finitely generated and torsion-free over the discrete valuation ring
$\mathcal O_{C,x}$ (a principal ideal domain), hence free; a coherent
module with free stalks is locally free (a finitely presented module
whose stalk at $x$ is free is free on a neighbourhood of $x$), of
constant rank $r=\dim_{k(C)}\mathcal E_\eta=\dim_{k(C)}\mathcal F_\eta=\operatorname{rk}\mathcal F$
because $C$ is irreducible. By additivity,
$\chi(\mathcal F)=\chi(\mathcal T)+\chi(\mathcal E)$, and by
definition $\deg\mathcal F=\deg\mathcal T+\deg\det\mathcal E$.
So (2) follows once we show, for every locally free $\mathcal E$ of
rank $r$,

$$
\chi(C,\mathcal E)=\deg\det\mathcal E+r(1-g). \tag{$\ast$}
$$

*Proof of $(\ast)$, by induction on $r$.* For $r=0$, $\mathcal E=0$
and both sides vanish ($\det\mathcal E=\mathcal O_C$ has degree $0$).
For $r=1$, $(\ast)$ is part (1), since $\det\mathcal E=\mathcal E$.
Let $r\ge2$. Choose $0\neq s\in\mathcal E_\eta$ and let
$\mathcal L\subseteq\mathcal E$ be the kernel of the composite
$\mathcal E\to j_*\mathcal E_\eta\to j_*(\mathcal E_\eta/k(C)s)$; as
above, $\mathcal L$ is coherent, with stalks
$\mathcal L_x=\mathcal E_x\cap k(C)s$ (intersection inside
$\mathcal E_\eta$; $\mathcal E_x\to\mathcal E_\eta$ is injective as
$\mathcal E_x$ is free over the domain $\mathcal O_{C,x}$). The module
$\mathcal E_x\cap k(C)s$ is nonzero (clear the denominators of $s$ with
respect to a basis of $\mathcal E_x$), finitely generated
($\mathcal O_{C,x}$ is Noetherian) and torsion-free of generic rank one,
hence free of rank one; and
$\mathcal E_x/\mathcal L_x\hookrightarrow\mathcal E_\eta/k(C)s$ is
torsion-free (if $ae\in k(C)s$ with $0\neq a\in\mathcal O_{C,x}$ then
$e\in k(C)s$), hence free of rank $r-1$. Thus $\mathcal L$ is an
invertible module ([def-sc-invertible-module]) and
$\mathcal E':=\mathcal E/\mathcal L$ is locally free of rank $r-1$,
by the criterion used above. The exact sequence
$0\to\mathcal L\to\mathcal E\to\mathcal E'\to0$ of locally free
modules gives
$\det\mathcal E\cong\mathcal L\otimes\det\mathcal E'$ (the
determinant is multiplicative in short exact sequences of finite
locally free modules: locally the sequence splits and
$\wedge^r(\mathcal L\oplus\mathcal E')=\mathcal L\otimes\wedge^{r-1}\mathcal E'$,
the isomorphism $l\wedge\tilde e_1\wedge\dots\wedge\tilde e_{r-1}\mapsto l\otimes e_1\wedge\dots\wedge e_{r-1}$
being independent of the lifts $\tilde e_i$ and so gluing). Since
$\deg$ is a homomorphism on $\operatorname{Pic}(C)$
([def-sc-pic0]), $\deg\det\mathcal E=\deg\mathcal L+\deg\det\mathcal E'$.
Additivity of $\chi$, part (1) for $\mathcal L$ and the induction
hypothesis for $\mathcal E'$ give

$$
\chi(\mathcal E)=\chi(\mathcal L)+\chi(\mathcal E')
=\bigl(\deg\mathcal L+1-g\bigr)+\bigl(\deg\det\mathcal E'+(r-1)(1-g)\bigr)
=\deg\det\mathcal E+r(1-g),
$$

which is $(\ast)$. This proves (2).
