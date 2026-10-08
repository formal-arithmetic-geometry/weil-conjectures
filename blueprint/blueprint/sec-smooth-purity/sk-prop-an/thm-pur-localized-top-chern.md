+++
id = "thm-pur-localized-top-chern"
kind = "theorem"
title = "Localized top Chern class"
order = 1987
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-frame-class", "def-pur-support-cohomology", "def-weil-derived-cohomology-sheaves", "def-weil-derived-tensor", "lem-pur-divisor-class", "lem-pur-frame-independence", "lem-pur-kummer-additivity", "lem-pur-kunneth-supported", "thm-pur-projective-bundle-formula"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $F$ be a rank-$r$ vector bundle on $T$, let $s$ be a regular
section, and write $i:Z(s)\hookrightarrow T$. There is a canonical
morphism

$$
c_r(F,s):i_*\Lambda_{Z(s)}\longrightarrow\Lambda_T(r)[2r]
$$

with the following properties:

1. *(L1)* for $r=1$ it is the localized Kummer class of the
Cartier divisor of $s$ (of [lem-pur-divisor-class]);
1. *(L2)* it commutes with base change whenever the
pulled-back section is still regular, in particular with
arbitrary base change for the tautological section on the total
space of a vector bundle;
1. *(L3)* for a transverse direct sum of sections it is the
cup product of the two localized classes;
1. *(L4)* after forgetting support it is $c_r(F)$.

Its construction uses only ordinary cohomology-with-support groups
and the projective-bundle formula.

## Proof

The line-bundle class in the proposed construction is the divisor class of [lem-pur-divisor-class]; products have their twists identified by [def-coefficient-twists-detailed].
Step 1: the flag-bundle pullback is injective. Write the group in
the form

$$
H^{2r}_{Z(s)}(T,\Lambda(r))
:=\operatorname{Hom}_{D(T,\Lambda)}
\bigl(i_*\Lambda_{Z(s)},\Lambda_T(r)[2r]\bigr).
$$

Pull $F$ back to its complete flag bundle $p:T'\to T$. Iterating
[thm-pur-projective-bundle-formula] gives a direct-sum
decomposition of $Rp_*\Lambda_{T'}$ whose degree-zero summand is
$\Lambda_T$; projection to this summand with the projection formula
is a left inverse to

$$
p^*:H^{2r}_{Z(s)}(T,\Lambda(r))
\longrightarrow
H^{2r}_{Z(s)\times_TT'}(T',\Lambda(r)),
$$

so this pullback is injective: the ordinary splitting principle for the
displayed abelian group.

Step 2: the class on the flag bundle. On $T'$ the flag quotients are
line bundles; successively take the localized Kummer classes of the
induced line-bundle sections on their successive zero loci and cup them,
obtaining an element
$\operatorname{cl}_{T'}\in H^{2r}_{Z(s)\times_TT'}(T',\Lambda(r))$.
The result is unchanged under a refinement of the flag: expanding the
product and using the additivity of
[lem-pur-kummer-additivity]
($c_1(L\otimes M)=c_1(L)+c_1(M)$) shows that it is the symmetric
elementary polynomial of degree $r$ in the Chern roots.

Step 3: the class descends, by localizing on the base. The following
gives a well-defined class on every open $T_0\subseteq T$ over which $F$
is trivial, and it is here that the descent is justified — by
[lem-pur-frame-independence], not by the degree-zero summand of the
projective-bundle decomposition. Choose an isomorphism
$F|_{T_0}\cong\mathcal O_{T_0}^r$ and write
$s|_{T_0}=(s_1,\dots,s_r)$ with $s_i\in\Gamma(T_0,\mathcal O)$; the
regularity of $s$ says exactly that $s_1,\dots,s_r$ is a frame of the
ideal of $Z(s)$ in the sense of [def-pur-frame-class], so put

$$
c_r(F,s)|_{T_0}=\kappa(s_1)\cup\cdots\cup\kappa(s_r)
\in H^{2r}_{Z(s)}(T_0,\Lambda(r)).
$$

A second trivialization is related to the first by an invertible matrix over
$T_0$, so by [lem-pur-frame-independence] the class depends only on
the ideal of $Z(s)$, hence only on the open and on $s$; on an overlap
the two frames frame the same ideal, so the classes agree and glue, and
because $H^{2r}_{Z(s)}(-,\Lambda(r))$ is computed by the sheaf-theoretic
operations of [def-pur-support-cohomology] they give an element
$c_r(F,s)\in H^{2r}_{Z(s)}(T,\Lambda(r))$. Now compare with
$\operatorname{cl}_{T'}$. Over a trivializing open $T_0$ the flag
bundle is $T_0\times_kG/B$, and there the universal filtration of the
trivialized bundle has line quotients whose sections are the images of the
components $s_i$ of the frame; the zero locus of such a section is the
preimage of $V(s_i)$, so by the functoriality of the Kummer class and of
the supported product the successive construction of Step 2 restricts to
the pullback of $\kappa(s_1)\cup\cdots\cup\kappa(s_r)$, that is, to
$p^*(c_r(F,s)|_{T_0})$. The trivializing opens cover $T$, so
$p^*c_r(F,s)=\operatorname{cl}_{T'}$. In particular the class of Step 2
does lie in the image of the injective pullback $p^*$ of Step 1, which is
what had to be shown, and $c_r(F,s)$ is the unique element with that
pullback.

Step 4: the four properties. They follow after the injective
flag-bundle pullback, where they reduce respectively to the rank-one
Kummer construction, the functoriality of a local equation, the
associativity and direct-sum behaviour of the cup product (with the
transversality as in [lem-pur-kunneth-supported]), and the usual
splitting-principle definition of $c_r(F)$. This is descent of one
element along a split injection of abelian groups, not descent of
derived categories or derived objects.
