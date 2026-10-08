+++
id = "thm-fin-deligne-generic-open"
kind = "theorem"
title = "Generic bounded constructibility for an open immersion"
order = 1637
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions", "lem-asd-smooth-generic-direct-image", "lem-fin-closed-immersion", "lem-fin-coordinate-generic-dimension", "lem-fin-finite-boundary-comparison", "lem-fin-finite-boundary-reconstruction", "lem-fin-generic-radicial-smoothing", "lem-fin-projective-coordinate-boundary", "lem-fin-radicial-exchange-descent", "lemma-weil-pbc-finite-exchange", "sbc-def-base-change-map", "sbc-lem-base-change-composition", "thm-constructible-serre", "thm-sp-truncation-e2", "thm-weil-pbc-bounded-below", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $S$ be integral and of finite type over a field $k$, let
$\ell\ne\operatorname{char}(k)$, and let
$j:X\hookrightarrow Y$ be an open immersion of finite-type
$S$-schemes. For a constructible $\mathbf F_\ell$-sheaf $F$
on $X$, there is a nonempty open $U\subset S$ such that
$Rj_{U,*}F|_{X_U}$ belongs to $D^b_c(Y_U,\mathbf F_\ell)$
and, for every morphism $T\to U$ with Noetherian $T$, its canonical base-change morphism

$$
Rj_{U,*}F|_{X_U}\big|_{Y_T}
\longrightarrow Rj_{T,*}F|_{X_T}
$$

is an isomorphism.
The notation refers to ordinary derived categories.

## Proof

Throughout this proof all base changes have Noetherian source.
We prove the two assertions simultaneously, so that every use of
the induction includes the specific exchange map. Replace $Y$
by the scheme-theoretic closure of $X$; the original immersion
is its composite with a closed immersion. Closed direct image
is exact and preserves constructibility by
[lem-fin-closed-immersion], and it commutes with base change by
[lemma-weil-pbc-finite-exchange]. We may therefore assume
that $X$ is dense in $Y$. The same observation extends any
case already proved for a dense open immersion to an arbitrary
immersion with that bound on the generic dimension of its source.

Induct on $n=\dim X_{k(S)}$. Before starting, remove the
closures of the images of the finitely many irreducible components
of $Y$ that do not dominate $S$. For an empty generic fiber
the remaining scheme is empty. For $n=0$, the dense open
$X_{k(S)}$ contains every point of the zero-dimensional
Noetherian space $Y_{k(S)}$, so it equals that space.
The closed complement $Y\setminus X$ has empty generic fiber.
Its finite affine presentations show that it becomes empty after
inverting one nonzero element of the base: over the fraction
field each coordinate ring is zero, so a nonzero base element
kills its unit; use the product for a finite affine cover.
Thus, after shrinking, $j$ is the identity and the assertion
holds. Assume now the assertion for generic source dimension
at most $n-1$, including all immersions as above.

*First step: the good locus has finite complement.*
The question is local on $Y$, and $Y$ has a finite affine
cover. For this step suppose $Y$ projective over an affine
open of $S$, and cover it by finitely many affine schemes
$Y_\alpha\hookrightarrow\mathbf A^{m_\alpha}_S$.
For each coordinate, regard
$X\cap Y_\alpha\hookrightarrow Y_\alpha$ as an immersion
over the integral finite-type base $\mathbf A^1_S$.
Its generic source dimension is at most $n-1$ by
[lem-fin-coordinate-generic-dimension]. The induction
hypothesis supplies a dense open $V_{\alpha r}\subset\mathbf A^1_S$
over whose inverse image the direct image is bounded constructible
and commutes with all base changes. This includes every base
change induced from $T\to S$: restrict the induced morphism
$\mathbf A^1_T\to\mathbf A^1_S$ to $V_{\alpha r}$.
There are finitely many coordinate pairs. Their union $G$
therefore has both properties, with a common finite cohomological
range. By [lem-fin-projective-coordinate-boundary], shrink
$S$ so that $Z=Y\setminus G$, with reduced structure, is
finite over $S$.

*Second step: smooth source and locally constant sheaf.*
Assume $X\to S$ is smooth and $F$ locally constant.
The assertion can be checked on each member of a finite affine
cover of $Y$. For one such member, embed it in affine space
and take its projective closure. The original affine member
is open in this closure, so $X$ remains an open subscheme of
the projective closure. Replacing the closure by the closure of
$X$ makes $X$ dense. This operation changes no generic
dimension of $X$, and the desired result on the projective
closure restricts to the original member.
We can thus use the first step with $b:Y\to S$ projective.
Set $K=Rj_*F$ and $a=bj:X\to S$. The first step proves
$K|_G\in D^b_c(G)$. After one further shrinking,
[lem-asd-smooth-generic-direct-image] proves
$Ra_*F=Rb_*K\in D^b_c(S)$.
[lem-fin-finite-boundary-reconstruction] now gives
$K\in D^b_c(Y)$.

For any $T\to S$ with Noetherian $T$, let $c:K|_{Y_T}\to Rj_{T,*}F|_{X_T}$
be its exchange morphism. On $G_T$ it is an isomorphism by
the first step. After applying $Rb_{T,*}$, proper base change
[thm-weil-pbc-bounded-below] and the composition rule
[sbc-lem-base-change-composition] identify the resulting
morphism with the exchange for $a$, which is an isomorphism
by the smooth-source lemma. The base change of $Z\to S$
is finite. Hence [lem-fin-finite-boundary-comparison],
applied over $T$, says that $c$ is an isomorphism.
Notice that the target of $c$ need only start in $D^+$;
its boundedness follows from the proved isomorphism.
This proves the entire dimension-$n$ assertion whenever the
source is smooth and the coefficient sheaf is locally constant.

*Third step: arbitrary constructible sheaf.*
By [lem-fin-generic-radicial-smoothing], after shrinking and
making a finite radicial surjective base change, the reduction of
$X$ has a dense smooth open $v:V\hookrightarrow X$ on which
$F$ is locally constant. Replacing the schemes by their
reductions does not change their etale topoi, by
[thm-weil-pbc-universal-homeomorphism-invariance].
The second step, which has already been proved at dimension
$n$, applies both to $v:V\hookrightarrow X$ and to
$jv:V\hookrightarrow Y$. After intersecting the two resulting
base opens, their derived direct images are bounded constructible
and commute with every base change. Form the triangle

$$
F\longrightarrow Rv_*v^*F\longrightarrow\Delta\longrightarrow F[1].
\tag{1}
$$

The first arrow is the adjunction unit. Both first terms are
bounded constructible, so the cohomology long exact sequence and
[thm-constructible-serre] show that $\Delta$ is
bounded constructible. The unit is the identity after restriction
to $V$, hence $\Delta|_V=0$. For the reduced closed complement
$i:W\hookrightarrow X$, termwise open–closed localization from
[def-weil-pbc-extension-by-zero] identifies
$\Delta=i_*i^*\Delta$. The generic dimension of $W$ is less
than $n$.

Apply the induction hypothesis to the immersion $ji:W\to Y$
and to each of the finitely many constructible sheaves
$\mathcal H^q(i^*\Delta)$. Intersect the finitely many base
opens. Finite truncation triangles, or their bounded spectral
sequence [thm-sp-truncation-e2], prove that
$R(ji)_*i^*\Delta=Rj_*\Delta$ is bounded constructible and
commutes with every base change. Only a finite number of
cohomology sheaves and a bounded truncation filtration occur.
Apply $Rj_*$ to (1). The middle term is
$R(jv)_*v^*F$, already handled by the second step, and the
third term has just been handled by lower-dimensional induction.
The long exact sequence proves bounded constructibility of
$Rj_*F$. After any base change, the second-step exchange
identifies the pullback of (1) with the analogous triangle for
$v_T$. The three exchange morphisms consequently form a
morphism of triangles; the second and third are isomorphisms,
so the first is an isomorphism as well.
Finally [lem-fin-radicial-exchange-descent] descends the result
through the finite radicial base change. Its hypothesis must be checked
over the whole base to which it is applied, so we first produce an open of
$S$ whose preimage lies inside the good open. Let $U\subseteq S$ be
the open over which the preceding steps hold and let
$U'\subseteq S'_{U}=S'\times_SU$ be the nonempty open of $S'_{U}$ on
which they were verified. Since $S'\to S$ is finite, surjective and
radicial, it is a homeomorphism on underlying spaces; $S$ being
integral, $S'$ and $S'_{U}$ are therefore irreducible of dimension
$\dim S$. The complement $F=S'_{U}\setminus U'$ is closed in
$S'_{U}$, and its image $C\subseteq U$ is closed because
$S'_{U}\to U$ is finite. If $C=U$, then $F\to U$ is surjective, so
$\dim F\ge\dim U=\dim S'_{U}$, which is impossible for a proper closed
subset of the irreducible $S'_{U}$. Hence $C\neq U$, and for the
nonempty open $U_1=U\setminus C$ the preimage $S'_{U_1}$ is contained
in $U'$. Applying [lem-fin-radicial-exchange-descent] over
$U_1$, and intersecting with the finitely many opens already produced,
completes the induction.
