+++
id = "rem-sf-continuity-obstruction"
kind = "remark"
title = "What the recorded proof of the comparison theorem uses, and why it does not extend to arbitrary sheaves"
order = 2055
uses = ["cor-sf-fullcd-weakly-contractible-test", "def-sf-fullcd-used-class", "def-weil-pbc-proetale-site", "def-weil-pbc-site-comparison-morphism", "lem-cbc-proetale-stalk-conservative", "lem-sf-etale-direct-image-vanishing", "lem-sf-proetale-vanishing-detection", "open-sf-ambient-adjoint-input", "prop-sf-comparison-bound-zero", "rem-sf-fullcd-counterexample", "rem-sf-fullcd-general-form", "rem-sf-fullcd-reduction", "thm-sf-fullcd-etale-origin"]
+++
The continuity statement $(\mathrm{C}_q)$ of
*Continuity for arbitrary sheaves implies the vanishing* was the single missing
input of the route that would have deduced $(\mathrm{G})$ from
[lem-sf-etale-direct-image-vanishing]. That route is now closed in the
negative: $(\mathrm{G})$ is *false*, by
*The all-sheaves, uniform-in-the-base-change form of the comparison bound is false* and
[rem-sf-fullcd-counterexample], so by the contrapositive of
*Continuity for arbitrary sheaves implies the vanishing* the statement
$(\mathrm{C}_q)$ fails at the base change $U$ of that counterexample in
every degree $q$ in which $R^q\nu_{U,*}F_G\neq0$, that is in unboundedly
many degrees. What the present remark records is why that failure is not an
accident of the construction: $(\mathrm{C}_q)$ is *not* obtained from
the étale vanishing lemma, and its
proof in the sources covers only sheaves of étale origin, so the hypothesis
is not available in the generality in which the general form needed it. A
further point is that
the resulting criterion does not go through geometric-point stalks, in
contrast with the failure of conservativity of the pro-étale geometric-point
stalks recorded in clause (4) of
[lem-cbc-proetale-stalk-conservative]: by
[lem-sf-proetale-vanishing-detection] and
[cor-sf-fullcd-weakly-contractible-test] the vanishing is tested on the
affine weakly contractible objects, and the continuity of the values along the
pointed étale neighbourhoods, not the conservative detection of sheaves, was
what the general form needed.

1. *The étale lemma does not bound the terms of the colimit.* The
colimit in $(\mathrm{C}_q)$ runs over the pointed étale neighbourhoods
$U$ of a geometric point of $V$, the comparison morphism being the
$\nu_V$ of [def-weil-pbc-site-comparison-morphism], and its terms are
the *pro-étale* cohomology groups $H^q(U_{\Proet},\mathcal F|_U)$ of
those finite-type models, the cohomology of the small pro-étale site of
[def-weil-pbc-proetale-site].
[lem-sf-etale-direct-image-vanishing] bounds the higher direct images of a
finite-type morphism on the *étale* sites, that is the groups
$H^q(U_{\Et},-)$; it says nothing about the pro-étale cohomology of $U$,
which for the sheaves of étale origin equals the étale cohomology by
Stacks Project, Pro-étale Cohomology, Lemma 61.19.6,
[Tag 099W](https://stacks.math.columbia.edu/tag/099W), but is not
controlled for the remaining sheaves. A bound on those terms uniform over the
inverse system is therefore a hypothesis about pro-étale cohomology and not
an étale statement, and *Continuity for arbitrary sheaves gives the full cohomological-dimension bound*(i) shows that the
continuity hypothesis, not the étale lemma, is what makes the terms vanish
above $2d$ for the finite-type models; so this route is not a reduction to
the étale bound. What the étale bound does give is the second factor of
the Leray spectral sequence of the comparison morphism, the $p$-direction
bounded by $2d$, as recorded in [rem-sf-fullcd-reduction].
1. *What the recorded proof of the comparison theorem uses.* The
vanishing of Stacks Project, Pro-étale Cohomology, Lemma 61.19.5,
[Tag 099V](https://stacks.math.columbia.edu/tag/099V) — which is
[thm-sf-fullcd-etale-origin] with the bound $2d$ sharpened to $0$ —
is proved through Lemma 61.19.4,
[Tag 099U](https://stacks.math.columbia.edu/tag/099U): for an injective
abelian sheaf $\mathcal I$ on $X_{\Et}$ and a pro-étale covering
$\lbrace U_i\to U\rbrace$ of an affine $U$ that is ind-étale over the
affine $X$, one writes each $U_i$ as a directed inverse limit of affine
étale $U_{i,a}\to U$, computes
$$
\check H^p\bigl(\mathcal U,\epsilon^{-1}\mathcal I\bigr)
=\varinjlim\check H^p\bigl(\mathcal U_{(a_1,\dots,a_n)},
\epsilon^{-1}\mathcal I\bigr)
$$
and reduces to the étale coverings $\mathcal U_{(a_1,\dots,a_n)}$ of the
*models*, where the Čech complexes are acyclic in positive degrees.
Three inputs make this work, and none of them is available for an arbitrary
pro-étale sheaf $\mathcal F$:
   1. **(a)** the degree-zero continuity of the *values* along the inverse
system, Stacks Project, Pro-étale Cohomology, Lemma 61.19.3,
[Tag 099S](https://stacks.math.columbia.edu/tag/099S): for a sheaf
$\mathcal G$ on $X_{\Et}$ and a directed inverse system of quasi-compact
quasi-separated pro-étale objects with affine transition maps one has
$\epsilon^{-1}\mathcal G(\varprojlim Y_i)=\varinjlim\epsilon^{-1}\mathcal G(Y_i)$.
This is the only continuity the sources record, and it is a statement about
pulled-back étale sheaves; for a sheaf that is not of étale origin it fails
in general. The recorded witness is Stacks Project, Pro-étale Cohomology,
Section 61.18, [Tag 0991](https://stacks.math.columbia.edu/tag/0991),
together with Example 61.19.12,
[Tag 0F6D](https://stacks.math.columbia.edu/tag/0F6D): the sheaf
$fun(-,A)/\underline A$ has zero stalk at the unique geometric point of
$\operatorname{Spec}k$, hence zero value at the strictly henselian limit
object by *The strictly henselian limit has no higher cohomology*(i), while its value at a
pro-étale model with infinitely many points is nonzero. The example is
stated for pro-étale neighbourhoods; it is the reason why no value
continuity may be assumed in $(\mathrm{C}_q)$.
   1. **(b)** the identification $\epsilon_*\epsilon^{-1}\mathcal G=\mathcal G$
of Stacks Project, Pro-étale Cohomology, Lemma 61.19.2,
[Tag 099T](https://stacks.math.columbia.edu/tag/099T), which converts the
étale Čech complex of the model into the pro-étale one; and the
acyclicity criterion of Stacks Project, Cohomology on Sites, Lemma 21.10.9,
[Tag 03F9](https://stacks.math.columbia.edu/tag/03F9), whose hypothesis
(3) requires the vanishing of the higher Čech cohomology of the sheaf with
respect to the chosen covers, which is what (a) and (b) supply — together
with the acyclicity of étale Čech complexes of injective étale sheaves,
Stacks Project, Cohomology on Sites, Lemma 21.10.2,
[Tag 03AW](https://stacks.math.columbia.edu/tag/03AW).
   1. **(c)** the injectivity of $\mathcal I$, used to produce the resolution.
For a general $\mathcal F$ the sheaf $R^q\nu_{V,*}\mathcal F$ is the sheaf
associated to the presheaf $U\mapsto H^q(U_{\Proet},\mathcal F|_U)$ by Stacks
Project, Cohomology on Sites, Lemma 21.7.4,
[Tag 072W](https://stacks.math.columbia.edu/tag/072W), and its sections
need not lift to the terms of that presheaf over a cover of the model; the
lifting that *is* available, *Sections of an associated sheaf lift locally*,
is what *Continuity for arbitrary sheaves implies the vanishing* uses, and it
converts $(\mathrm{C}_q)$ into the vanishing of the associated sheaf only
because $(\mathrm{C}_q)$ is a statement about *every* class on
*every* pointed neighbourhood. The converse implication is not
available: the vanishing of $R^q\nu_{V,*}\mathcal F$, that is $P^{\#}=0$,
says only that every class of $P(U)$ dies on some étale *cover* of
$U$ — this is what the two-step construction of the associated sheaf
recalled in the proof of *Sections of an associated sheaf lift locally* gives,
since $P\to P^{+}$ kills exactly the classes that vanish on a covering and
$P^{+}\to P^{\#}$ is injective — whereas $(\mathrm{C}_q)$ demands death
on a single pointed refinement.
1. *What remains true, and where the residue lies.* On the
pro-étale site the only vanishing statement for *all* sheaves that the
recorded sources supply is at a weakly contractible object (Sites, Definition
7.40.2, [Tag 090L](https://stacks.math.columbia.edu/tag/090L); Pro-étale
Cohomology, Lemma 61.13.3,
[Tag 098I](https://stacks.math.columbia.edu/tag/098I) and Lemma 61.13.5,
[Tag 0F4P](https://stacks.math.columbia.edu/tag/0F4P)), which is the input
of [lem-sf-proetale-vanishing-detection] and of
[cor-sf-fullcd-weakly-contractible-test]; the hypercovering of Pro-étale
Cohomology, Lemma 61.14.1,
[Tag 09A1](https://stacks.math.columbia.edu/tag/09A1) with Lemma 61.14.2,
[Tag 09A2](https://stacks.math.columbia.edu/tag/09A2) carries no bound on
its length — and by *The question of a bounded weakly contractible hypercovering has a negative answer* no hypercovering of a
nonempty object is bounded at all, so that a bound on the length is
unattainable in principle and not merely absent from this construction — so
it cannot bound the vanishing degree of $R^q\nu_{V,*}$, as
[rem-sf-fullcd-general-form] records. Accordingly neither the sources
recorded here nor the acyclicity devices recalled above decide
$(\mathrm{C}_q)$ for a sheaf that is not of étale origin, and in this form
$(\mathrm{C}_q)$ is not proved here in that generality, and cannot be: by the
contrapositive of *Continuity for arbitrary sheaves implies the vanishing* the
counterexample of [rem-sf-fullcd-counterexample] refutes it at its base
change. What is now known about it is
exactly three things, recorded in the items following this remark. First, for
every sheaf of étale origin – in particular on the blueprint's coefficient
class [def-sf-fullcd-used-class] – the statement is a theorem with a
complete proof, *Continuity for sheaves of étale origin: every class dies on a single pointed refinement*: every class dies on a
single pointed étale refinement, obtained from a covering that kills it by
forming the disjoint union of its members. Second, its pro-étale form holds
for *every* sheaf and is a triviality,
*The pro-étale form of the continuity statement: every class dies on the strict henselization limit*: the strict henselization limit is
an initial object of the category of pointed pro-étale neighbourhoods, so
every class dies on that one pro-étale refinement, the target being zero by
*The strictly henselian limit has no higher cohomology*(iii); the whole content of
$(\mathrm{C}_q)$ is therefore the passage from pro-étale refinements to
étale ones. Third, that passage cannot be made by a cofinality argument,
*The pointed étale neighbourhoods are not cofinal among the pointed pro-étale ones*: an infinite separable extension
of the residue field gives a pointed pro-étale neighbourhood that receives no
morphism from any pointed étale neighbourhood, so the two colimits are not
related by the criterion that compares them. With
$(\mathrm{C}_q)$ failing in that remaining case – the general form of
$(\mathrm{G})$ being false, by
*The all-sheaves, uniform-in-the-base-change form of the comparison bound is false* and
[rem-sf-fullcd-counterexample], and $(\mathrm{C}_q)$ failing with it at
that counterexample's base change, by
*Continuity for arbitrary sheaves implies the vanishing* – the condition
$\operatorname{FullCD}(p,A;c_{\mathrm{cd}})$ of
[open-sf-ambient-adjoint-input] is read on the blueprint's coefficient
class, where it is the theorem [thm-sf-fullcd-used-class] with the sharp
comparison bound $M=0$ of [prop-sf-comparison-bound-zero]. Nothing
here weakens the unconditional results: on the blueprint's coefficient class
[def-sf-fullcd-used-class] the vanishing is the theorem
[thm-sf-fullcd-etale-origin], with the comparison bound $0$ and
uniformly over the base changes, by
[prop-sf-comparison-bound-zero], and every conditional entry of the
matrix is conditional, on that class, on the ambient datum's assertion for the
complexes outside it, whose vanishing half there is the theorem
[thm-sf-fullcd-class] and whose existence half there is the theorem
[thm-sf-ambient-adjoint-class], as
[rem-sf-class-adjoint-residue] records.
