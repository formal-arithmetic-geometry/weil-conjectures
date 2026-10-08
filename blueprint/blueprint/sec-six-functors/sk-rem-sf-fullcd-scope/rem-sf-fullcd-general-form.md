+++
id = "rem-sf-fullcd-general-form"
kind = "remark"
title = "The general form of $\\operatorname{FullCD}$, and the form the blueprint uses"
order = 2052
uses = ["cor-sf-fullcd-weakly-contractible-test", "def-sf-fullcd-used-class", "def-weil-finite-torsion-constructibility", "def-weil-full-cohomological-dimension", "lem-cbc-proetale-stalk-conservative", "lem-sf-etale-direct-image-vanishing", "lem-sf-fullcd-detection-equivalence", "lem-sf-proetale-constructible-origin", "lem-sf-proetale-vanishing-detection", "prop-sf-comparison-bound-zero", "thm-sf-fullcd-etale-origin", "thm-sf-fullcd-used-class", "thm-sp-grothendieck"]
+++
The condition [def-weil-full-cohomological-dimension] quantifies over
*all* sheaves of $A$-modules on $\overline X_{\Proet}$, and it is by
[lem-sf-fullcd-detection-equivalence] equivalent to a uniform bound on
the cohomological dimension of the pro-étale sites of the base-changed
sources. Two forms of that condition must be distinguished.

1. *On the blueprint's coefficient class it is a theorem*, with the
bound $2\dim\overline X$ and uniformly over the base changes: this is
[thm-sf-fullcd-used-class], whose class
[def-sf-fullcd-used-class] is the class of étale origin, equivalently
– by [lem-sf-proetale-constructible-origin] – the class of
constructible pro-étale coefficient sheaves
([def-weil-finite-torsion-constructibility]). The comparison bound
itself is $M=0$ on that class, by
[prop-sf-comparison-bound-zero]: the residual $2\dim\overline X$ is the
étale direction of the Leray spectral sequence of
[thm-sp-grothendieck] and not a lower bound on
$R^q\nu_{\overline X,*}$. Every coefficient sheaf
that this manuscript constructs lies in it: the construction of the six
operations takes place on the bounded constructible categories, so the
coefficient sheaves occurring in the statements of the blueprint are
constructible, and by the cited origin statement they are exactly the ones
covered by [thm-sf-fullcd-etale-origin].
1. *On arbitrary pro-étale module sheaves, uniformly over the base
changes, it is FALSE.* The general form is refuted by
*The all-sheaves, uniform-in-the-base-change form of the comparison bound is false*, whose counterexample is recorded in
[rem-sf-fullcd-counterexample]: there are a scheme $X_0$, an affine
pro-étale object $U\to X_0$ of $X_{0,\Proet}$ and, for every integer
$M$, a sheaf $F_G$ of $A$-modules on $U_{\Proet}$ – not of étale
origin – with $R^q\nu_{U,*}F_G\neq0$ for some $q>M$. What the recorded
tools do and do not bound is the following. The
recorded tools do not bound it: by
[lem-sf-fullcd-detection-equivalence] the condition is the vanishing of
the pro-étale cohomology of the base-changed source
$\overline X\times_YV$, tested by
[lem-sf-proetale-vanishing-detection] at the affine weakly contractible
objects $W\to V$ — the form of the test recorded in
[cor-sf-fullcd-weakly-contractible-test] — and the object
$\overline X\times_YW$ that appears is
the base change of $W$ along the proper morphism $p$, which is *not*
pro-étale; the argument that makes every sheaf acyclic on a weakly
contractible object – every pro-étale cover of it has a section, so its
global-sections functor is exact, which is Stacks Project, Cohomology on
Sites, Lemma 21.51.1,
[Tag 0946](https://stacks.math.columbia.edu/tag/0946) – therefore does
not apply to $\overline X\times_YW$, and no bound on those groups is
recorded. A search of the sources recorded in this blueprint's audit ledger
was carried out for exactly this bound, and it found no proof and no
counterexample. On the pro-étale site the only vanishing statement for
*all* sheaves is the one just named, at a weakly contractible object;
for sheaves of étale origin the sharper statement
$R^q\nu_{\overline X,*}\nu_{\overline X}^*\mathcal G=0$ for $q>0$, that
is with the bound $0$, is Stacks Project, Pro-étale Cohomology, Lemma
61.19.5,
[Tag 099V](https://stacks.math.columbia.edu/tag/099V), which is
[thm-sf-fullcd-etale-origin] with the bound $2d$ replaced by the
sharper one; Stacks Project, Pro-étale Cohomology, Example 61.19.12,
[Tag 0F6D](https://stacks.math.columbia.edu/tag/0F6D), names a sheaf
that is not of étale origin and computes none of its cohomology; and the
pro-étale chapter 61 contains no statement about a cohomological dimension
of the pro-étale site at all. The étale analogue of the missing bound is
classical and is a definition plus a theorem: the cohomological dimension
$\operatorname{cd}(f)$ is defined by the vanishing of $R^if_*\mathcal F$,
$i>\operatorname{cd}(f)$, for *every* abelian *torsion* sheaf
$\mathcal F$ on $X_{\Et}$, Stacks Project, Étale Cohomology,
Definition 59.96.1,
[Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z), and it is finite
for a morphism of finite type over a field, Lemma 59.96.2,
[Tag 0F10](https://stacks.math.columbia.edu/tag/0F10); the pro-étale
counterpart of neither exists in the sources recorded here. The one
class of non-constructible coefficients for which the blueprint has a name
is the sheafified quotient of clause (4) of
[lem-cbc-proetale-stalk-conservative], a nonzero sheaf with all
geometric-point stalks zero; the vanishing for it and its relatives is not
decided by anything in this manuscript either, no degree of its pro-étale
cohomology being computed anywhere in the chain, so this sheaf yields neither a
proof of the general form nor a counterexample to it; the counterexample that
refutes the general form is a different sheaf, the $F_G$ of
[rem-sf-fullcd-counterexample]. Consequently the
general form is not an open problem but a false statement, refuted by
*The all-sheaves, uniform-in-the-base-change form of the comparison bound is false* and
[rem-sf-fullcd-counterexample]; what survives, and what this manuscript
uses, is the class form: on the coefficient class
[def-sf-fullcd-used-class] the vanishing is the theorem
[thm-sf-fullcd-used-class], whose comparison bound is $M=0$ by
[prop-sf-comparison-bound-zero], so the statements that need only the
class form are unconditional on that class, as
[rem-sf-fullcd-reduction] states.
1. *What the search of the round of 18 September 2026 adds: the
reduction, the shape a counterexample must have, the concrete obstruction,
and the pages checked.* None of the four points below is a claim about the
truth of the general form; each is a fact about the recorded tools.
   1. **(a)** *On the source itself the étale factor is already bounded,
so only the vanishing degree of $R^q\nu_{\overline X,*}$ is missing there.*
For *every* sheaf $G$ of $A$-modules on the étale site of a
finite-type $k$-scheme $\overline X$ with $\dim\overline X\le d$ one has
$H^p(\overline X_{\Et},G)=0$ for $p>2d$: apply
[lem-sf-etale-direct-image-vanishing] to the structure morphism
$\overline X\to\operatorname{Spec}k$, whose target has trivial étale
cohomology because $k$ is algebraically closed, and read off the Leray
spectral sequence of [thm-sp-grothendieck], in which every term with
$p>0$ vanishes. Hence in the Leray spectral sequence
$E_2^{p,q}=H^p(\overline X_{\Et},R^q\nu_{\overline X,*}\mathcal F) \Rightarrow H^{p+q}(\overline X_{\Proet},\mathcal F)$ of the comparison
morphism the $p$-direction is bounded by $2d$ independently of
$\mathcal F$, and unbounded degrees can enter only through $q$: if
$R^q\nu_{\overline X,*}\mathcal F=0$ for every $q>M$ and every sheaf
$\mathcal F$ of $A$-modules on $\overline X_{\Proet}$, then
$H^r(\overline X_{\Proet},\mathcal F)=0$ for every $r>M+2d$. This is the
sense in which the étale factor of the comparison is not what is missing
on the source. It is *not* a statement about the base-changed sources
of [lem-sf-fullcd-detection-equivalence]: for $V\to Y$ in
$Y_{\Proet}$ the scheme $\overline X\times_YV$ is a pro-étale limit and
not of finite type over $k$, so the cited étale bound does not apply to
it, and the same reduction there would need that bound for the limit as
well. That second gap is recorded here rather than passed over; it is
exactly the gap that the continuity statement of
*Continuity for arbitrary sheaves implies the vanishing* closes on the limit
sources, *Continuity for arbitrary sheaves gives the full cohomological-dimension bound*(ii).
   1. **(b)** *The shape a counterexample must have: a coefficient sheaf whose
Čech complex along a weakly contractible hypercovering is unbounded.* By
Stacks Project, Pro-étale Cohomology,
Lemma 61.14.2,
[Tag 09A2](https://stacks.math.columbia.edu/tag/09A2), for a
hypercovering $K$ of a quasi-compact and quasi-separated object $U$ of
$T_{\Proet}$ whose terms $K_n=\{U_n\to U\}$ consist of weakly
contractible objects one has
$R\Gamma(U,\mathcal E)=\operatorname{Tot}(s(\mathcal E^\bullet(K)))$, and
by Lemma 61.14.1,
[Tag 09A1](https://stacks.math.columbia.edu/tag/09A1), such
hypercoverings exist with every $U_n$ affine and weakly contractible. The
construction puts no bound on the number of non-empty terms. If for some
object $U$ such a hypercovering were *bounded*, $K_n=\emptyset$ for
$n>N$, then its Čech complex would be concentrated in degrees
$0,\dots,N$ and $H^q(U,\mathcal F)=0$ for every $q>N$ and
*every* sheaf $\mathcal F$ of abelian groups. That hypothesis is
however never satisfied by a nonempty $U$: by
*No hypercovering of a nonempty object has an empty term* every hypercovering of a nonempty
object has a nonempty term in every degree, so the criterion is vacuous, and
*The question of a bounded weakly contractible hypercovering has a negative answer* records the consequence for the question
whether a bound on the length of a weakly contractible hypercovering exists
at all. The vanishing for $U=\operatorname{Spec}\bar k$ with $\bar k$
separably closed, which is the case of the sheaf of clause (4) of
[lem-cbc-proetale-stalk-conservative] referred to here, comes instead
from *The strictly henselian limit has no higher cohomology*(iii), and it is also what the criterion
*Vanishing above the degree in which the coefficient sheaf dies on the terms* gives, the constant hypercover
of $\operatorname{Spec}\bar k$ having terms that are acyclic for that sheaf and
on which that sheaf has no sections. A counterexample to the general form must
therefore exhibit a coefficient sheaf whose Čech
complex along a weakly contractible hypercovering of one of the
base-changed sources has cohomology in arbitrarily high degrees; the
unboundedness of the hypercovering is automatic by
*No hypercovering of a nonempty object has an empty term* and is no part of the obstruction, and
such a sheaf is constructed in [rem-sf-fullcd-counterexample], where the
role of the base-changed source is played by the pro-étale object $U$ and
the unbounded degrees are those of the coefficient sheaf $F_G$.
   1. **(c)** *The concrete obstruction, and why the one known
non-étale-origin sheaf cannot witness it.* The stalk of
$R^q\nu_{\overline X,*}\mathcal F$ at a geometric point $\bar x$ is the
filtered colimit of the groups $H^q(U_{\Proet},\mathcal F)$ over the étale
neighbourhoods $U$ of $\bar x$, whereas the object
$\operatorname{Spec}\mathcal O^{sh}_{\overline X,\bar x}$ at the limit of
that system is a *point* of the pro-étale topos: by Stacks Project,
Pro-étale Cohomology, Section 61.18,
[Tag 0991](https://stacks.math.columbia.edu/tag/0991), the functor
$\mathcal F\mapsto\mathcal F(\operatorname{Spec}\mathcal O^{sh})$ is the
geometric-point stalk functor $\mathcal F\mapsto\mathcal F_{\bar x}$ and it
is exact. Hence $H^q(\operatorname{Spec}\mathcal O^{sh}_{\overline X,\bar x},\mathcal F)=0$ for every $q>0$ and every sheaf $\mathcal F$,
which is now recorded as a proved statement,
*The strictly henselian limit has no higher cohomology*(iii), so that the sheafified quotient of
clause (4) of
[lem-cbc-proetale-stalk-conservative] — the sheaf $fun(-,A)/\underline A$ of Stacks Project, Pro-étale Cohomology, Example 61.19.12,
[Tag 0F6D](https://stacks.math.columbia.edu/tag/0F6D) — is acyclic on
every such object. What the two computations leave open is exactly the
comparison of the colimit of the $H^q$ over the neighbourhoods with the
$H^q$ of the object at the limit, a continuity statement which Stacks
records only for sheaves of étale origin: the values of the pullback of an
étale sheaf commute with the limit (Lemma 61.19.3,
[Tag 099S](https://stacks.math.columbia.edu/tag/099S)), the Čech
complexes of Lemma 61.19.4
([Tag 099U](https://stacks.math.columbia.edu/tag/099U)) are acyclic
there, and the resulting vanishing Lemma 61.19.5
([Tag 099V](https://stacks.math.columbia.edu/tag/099V)) is
[thm-sf-fullcd-etale-origin] with the bound $2d$ sharpened to $0$.
A counterexample must produce a class on the étale neighbourhoods of a
geometric point that survives every refinement, that is, a failure of this
continuity, and [rem-sf-fullcd-counterexample] produces one. That
continuity statement is isolated and
analysed in [rem-sf-continuity-obstruction]: it is *not* a
consequence of [lem-sf-etale-direct-image-vanishing], whose terms are
étale and not pro-étale cohomology groups of the models, whereas it does
imply the vanishing with the sharpest bound $M=0$,
*Continuity for arbitrary sheaves implies the vanishing*, and hence
$\operatorname{FullCD}(p,A;2d)$, *Continuity for arbitrary sheaves gives the full cohomological-dimension bound*; and it is
the statement that fails at the counterexample's base change, by
*The all-sheaves, uniform-in-the-base-change form of the comparison bound is false*. The residue of the general form was
therefore exactly that statement, and it is now a residue no longer: the
general form is false, and what the chapter uses is the class form
[thm-sf-fullcd-used-class], with the sharp comparison bound $M=0$ of
[prop-sf-comparison-bound-zero].
   1. **(d)** *Why the classical transplant fails, and the pages checked.*
The classical phenomenon of unbounded cohomology of arbitrary torsion
sheaves needs a base field of infinite cohomological dimension: for
$K=\mathbf R$ the constant sheaf $\mathbf Z/2$ has
$H^q(\operatorname{Spec}K_{\Et},\mathbf Z/2) =H^q(\mathbf Z/2,\mathbf Z/2)=\mathbf Z/2$ for *all* $q$, in the
pro-étale form as well as in the étale one by Stacks Project, Pro-étale
Cohomology, Lemma 61.22.1,
[Tag 09B4](https://stacks.math.columbia.edu/tag/09B4)
($H^i(\operatorname{Spec}k,\underline M^\wedge) =H^i_{\mathrm{cont}}(G,M)$). This is exactly what forces the hypothesis
$\operatorname{cd}(K)<\infty$ in Stacks Project, Étale Cohomology, Lemma
59.96.2, [Tag 0F10](https://stacks.math.columbia.edu/tag/0F10), whose
part (2) bounds $\operatorname{cd}(X)$ for finite-type $X/K$, the
definition being Definition 59.96.1,
[Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z), and the affine
bound being Proposition 59.95.6,
[Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
($\operatorname{cd}(X)\le\dim X+\operatorname{cd}(K)$). In the setting of
this remark $k$ is algebraically closed, so the residue field of every
point of every pro-étale base change is separably closed and no such
periodic Galois group occurs; the transplant of the $K=\mathbf R$ example,
of the skyscraper gadgets of the Zariski topology, and of the étale
cohomological-dimension theorem therefore produces no counterexample here.
Read in this round, each page fetched and compared with the claim made: the
Chapter 61 table of contents
([Tag 0965](https://stacks.math.columbia.edu/tag/0965), which contains
no section on a cohomological dimension of the pro-étale site) and its
Sections 61.13
([Tag 098I](https://stacks.math.columbia.edu/tag/098I),
[Tag 0990](https://stacks.math.columbia.edu/tag/0990)), 61.14
([Tag 09A1](https://stacks.math.columbia.edu/tag/09A1),
[Tag 09A2](https://stacks.math.columbia.edu/tag/09A2)), 61.15
([Tag 0994](https://stacks.math.columbia.edu/tag/0994)), 61.18
([Tag 0991](https://stacks.math.columbia.edu/tag/0991)), 61.19
([Tag 099R](https://stacks.math.columbia.edu/tag/099R), with Lemmas
61.19.3–61.19.6 and Example 61.19.12), 61.22
([Tag 09B4](https://stacks.math.columbia.edu/tag/09B4)), together with
Chapter 59's Sections 59.95
([Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)) and 59.96
([Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z),
[Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)). The full
Bhatt–Scholze paper was again not retrievable with the tools available here
(the PDF endpoints returned a network error and an unsupported content
type), so it was consulted only through the Stacks reproductions quoted
above, as Section 12 of the audit ledger records.

*The exact wording of the form that is false.* For a finite-type
$k$-scheme $\overline X$ with $\dim\overline X\leq d$, a proper
finite-type morphism $p:\overline X\to Y$ and a coefficient ring
$A=A_{E,n}$, form $(\mathrm{G})$ is the assertion that there is an integer
$M$ with

$$
(\mathrm{G})\qquad
R^q\nu_{\overline X,*}\mathcal F=0\qquad(q>M)
$$

for *every* sheaf $\mathcal F$ of $A$-modules on
$\overline X_{\Proet}$, uniformly over the base changes $V\to Y$ of
$Y_{\Proet}$; equivalently, by
[lem-sf-fullcd-detection-equivalence], the uniform bound on the
pro-étale cohomology of the base-changed sources. That assertion is
*false*: *The all-sheaves, uniform-in-the-base-change form of the comparison bound is false* exhibits an object
$U\to X_0$ of $X_{0,\Proet}$ and a sheaf $F_G$ of $A$-modules on
$U_{\Proet}$ with $R^q\nu_{U,*}F_G\neq0$ for arbitrarily large $q$, the
construction being recorded in [rem-sf-fullcd-counterexample]. It is the
quantification over *all* sheaves of $A$-modules, together with the
uniformity over the pro-étale base changes, that fails. On the blueprint's
coefficient class [def-sf-fullcd-used-class] the comparison bound holds
with $M=0$ by [prop-sf-comparison-bound-zero], and the vanishing
required by [def-weil-full-cohomological-dimension] therefore holds on
that class with the bound $2d$, which is [thm-sf-fullcd-used-class].
