+++
id = "sk-prop-trace-adic"
kind = "section"
title = "Adic realization"
order = 2384
uses = ["sk-d-setup", "sk-d-six", "sk-d-weil", "sk-def-sf-weil-complexes", "sk-p-trace-coeff", "sk-prop-sf-trace-perfectness", "sk-thm-sf-ctf-stability"]
lean = ["AlgebraicGeometry.ProEtale.derivedComplete_limit_and_nonempty_iso_limit"]
+++
*Proposition (sketch).*

Write $A_n=A_{E,n}$. Call a system
$K_\bullet=(K_n,t_{n+1,n})_{n\ge1}$ with $K_n\in D^b_{ctf}(X,A_n)$
*normalized* if $K_n\otimes^{\mathrm L}_{A_n}A_j\xrightarrow{\sim}K_j$
for $j\le n$, and *uniform* if the $K_n$ share a cohomological range and
Tor amplitude.

3pt
1. **(i)** *Realization.* For a normalized uniform system the derived
limit $K_{\mathcal O_E}=R\varprojlim_nK_n$ is derived complete, lies in the
same range, and satisfies
$K_{\mathcal O_E}\otimes^{\mathrm L}_{\mathcal O_E}A_n\cong K_n$ for every
$n$, compatibly with the transitions.
1. **(ii)** *Compact cohomology and stalks.* The systems
$R\Gamma_c(X,K_n)$ and $(K_n)_{\bar y}$ are normalized systems of perfect
$A_n$-complexes, and realization commutes with both:
$$
R\Gamma_c(X,K_{\mathcal O_E})\cong R\varprojlim_nR\Gamma_c(X,K_n),
\qquad
(K_{\mathcal O_E})_{\bar y}\cong R\varprojlim_n(K_n)_{\bar y},
$$
both perfect over $\mathcal O_E$. If moreover $K_\bullet$ is a
*compatible tower of Weil pairs* — isomorphisms
$\varphi_n:\Phi_1^*K_n\xrightarrow{\sim}K_n$ as in [sk-d-weil] at every
level, i.e. strict Weil complexes at $A_n$ in the sense of
[sk-def-sf-weil-complexes], with
$t_{n+1,n}\circ\varphi_{n+1}=\varphi_n\circ\Phi_1^*t_{n+1,n}$ under the
coefficient identifications — or, more generally, carries a compatible
tower of Frobenius coefficient morphisms $\psi_n:\Phi_1^*K_n\to K_n$
satisfying the same compatibility, then the global and local Frobenius
operators of the levels form compatible families of endomorphisms of the
two towers, the realizations carry induced operators, and the displayed
isomorphisms are equivariant for them. For a bare normalized system no
Frobenius structure and no equivariance is asserted: a tower of skyscraper
sheaves at a point of $\mathbf A^1$ not fixed by $\Phi_1$ has moving
support and admits no $\varphi_n$ at any level.
1. **(iii)** *Rationalization and coefficient-field extension.*
$D^b_c(X,E)=D^b_c(X,\mathcal O_E)[1/\varpi]$ has the same objects as the
integral category and morphisms
$\operatorname{Hom}_{\mathcal O_E}(-,-)\otimes_{\mathcal O_E}E$; it is
idempotent complete, and the canonical functor to its Karoubi envelope is an
exact equivalence. Exact $\mathcal O_E$-linear functors and natural
transformations between integral categories transport to the rational ones.
Consequently every $E$-stage object is the rationalization of an integral
system — a lattice — and every $E$-stage morphism is $\varpi^{-N}u$ for
an integral $u$ and some $N$. The $\overline{\mathbf Q}_\ell$-stage is the filtered colimit over
finite $E/\mathbf Q_\ell$, so each of its objects and morphisms is already represented
at a finite stage.

These are the realization statements of
Bhatt–Scholze (§§6.5, 6.8; for the rationalization step (iii), 6.8.14 with
6.8.12–6.8.13) and, for the perfect towers over the point in (ii),
[Stacks, Tag 09AW](https://stacks.math.columbia.edu/tag/09AW).

## Proof

(i) Derived completeness: each $K_n$ is killed by $\varpi^n$, hence derived
$\varpi$-complete, and a derived limit of derived complete objects is derived
complete. The reduction isomorphisms do *not* come from local finite-free
models: constructibility and finite Tor amplitude provide such models on the
strata only, not across them (for $i:\{0\}\hookrightarrow\mathbf A^1$ the
tower $i_*A_n$ is normalized, flat and uniform, but its rank jumps at $0$).
They are formal. Since
$A_n=\operatorname{cone}(\varpi^n:\mathcal O_E\to\mathcal O_E)$ is perfect
over $\mathcal O_E$, the functor $-\otimes^{\mathrm L}_{\mathcal O_E}A_n$ is
a finite colimit and commutes with the exact functor $R\varprojlim$, so
$K_{\mathcal O_E}\otimes^{\mathrm L}_{\mathcal O_E}A_n\cong
R\varprojlim_j\bigl(K_j\otimes^{\mathrm L}_{\mathcal O_E}A_n\bigr)$. For
$j\ge n$ the complex
$A_j\otimes^{\mathrm L}_{\mathcal O_E}A_n=[A_j\xrightarrow{\varpi^n}A_j]$
has $H^0=A_n$ and $H^{-1}=\ker(\varpi^n\mid A_j)\cong A_n$, so its
canonical truncation triangle, tensored over $A_j$ with $K_j$, gives a
triangle
$K_n[1]\to K_j\otimes^{\mathrm L}_{\mathcal O_E}A_n\to K_j\otimes^{\mathrm L}_{A_j}A_n\cong K_n$,
functorial in $j$ (the last isomorphism is the normalization). In the tower
of first terms the transition
$\ker(\varpi^n\mid A_{j+1})\to\ker(\varpi^n\mid A_j)$ is multiplication by
$\varpi$ under the identifications with $A_n$, so the composite of $n$
consecutive transitions is $\varpi^n=0$ on $K_n$: the tower is pro-zero
and its derived limit vanishes (its shift endomorphism on the product is
nilpotent, so $1-\mathrm{shift}$ in the Roos triangle is invertible). The
third terms form the constant tower $K_n$. Hence
$K_{\mathcal O_E}\otimes^{\mathrm L}_{\mathcal O_E}A_n\cong K_n$, compatibly
with the transitions; neither constructibility nor uniformity enters, and
over the point $s$ this is the algebraic statement
[Stacks, Tag 09AW](https://stacks.math.columbia.edu/tag/09AW). For the
range: countable products are exact on the pro-étale site, so there are
exact sequences
$0\to R^1\!\varprojlim_jH^{i-1}(K_j)\to H^i(K_{\mathcal O_E})\to\varprojlim_jH^i(K_j)\to0$,
and in the top degree $b$ of the common range the maps
$H^b(K_{j+1})\to H^b(K_j)=H^b(K_{j+1})\otimes_{A_{j+1}}A_j$ are surjective
(right exactness of $\otimes$ in the top degree), so the $R^1\!\varprojlim$
term vanishes there and $K_{\mathcal O_E}$ lies in the common range;
uniformity of the bounds is what makes the limit stay in a fixed range. The
identification of these realizations with the derived-complete constructible
$\mathcal O_E$-complexes of the framework is the reconstruction statement of
the proper-base-change chapter (lem-weil-pbc-reconstruction-uniform-tower),
whose hypothesis of local finite-free models on a stratification is an
additional datum, not implied by the hypotheses here.

(ii) Each level is perfect by [sk-prop-sf-trace-perfectness], and the
transitions are morphisms of perfect complexes by naturality of
$R\Gamma_c$ and of stalks; normalizedness of the two systems is
normalizedness of $K_\bullet$ together with the coefficient-reduction
isomorphisms for $Ra_{X!}$ and for $L\bar y^*$, which hold by
[sk-thm-sf-ctf-stability]. Over the point $s$ the realization of a
normalized tower of perfect $A_n$-complexes is the algebraic statement
[Stacks, Tag 09AW](https://stacks.math.columbia.edu/tag/09AW), kept
separate from (i): the derived limit is perfect and derived complete over
the complete ring $\mathcal O_E$ and reduces to the levels, with no
uniformity hypothesis. Applied to $R\Gamma_c(X,K_n)$ and to
$(K_n)_{\bar y}$ it gives the right-hand sides; the displayed isomorphisms
then express that compact cohomology and geometric stalks at the
$\mathcal O_E$-stage, which are defined levelwise on the normalized systems
of [sk-d-setup] and agree with the pro-étale functors by
[sk-thm-sf-ctf-stability], commute with the realization of (i).
Equivariance requires the extra datum. Given a compatible tower $\psi_n$
(in particular a compatible tower of Weil pairs $\varphi_n$), the global
and local operators $F_{c,m}(\psi_n)$ and $(\psi_{n,m})_{\bar y}$ are built
from $\psi_n$ by pullback, units, counits and the composition law, all
natural in the coefficient and compatible with coefficient reduction, and
the compatibility condition says exactly that $\psi_{n+1}$ reduces to
$\psi_n$; hence they form compatible families of endomorphisms of the two
normalized towers of perfect complexes. A compatible family lifts to an
endomorphism of the realization (represent the tower by minimal finite free
models with surjective reductions, as in Stacks 09AW, and lift the matrices
step by step), its trace reduces to the levelwise traces, and the displayed
isomorphisms intertwine the lifted operators with the derived limits of the
families, which is the asserted equivariance. Without such a tower there is
no operator on the realization to be equivariant for.

(iii) All of this is the construction of the rational category: it is
*defined* as the localization $D^b_c(X,\mathcal O_E)[1/\varpi]$, with the
same objects and with morphisms tensored up to $E$, so the descent of
field-stage objects to integral models is tautological and clearing
denominators is writing an element of
$\operatorname{Hom}\otimes_{\mathcal O_E}E$ as $\varpi^{-N}u$. Idempotent
completeness, and hence the equivalence with the Karoubi envelope, is proved
from the localized $t$-structure; transport of exact functors and of natural
transformations is their $\mathcal O_E$-linearity. For $\overline{\mathbf Q}_\ell$, a filtered
colimit of categories has every object and every morphism represented at a
finite stage, and two representatives agree after a further finite extension.

Uses: [sk-d-setup], [sk-d-six], [sk-d-weil], [sk-def-sf-weil-complexes], [sk-p-trace-coeff], [sk-prop-sf-trace-perfectness], [sk-thm-sf-ctf-stability]
