+++
id = "rem-sf-fullcd-reduction"
kind = "remark"
title = "What $\\operatorname{FullCD}$ supplies, and what would discharge it"
order = 2054
uses = ["cor-sf-fullcd-weakly-contractible-test", "def-sf-fullcd-class", "def-sf-fullcd-used-class", "def-weil-ambient-exceptional-adjoint", "def-weil-exceptional-adjoint-admissibility", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-full-cohomological-dimension", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-site", "def-weil-pbc-site-comparison-morphism", "lem-cbc-proetale-stalk-conservative", "lem-sf-etale-direct-image-vanishing", "lem-sf-fullcd-detection-equivalence", "lem-sf-proetale-constructible-origin", "lem-sf-proetale-vanishing-detection", "open-sf-ambient-adjoint-input", "prop-sf-comparison-bound-zero", "rem-sf-fullcd-counterexample", "rem-sf-fullcd-general-form", "thm-sc-finite-type-torsion-cd", "thm-sf-ambient-adjoint-class", "thm-sf-fullcd-class", "thm-sf-fullcd-etale-origin", "thm-sf-fullcd-used-class", "thm-sp-grothendieck"]
+++
The named interface [open-sf-ambient-adjoint-input] turns on the full
cohomological-dimension condition
[def-weil-full-cohomological-dimension] for the compactification of a
general separated finite-type morphism. Three things about that condition
can now be said exactly.

1. *Its torsion half is a theorem, on the étale site and
independently of the coefficient stage.* For the étale site the
vanishing required by $\operatorname{FullCD}$ holds for every sheaf of
$A$-modules, with the bound $2d$ for a source of dimension at most
$d$, by [lem-sf-etale-direct-image-vanishing]; that lemma quantifies
over all finite-type morphisms, proper or not, and its bound is the one of
[thm-sc-finite-type-torsion-cd], which depends only on the dimension
and on the torsion cohomological dimension of the ground field, hence not
on the coefficient ring $A_{E,n}$.
1. *The same bound is a theorem for every coefficient sheaf of
étale origin, and the comparison bound there is the sharp $M=0$.*
[thm-sf-fullcd-etale-origin] transfers the bound
$2d$ of clause (1) to the small pro-étale site along the comparison
direct image for every sheaf $\mathcal F\cong\nu_{\bar X}^*\mathcal G$
pulled back from an étale sheaf $\mathcal G$, uniformly over the base
changes; the comparison bound itself is $0$ on that class, by
[prop-sf-comparison-bound-zero], the residual $2d$ being the étale
direction of the Leray spectral sequence of [thm-sp-grothendieck]. The
general form, quantified over *all* pro-étale module sheaves and
uniformly over the pro-étale base changes, is *false*, by
*The all-sheaves, uniform-in-the-base-change form of the comparison bound is false* and
[rem-sf-fullcd-counterexample]: the counterexample's sheaf $F_G$ is a
sheaf of $A$-modules on a pro-étale base change $U$ of a base $X_0$,
not of étale origin, whose comparison direct images fail to vanish in
unboundedly many degrees. Constructibility is exactly the dividing line
here: [lem-sf-proetale-constructible-origin] identifies the
constructible pro-étale coefficients with the étale ones, so the class on
which the bound holds is the blueprint's coefficient class
[def-sf-fullcd-used-class], while the sheafified quotient of clause (4)
of [lem-cbc-proetale-stalk-conservative] and the sheaf $F_G$ of
[rem-sf-fullcd-counterexample] lie outside it.
1. *What remains can be tested without geometric-point stalks.*
Let $\nu_{\bar X}:\bar X_{\mathrm{proet}}\to\bar X_{\Et}$
be the comparison morphism and let $\mathcal F$ be a sheaf of $A$-modules
on $\bar X_{\mathrm{proet}}$. The Grothendieck spectral sequence of the
composite of the two section functors
$\Gamma(\bar X_{\mathrm{proet}},-)=\Gamma(\bar X_{\Et},-)\circ\nu_{\bar X,*}$
is [thm-sp-grothendieck], and it reads
$$
E_2^{p,q}=H^p\bigl(\bar X_{\Et},R^q\nu_{\bar X,*}\mathcal F\bigr)
\Longrightarrow H^{p+q}\bigl(\bar X_{\mathrm{proet}},\mathcal F\bigr).
$$
Each $R^q\nu_{\bar X,*}\mathcal F$ is a torsion étale sheaf of
$A$-modules, so clause (1) makes $E_2^{p,q}=0$ for
$p>2\dim\bar X$; hence a bound
$R^q\nu_{\bar X,*}\mathcal F=0$ for $q>M$, uniform in $\mathcal F$,
would give $\operatorname{FullCD}(p,A;2\dim\bar X+M)$, and the same
argument applied to the fibres of the base changes gives the relative form.
For such a bound, and for $\operatorname{FullCD}$ itself, the geometric
point stalks need not be consulted: by
[lem-sf-proetale-vanishing-detection] vanishing on the pro-étale
site is detected by evaluation at the affine weakly contractible objects,
and by [cor-sf-fullcd-weakly-contractible-test] the condition
$\operatorname{FullCD}(p,A;c)$ is therefore equivalent to the vanishing
of the finitely many evaluations recalled there, so the failure of
conservativity of the geometric-point stalks recorded in clause (4) of
[lem-cbc-proetale-stalk-conservative] does not by itself obstruct the
test. What that test does not supply is a bound: the evaluations are
cohomology groups of the pro-étale site of the base-changed source, and
no recorded statement bounds them for the module sheaves that are not of
étale origin – clause (2) is the only case in which a bound is known, and
in general the bound fails, by
*The all-sheaves, uniform-in-the-base-change form of the comparison bound is false*. The implication that would have
supplied such a bound is recorded here, and its hypothesis is now known to
fail in general: by *Continuity for arbitrary sheaves implies the vanishing* the
continuity statement $(\mathrm{C}_q)$ recorded there — every cohomology
class on an étale neighbourhood of a geometric point dies after refinement,
equivalently the cohomology of the limit object is the colimit of the
cohomologies of its finite-type models, the limit object itself having no
higher cohomology for any sheaf by *The strictly henselian limit has no higher cohomology* — gives
$R^q\nu_{\bar X,*}\mathcal F=0$ for *every* $q\ge1$, that is, the
sharpest bound $M=0$, and then
$\operatorname{FullCD}(p,A;2\dim\bar X)$ by
*Continuity for arbitrary sheaves gives the full cohomological-dimension bound*, so that the bound of this item would improve
from $2\dim\bar X+M$ to $2\dim\bar X$. The counterexample of
[rem-sf-fullcd-counterexample] shows, through the contrapositive of that
theorem, that $(\mathrm{C}_q)$ fails at its base change $U$ in the degrees
in which $R^q\nu_{U,*}F_G\neq0$, so that continuity cannot be the residue in
that generality; its terms are pro-étale, not étale, cohomology groups of
the models, hence it is not obtained from
[lem-sf-etale-direct-image-vanishing] either, as
[rem-sf-continuity-obstruction] records, and the form in which
*Continuity for arbitrary sheaves gives the full cohomological-dimension bound* consumes it is the one for the finite-type
models.

Accordingly the general form, on all sheaves, is not merely unproved: it is
*false*, by *The all-sheaves, uniform-in-the-base-change form of the comparison bound is false* and
[rem-sf-fullcd-counterexample], so the ambient datum
[def-weil-ambient-exceptional-adjoint] is read *on the
blueprint's coefficient class* [def-sf-fullcd-used-class], where
clause (1) of [def-weil-exceptional-adjoint-admissibility] is a theorem
in *both* of its halves: the vanishing half is the class-restricted
datum [def-sf-fullcd-class], supplied with the bound $2\dim\bar X$ and
uniformly over the base changes by [thm-sf-fullcd-class], and the
existence half, with its unit, counit and compactification comparisons, is
the theorem [thm-sf-ambient-adjoint-class]; the interface
[open-sf-ambient-adjoint-input] therefore no longer names the existence
half on that class, and what it still names – the adjunction for the
complexes outside the class – is analysed in
[rem-sf-class-adjoint-residue].
Two consequences of the class form [thm-sf-fullcd-used-class] are worth
recording here. First, every coefficient sheaf of that class satisfies the
vanishing required by $\operatorname{FullCD}$, with the bound
$2\dim\bar X$ and uniformly over the base changes, and the comparison bound
itself is $M=0$ by [prop-sf-comparison-bound-zero], so that for the
coefficient categories this manuscript
actually uses – the bounded constructible and finite-Tor categories of
[def-weil-finite-torsion-constructibility] and
[def-weil-finite-tor-amplitude], whose coefficient sheaves are
constructible by construction – the full-cohomological-dimension input of
the ambient datum is a theorem on the restricted input and not a hypothesis;
what the ambient datum still assumes on those categories is nothing beyond
that theorem and [thm-sf-ambient-adjoint-class]: the existence half, which
*Ambient exceptional right adjoint* derives from clause (1) for the
unrestricted input, is on the class the cited theorem. Second, the general form of the condition,
quantified over arbitrary pro-étale module sheaves and uniformly over the
base changes, is by
[lem-sf-fullcd-detection-equivalence] the uniform bound on the
pro-étale cohomology of the base-changed sources, and it is refuted by
[rem-sf-fullcd-counterexample], as
[rem-sf-fullcd-general-form] records.
