+++
id = "thm-sp-if-e1"
kind = "theorem"
title = "Hypercohomology spectral sequence via a Cartan--Eilenberg resolution"
order = 522
uses = ["def-sp-convergence", "def-sp-double-complex-total", "def-sp-injective-resolutions", "def-sp-kinjective-bridge", "def-sp-left-exact-additive", "def-sp-truncation-couple", "lem-sp-kinjective-computes", "thm-sp-double-complex-spectral-sequences", "thm-sp-spectral-object-yields"]
+++
Let $v$ be as in [def-sp-truncation-couple] and let $A^{\bullet,\bullet}$ be
a Cartan--Eilenberg resolution of a bounded-below complex $K^\bullet$: the
row $A^{\bullet,s}$ is an injective resolution
[def-sp-injective-resolutions] of $K^s$, and the column cohomologies are the
$\mathcal H^s(K^\bullet)$. Then the filtration of the total complex by the
*second* degree gives the spectral sequence

$$
 E_1^{r,s}=R^rv(K^s)\Longrightarrow
 \mathcal H^{r+s}(RvK^\bullet),
$$

$d_1:E_1^{r,s}\to E_1^{r,s+1}$, induced by the differential of $K^\bullet$,
and the abutment is the cohomology of the derived functor of $K^\bullet$,
independent of the resolution.

**Status.** The proof formerly invoked Stacks Tags 0130/0131 for the whole
bicomplex spectral sequence without constructing it. It is now an application
of [thm-sp-spectral-object-yields] to the total complex of the double complex
with its second-degree filtration ([def-sp-double-complex-total],
[thm-sp-double-complex-spectral-sequences] (II)), together with the standard identification
of the row cohomology with the derived functors.

It also formerly asserted that a Cartan--Eilenberg resolution computes the
derived functor of a complex, attributing that to
[def-sp-left-exact-additive], which defines derived functors only on objects,
and then took independence of the resolution from
[lem-sp-kinjective-computes], whose own proof appealed back to this theorem.
$Rv$ on complexes is now defined once, in [def-sp-kinjective-bridge], and both
steps are readings of that definition. The dependence runs one way: this
theorem uses the lemma, the lemma does not use this theorem.

## Proof

Each row $A^{\bullet,s}$ is an injective resolution of $K^s$, so the entries
$R^rv(K^s)$ are the $r$-th cohomology of $v(A^{\bullet,s})$ by
[def-sp-injective-resolutions]. Apply [thm-sp-spectral-object-yields] to the
total complex
$K^\bullet:=\operatorname{Tot}\bigl(v(A^{\bullet,\bullet})\bigr)$ with its
decreasing filtration by the second degree,
$F^sK^\bullet:=\bigoplus_{s'\geq s}v(A^{\bullet,s'})$. This is a filtration
by subcomplexes: the total differential preserves the second degree in its
first summand and raises it in its second, so $\bigoplus_{s'\geq s}$ is
stable. It is bounded in each degree, because a total degree receives only
finitely many rows, the complex $K^\bullet$ being bounded below. The graded
pieces are $\operatorname{gr}^sK^\bullet=\operatorname{Tot}
\bigl(v(A^{\bullet,s})\bigr)$, so item (a) of that theorem gives

$$
 E_1^{r,s}=H^{r+s}\bigl(\operatorname{Tot}(v(A^{\bullet,s}))\bigr)
 =H^r\bigl(v(A^{\bullet,s})\bigr)=R^rv(K^s),
$$

the middle identification being the standard one for a complex concentrated
in a single degree of the second index, and the differential $d_1$ being the
boundary homomorphism of the filtration, which is induced by the differential
of $K^\bullet$ because the rows are resolutions of the $K^s$ and the maps
between them come from $K^\bullet$. Item (b) of the same theorem identifies
the abutment with the cohomology of the total complex, $\mathcal
H^{r+s}(\operatorname{Tot}(v(A^{\bullet,\bullet})))$.

It remains to identify that with $\mathcal H^{r+s}(RvK^\bullet)$, for the
derived functor on $\operatorname{Ch}^+$ of [def-sp-kinjective-bridge]. In
total degree $n$,

$$
 \operatorname{Tot}(A^{\bullet,\bullet})^n=
 \bigoplus_{r+s=n}A^{r,s},
$$

a *finite* direct sum: the rows are resolutions, so $A^{r,s}=0$ for $r<0$, and
$K^\bullet$ is bounded below, so $A^{r,s}=0$ for $s$ below some $s_0$. A
finite direct sum of injectives is injective, so
$\operatorname{Tot}(A^{\bullet,\bullet})$ is a bounded-below complex of
injectives, hence K-injective by part (2) of [lem-sp-kinjective-computes]. The
augmentation $K^\bullet\to\operatorname{Tot}(A^{\bullet,\bullet})$ of a
Cartan--Eilenberg resolution of a bounded-below complex is a
quasi-isomorphism, so it is a K-injective resolution of $K^\bullet$ and

$$
 RvK^\bullet\cong v\bigl(\operatorname{Tot}(A^{\bullet,\bullet})\bigr)
 =\operatorname{Tot}\bigl(v(A^{\bullet,\bullet})\bigr),
$$

the second equality because $v$ is additive
[def-sp-left-exact-additive] and the total complex is a finite direct sum in
each degree. Independence of the chosen Cartan--Eilenberg resolution is part
(1) of [lem-sp-kinjective-computes]: any two K-injective resolutions of
$K^\bullet$ give canonically isomorphic values.
