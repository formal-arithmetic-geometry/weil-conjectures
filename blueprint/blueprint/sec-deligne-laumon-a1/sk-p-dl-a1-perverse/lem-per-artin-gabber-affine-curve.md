+++
id = "lem-per-artin-gabber-affine-curve"
kind = "lemma"
title = "Affine pushforward is perverse up to the relative dimension"
order = 2743
uses = ["def-per-perverse-subcategories", "def-weil-derived-cohomology-sheaves", "def-weil-open-closed-recollement", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions", "fix-cor-verdier-exchange", "lem-sc-cohomological-dimension", "lemma-weil-pbc-etale-cohomology-continuity", "prop-sf-open-closed-triangle-all-stages"]
+++
Let $f:X\to Y$ be an
affine morphism of finite
type between separated schemes of finite type over a field $k$,
whose geometric fibers have dimension at most $d$ (the instance used
here is $d=1$: the projection
$p_2:\mathbf A^1_{k_0}\times\mathbf A^1_{k_0}\to\mathbf A^1_{k_0}$
and its base changes). Then

$$
Rf_!\bigl({}^pD^{\le0}(X)\bigr)\subset{}^pD^{\le d}(Y),\qquad
Rf_!\bigl({}^pD^{\ge0}(X)\bigr)\subset{}^pD^{\ge -d}(Y).
$$

In the relative-dimension-one instance the $!$-pushforward is exact
for the perverse subcategories up to the shift by one.

## Proof

This is Artin–Gabber in the form *the compact-support
pushforward along an affine morphism with fibers of dimension at most
$d$ has perverse amplitude $\le d$* (Beilinson–Bernstein–Deligne,
*Faisceaux pervers*, Asterisque 100 (1982), Chapitre 4, § 4.1.2;
the proof is the one summarized below). The cohomological dimension input
of that classical statement has the following Stacks Project entries, read
verbatim: the affine vanishing theorem for an affine scheme of finite type
over a field is Proposition 59.95.6,
[Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
($\operatorname{cd}(X)\leq\dim(X)+\operatorname{cd}(K)$); its relative form
for an affine morphism of finite type over a field is Lemma 59.95.8,
[Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X) (if
$\mathcal F$ is supported in the locus $E_a(X)$ of points of
transcendence degree $\leq a$, then $R^qf_*\mathcal F$ is supported in
$E_{a-q}(Y)$); the notion of cohomological dimension is Definition 59.95.1,
[Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q); and the vanishing
on such loci is Lemma 59.95.7,
[Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W). The estimates
quoted in Step 1 below are the ones proved in this blueprint
([lem-sc-cohomological-dimension]).

Step 1 (the fibre range). The fibers of $f$ have dimension at most
$d$, and over the base of the finite-type morphism the relative
cohomological range is that of a scheme of dimension $\le d$: for a
constructible sheaf $G$ on $X$ the higher direct images satisfy
$R^af_!G=0$ for $a>2d$ (the cohomological dimension estimates
$\operatorname{cd}_\ell\le2\dim$ of
[lem-sc-cohomological-dimension] of the Jacobian chapter at the
finite-torsion levels, with the adic passage of the etale-cohomology
continuity [lemma-weil-pbc-etale-cohomology-continuity] of
the ambient-foundations chapter; for $d=0$ this is the concentration of a finite
scheme, for $d=1$ the range of a curve $a\le2$ – for the affine
fibers of the affine morphism $f$ the sharper affine-Lefschetz
range $a\le1$ applies as well, but the $2d$-bound is the one that
is needed below, since the relative degree contribution of the blocks
absorbs the shift by $d$ but not $2d$).

Step 2 (the $\le$-direction on the generating blocks). By the middle
perverse $t$-structure on a curve, in the form of the perverse
truncation functors and of the generating blocks of the perverse heart
(the punctual objects $i_{x,*}H$, the extensions by zero
$j_!\mathcal F[1]$, and the middle extensions $j_*\mathcal F[1]$,
Beilinson–Bernstein–Deligne, *Faisceaux pervers*, Chapitre 1,
§§ 1.3–1.4), it suffices to check the two inclusions of
[def-per-perverse-subcategories] on those blocks and to use the
extension closure: a punctual block
$K=i_{x,*}H$ has $Rf_!K$ supported in finitely many points with
the same degree behaviour (the finite-morphism behaviour of the closed
point, degree concentration $a=0$), which lies in ${}^pD^{\le d}$;
a middle-extension block of the open type $j_*\mathcal F[1]$ with
the relative curve sits over the relative open with fibers of
dimension at most one and the relative degree range of Step 1 (degree
contribution $a\le1$), whose support dimension plus the relative
dimension contribution is shifted by exactly the $d=1$ amount, so
that the object lies in ${}^pD^{\le1}$. The extension closure and
the truncation induction complete the $\le$-direction in the
standard Artin–Gabber argument.

Step 3 (the $\ge$-direction). By the duality symmetry of the middle
perverse $t$-structure (Beilinson–Bernstein–Deligne, *Faisceaux
pervers*, Chapitre 1, § 1.3.6), $K\in{}^pD^{\ge0}(X)$ is equivalent to
$D_XK\in{}^pD^{\le0}(X)$, and the Verdier exchange
[fix-cor-verdier-exchange] for the affine morphism gives
$D_Y(Rf_!K)\cong Rf_*(D_XK)$. The cosupport condition of $Rf_!K$
is therefore equivalent to the support condition of $Rf_*(D_XK)$,
i.e. to the *$\le$-assertion for $Rf_*$* applied to
$D_XK$. That assertion is proved by the argument of Step 2 with
$f_!$ replaced by $f_*$: the duality symmetry also exchanges the
roles of $f_!$ and $f_*$ in the block analysis (a punctual block
is finite on either side, and a middle-extension block satisfies the
same degree range with $j_*$ as it does with $j_!$, the difference
being concentrated in the relative boundary, whose contribution is
absorbed in the same $d$-shift by the open–closed recollement
triangle [def-weil-open-closed-recollement] (at $\Qlb$, [prop-sf-open-closed-triangle-all-stages]), in the form of the
boundary sequence of the middle extension of loc. cit., § 1.4).
Hence $Rf_!K\in{}^pD^{\ge -d}(Y)$.
