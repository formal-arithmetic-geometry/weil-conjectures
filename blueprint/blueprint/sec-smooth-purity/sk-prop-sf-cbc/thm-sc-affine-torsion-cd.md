+++
id = "thm-sc-affine-torsion-cd"
kind = "theorem"
title = "The affine torsion cohomological dimension bound"
order = 1551
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-sc-etale-torsion-cd", "def-weil-pbc-scheme-conventions", "lem-kun-cd-sep-closed-point", "lem-sc-arbitrary-curve-cd", "lem-sc-cd-affine-limit", "lem-sc-cd-ground-field", "lem-sc-one-variable-field-cd", "lem-sc-support-dimension-union", "lem-weil-pbc-cohomology-filtered-colimit", "lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-torsion-filtered-union", "prop-weil-pbc-strict-henselization-stalk-formula", "thm-sp-grothendieck"]
+++
Let $K$ be a field with $\operatorname{cd}_{\rm tor}(K)\leq c$.
For any affine finite-type
$K$-scheme $X$, one has

$$
\operatorname{cd}_{\rm tor}(X)\leq\dim X+c,
$$

with both bounds understood as in [def-sc-etale-torsion-cd].

## Proof

We induct on $d=\dim X$, simultaneously over all ground fields.
Dimension zero follows from exact finite direct image
([lemma-weil-pbc-finite-direct-image-exact]) for the finite
structure map. Dimension one over an algebraically closed field
is [lem-sc-arbitrary-curve-cd], and
[lem-sc-cd-ground-field] gives it over all fields.
Suppose $d>1$ and that the result is established in smaller
dimensions over every field. It suffices to prove the result
over algebraically closed $K$, then apply
[lem-sc-cd-ground-field] again. We now assume $K$ algebraically
closed. Noether normalization gives a finite map
$X\to\mathbf A_K^d$. We use the elementary algebra theorem
[Stacks Project,
Tag 00OY](https://stacks.math.columbia.edu/tag/00OY). Exact finite direct image reduces to a sheaf $M$
on $\mathbf A^d$. We first take $M$ killed by an integer $n$.

*Local calculation in dimension $d$.*
Let $Y$ be smooth integral of dimension $d$ over $K$, and
let $j:Y\setminus D\to Y$ be the complement of an effective
Cartier divisor. At $y\in D$ put
$a=\operatorname{trdeg}_K\kappa(y)$ and
$R=\mathcal O^{\rm sh}_{Y,y}$. Choose lifts of a separating
transcendence basis of $\kappa(y)/K$.
Every nonzero polynomial in these lifts is a unit in $R$,
so they embed $K(t_1,\ldots,t_a)$ in $R$.
Hensel lifting, with the prescribed residues in the separably
closed residue field of $R$, extends this to an embedding of
its separable closure $F$ in $R$. Indeed each finite
separable extension has a primitive element with simple minimal
polynomial; its chosen residual root lifts uniquely, and these
unique lifts are compatible on finite subextensions.

The regular local ring $R$ is a domain, and its fraction
field is algebraic over $K(Y)$. Hence
$\operatorname{trdeg}_F\operatorname{Frac}(R)=d-a$.
If $f\in\mathfrak m_R$ is a local equation of $D$, then
$f\ne0$. A nonzero polynomial in $f$ over $F$ is a power
of $f$ times a unit: factor out its lowest nonzero power and
reduce the remaining expression modulo $\mathfrak m_R$.
Thus $F(x)$ embeds in $R[1/f]$ by $x\mapsto f$.
This ring is the filtered union of its finitely generated
$F(x)$-subalgebras, which are domains of dimension at most
$d-a-1<d$. The lower-dimensional induction hypothesis,
[lem-sc-one-variable-field-cd], and
[lem-sc-cd-affine-limit] give
$\operatorname{cd}_{\rm tor}(R[1/f])\leq d-a$.
The stalk formula
[prop-weil-pbc-strict-henselization-stalk-formula]
therefore gives $(R^qj_*M)_{\bar y}=0$ for $q>d-a$.
This calculation uses separating bases only over the
algebraically closed ground field.

*From the local calculation to affine space.*
Put $B=\mathbf A_K^{d-1}$, take
$j:\mathbf A^d\to\mathbf P^1\times B$, and write
$g:\mathbf P^1\times B\to B$ and $f=g j$.
For $q>0$, the sheaf $R^qj_*M$ is supported on
$D=\{\infty\}\times B$, since restriction to $\mathbf A^d$
is the higher direct image of the identity.
It equals $i_*N_q$ for $i:D\to\mathbf P^1\times B$,
as follows on stalks. Since $g i$ is an isomorphism and
finite direct image is exact,
$R^pg_*R^qj_*M=0$ for $p>0,q>0$.
Proper base change in
[cor-weil-pbc-geometric-fiber-finite] and the curve bound give
$R^pg_*j_*M=0$ for $p>2$: the geometric fibres of $g$ are
projective lines over the separably closed fields
$\kappa(z)^{{\mathrm{sep}}}$, and such a curve has torsion
cohomological dimension at most $2$, because
$\operatorname{cd}_{\rm tor}(\kappa(z)^{{\mathrm{sep}}})=0$
([lem-kun-cd-sep-closed-point]) while the projective line over the
algebraic closure has dimension at most $2$
([lem-sc-arbitrary-curve-cd]), the comparison
[lem-sc-cd-ground-field] transferring that bound to the separably
closed field.
The spectral sequence of [thm-sp-grothendieck] consequently
identifies $R^qf_*M$ with $g_*R^qj_*M$ for $q>2$;
the only possible exceptional differential would be
from bidegree $(0,1)$ to $(2,0)$, of total degrees one and two.
The local calculation implies that the stalks of $R^qf_*M$
vanish at points of transcendence degree greater than $d-q$
for $q>2$.

For $q=2$, the generic stalk formula identifies its stalk
at a geometric generic point of $B$ with
$H^2(\mathbf A^1_{\kappa(\eta)^{\rm sep}},M|)$.
This is zero by the dimension-one case already proved over
all fields, since a separably closed field has torsion
cohomological dimension zero, [lem-kun-cd-sep-closed-point]. Thus in this case too the
stalks vanish at points of transcendence degree greater than
$d-q=d-2$. This uses base change to a generic strict
localization, not a proper-base-change assertion for $f$.

*Cohomology of the resulting sheaves on $B$.*
If $N$ is zero at points of transcendence degree $>a$,
[lem-sc-support-dimension-union] writes it as a filtered
union of sheaves $N_Z$ supported on closed $Z\subset B$
of dimension at most $a$. Such a sheaf is $i_*i^*N_Z$,
and $Z$ is affine. Exact finite direct image and the
lower-dimensional induction hypothesis show
$H^p(B,N_Z)=0$ for $p>a$.
By [lem-weil-pbc-cohomology-filtered-colimit] the same
holds for $N$.
Apply this to $R^qf_*M$: for $q\geq2$ take $a=d-q$;
when $a<0$ all stalks vanish. For $q=0,1$, use the
induction bound $\dim B=d-1$ directly.
Every nonzero term of

$$
H^p(B,R^qf_*M)\ \Longrightarrow\ H^{p+q}(\mathbf A^d,M)
$$

has $p+q\leq d$. This proves the induction over algebraically
closed fields, and the earlier descent step completes it
over every field with the stated bound $c$.
Finally [lemma-weil-pbc-torsion-filtered-union], [lem-weil-pbc-cohomology-filtered-colimit]
removes the exponent bound on $M$.
