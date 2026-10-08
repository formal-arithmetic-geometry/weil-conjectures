+++
id = "lem-sf-etale-direct-image-vanishing"
kind = "lemma"
title = "Vanishing of the higher direct images above the dimension"
order = 1790
uses = ["def-sc-etale-torsion-cd", "def-sf-uniform-direct-image-vanishing", "def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "fin4-lem-fibrewise-cohomological-dimension", "lem-kun-cd-stalk-criterion", "lem-kun-dimension-formula", "lem-sf-separably-closed-torsion-cd", "lem-weil-pbc-qcqs-higher-direct-image", "lemma-weil-pbc-geometric-stalk-conservative", "thm-sc-finite-type-torsion-cd"]
+++
Let $k$ be an algebraically closed field, let $X,Y$ be finite-type
$k$-schemes with $\dim X\leq d$, let $f:X\to Y$ be a finite-type
morphism and let $A$ be a finite ring annihilated by an integer
invertible in $k$. Then the higher direct images of $f$ on the
small étale sites satisfy
$R^qf_*M=0$ for every $q>2d$ and every sheaf $M$ of $A$-modules on
$X_{\Et}$; that is, $\operatorname{UDV}(f,A;2d)$ holds in the sense of
[def-sf-uniform-direct-image-vanishing]. Separatedness of $f$ is
not needed.

## Proof

A sheaf of $A$-modules is a torsion sheaf of abelian groups, $A$ being
finite. By [lemma-weil-pbc-geometric-stalk-conservative] a sheaf on the
small étale site of $Y$ vanishes as
soon as all of its geometric stalks do, so it suffices to prove that
$(R^qf_*M)_{\bar y}=0$ for $q>2d$ at every geometric point
$\bar y\to Y$.

Fix such a point. The stalk of a sheaf on the small étale site is the
filtered colimit of its sections over the pointed étale neighbourhoods,
and [lem-weil-pbc-qcqs-higher-direct-image] evaluates the sheaf
$R^qf_*M$ of [def-weil-pbc-direct-image] on an étale object
$W\to Y$ as $H^q(W\times_YX,M|)$; the morphism $f$ is of finite type,
hence quasi-compact and quasi-separated, so

$$
(R^qf_*M)_{\bar y}
=\varinjlim_{(W,\bar w)}H^q\bigl(W\times_YX,M|\bigr),
$$

the colimit running over the pointed étale neighbourhoods of $\bar y$, as in [lem-kun-cd-stalk-criterion].

Each $W\times_YX$ is a finite-type $k$-scheme, and it has dimension at
most $d$: for a point $z\in W\times_YX$ with image $x\in X$ the
morphism $W\times_YX\to X$ is étale, so
$\mathcal O_{W\times_YX,z}$ is an étale local algebra over
$\mathcal O_{X,x}$ with finite separable residue extension, the two local
rings have the same dimension, and [lem-kun-dimension-formula]
computes the two local dimensions as the dimension at the point minus the
transcendence degree of the residue field over $k$; those transcendence
degrees agree because $\kappa(z)/\kappa(x)$ is finite separable. Hence
$\dim_z(W\times_YX)=\dim_xX\leq\dim X\leq d$.

The field $k$ is algebraically closed, so
$\operatorname{cd}_{\rm tor}(k)\leq0$ by
[lem-sf-separably-closed-torsion-cd], and
[thm-sc-finite-type-torsion-cd] with $c=0$ gives
$H^q(W\times_YX,M|)=0$ for $q>2d$, for every torsion sheaf $M|$; this
is the statement recorded for constructible coefficients as
[fin4-lem-fibrewise-cohomological-dimension]. Every group of the
colimit above is therefore zero, so the stalk vanishes, and with all stalks
the sheaf.
