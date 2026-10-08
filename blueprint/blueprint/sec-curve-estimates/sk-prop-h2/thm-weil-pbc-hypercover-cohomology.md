+++
id = "thm-weil-pbc-hypercover-cohomology"
kind = "theorem"
title = "Cohomology is computed after hypercover refinement"
order = 949
uses = ["def-weil-pbc-etale-cohomology", "def-weil-pbc-finite-split-hypercover", "lem-weil-pbc-hypercover-free-resolution", "lem-weil-pbc-hypercover-refinement"]
+++
For a quasi-compact quasi-separated scheme $X$, an abelian etale sheaf $F$,
and $q\geq0$, there is a natural isomorphism

$$
 \varinjlim_{U}H^q(C^\bullet(U,F))
 \xrightarrow{\sim} H^q(X_{\Et},F).
$$

The limit is over refinements, modulo simplicial homotopy, of the hypercovers
finite in each degree [def-weil-pbc-finite-split-hypercover]. The right side
is the derived cohomology of [def-weil-pbc-etale-cohomology]. A
representative, and a relation between representatives, use only finitely
many degrees. The same assertion holds for sheaves of modules over a fixed
constant ring, with cohomology derived in that module category.

## Proof

Choose an injective resolution $F\to I^\bullet$, in degrees $r\geq0$, to
compute the cohomology of [def-weil-pbc-etale-cohomology]. For each $U$, form
the first-quadrant double complex $D^{p,r}=I^r(U_p)$ with total differential
$\delta+(-1)^p d_I$. By [lem-weil-pbc-hypercover-free-resolution], its
augmented rows are exact. Taking horizontal cohomology first therefore shows
that

$$
 \Gamma(X,I^\bullet)\longrightarrow\operatorname{Tot}D
$$

is a quasi-isomorphism. This uses only finite sums in each total degree. The
inclusion $F\to I^\bullet$ now gives the asserted map from hypercover
cohomology to derived cohomology.

We prove its surjectivity without declaring a single hypercover acyclic for
$F$. Represent a degree-$q$ class by a total cocycle. Its component in
bidegree $(0,q)$, if $q>0$, is $d_I$-closed. Exactness of the resolution as a
complex of sheaves makes it locally a $d_I$-boundary. By
[lem-weil-pbc-hypercover-refinement], refine to choose a primitive, and
subtract its total coboundary. The component $(0,q)$ is now zero. The cocycle
equation makes the component $(1,q-1)$ vertically closed. If $q-1>0$, repeat,
with the sign $(-1)^1$ in its primitive. After the finitely many positions
$(p,q-p)$ with $q-p>0$, only $(q,0)$ remains. It is vertically closed, hence
lies in $F(U_q)$, and its horizontal differential is zero. It is the required
representative in $C^\bullet(U,F)$.

For injectivity, suppose a degree-$q$ cocycle in this last complex is a total
boundary. Choose a total primitive of degree $q-1$. Its positive
vertical-degree components are vertically closed in the same successive
order, because its differential has only vertical degree zero. After
refinement subtract total coboundaries from the primitive to remove these
components. The remaining primitive lies in $F(U_{q-1})$. Thus the original
cocycle is already a boundary after refinement. For $q=0$, injectivity
instead follows directly from the injectivity of $F\to I^0$. For two
representatives first take a common refinement and apply this argument to
their difference. Homotopic refinements induce equal cohomology maps by the
prism identity in [lem-weil-pbc-hypercover-refinement]. This proves the
displayed isomorphism and its naturality. All operations used only a finite
truncation as defined in [def-weil-pbc-finite-split-hypercover]; the cocycle
condition uses degree $q+1$. This gives the finite-cover version of
[Stacks Project, Tag 01H0](https://stacks.math.columbia.edu/tag/01H0). The
colimit here is taken on cohomology groups; no colimit of complexes indexed
by the homotopy category is used. For module coefficients, take an injective
resolution in the module category and use the free-module version of
[lem-weil-pbc-hypercover-free-resolution]; every subsequent local lifting and
double-complex calculation is unchanged.
