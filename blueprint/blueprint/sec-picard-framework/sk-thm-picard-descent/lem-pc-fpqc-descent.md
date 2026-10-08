+++
id = "lem-pc-fpqc-descent"
kind = "lemma"
title = "FPQC descent for quasi-coherent modules"
order = 763
uses = ["def-sc-invertible-module"]
lean = ["AlgebraicGeometry.bijective_toDescentData_map", "AlgebraicGeometry.exists_isQuasicoherent_toDescentData_iso", "AlgebraicGeometry.isFinitePresentation_of_toDescentData_iso", "AlgebraicGeometry.isLocallyFree_of_toDescentData_iso", "AlgebraicGeometry.isInvertible_of_toDescentData_iso"]
+++
(Descent, Proposition 35.5.2, Tag
[023T](https://stacks.math.columbia.edu/tag/023T), and Descent,
Section 35.7.) Let $\{f_i:S_i\to S\}_{i\in I}$ be an fpqc covering of
schemes.

1. The functor $\mathcal{M}\mapsto(f_i^*\mathcal{M},\mathrm{can})_{i\in I}$
from quasi-coherent $\mathcal{O}_S$-modules to descent data of
quasi-coherent modules for this covering (quasi-coherent
$\mathcal{O}_{S_i}$-modules $\mathcal{M}_i$ with isomorphisms
$\varphi_{ii'}:\mathrm{pr}_1^*\mathcal{M}_i\to\mathrm{pr}_2^*\mathcal{M}_{i'}$
on $S_i\times_SS_{i'}$ satisfying the cocycle condition on the triple
products) is an equivalence of categories: every descent datum is
effective.
2. The equivalence preserves and reflects flatness, finite presentation
and finite local freeness (of a given rank $r$): a quasi-coherent
$\mathcal{M}$ has one of these properties if and only if every
$f_i^*\mathcal{M}$ has it.
3. In particular (*descent of invertible modules*, [def-sc-invertible-module]):
invertible $\mathcal{O}_{S_i}$-modules with gluing isomorphisms
satisfying the cocycle condition glue to an invertible
$\mathcal{O}_S$-module $\mathcal{L}$ with $f_i^*\mathcal{L}\cong\mathcal{L}_i$
compatibly with the gluing data; and if an invertible
$\mathcal{O}_S$-module $\mathcal{L}$ admits trivializations
$f_i^*\mathcal{L}\cong\mathcal{O}_{S_i}$ whose two pullbacks to every
$S_i\times_SS_{i'}$ agree (i.e. compatible with the canonical gluing
isomorphisms), then $\mathcal{L}\cong\mathcal{O}_S$. (Without the
compatibility this fails already for Zariski coverings.)

Applied to the fpqc covering $\{X_{T_i}\to X_T\}$ obtained by base change
from an fpqc covering $\{T_i\to T\}$ and a morphism $X\to T$, this is
the form in which the statement is used: cartesian families
$\mathcal{L}_i$ on $X_{T_i}$ satisfying the cocycle condition glue to an
invertible $\mathcal{L}$ on $X_T$ with $\mathcal{L}|_{X_{T_i}}\cong\mathcal{L}_i$.

## Proof

*Step 1: the affine case for modules.* Let $A\to B$ be a faithfully
flat ring map, and let

$$
\Delta:B\longrightarrow B\otimes_AB,\quad \Delta(b)=b\otimes1
$$

be the canonical inclusion; write $B^{\otimes r}$ for the $r$-fold
tensor product. A *descent datum* for the covering
$\{\operatorname{Spec}(B)\to\operatorname{Spec}(A)\}$ on a $B$-module $N$ is an isomorphism

$$
\psi:N\otimes_AB\longrightarrow B\otimes_AN
$$

of $B\otimes_AB$-modules satisfying the
*cocycle condition*: the two isomorphisms

$$
N\otimes_AB\otimes_AB\longrightarrow B\otimes_AB\otimes_AN
$$

obtained by applying $\psi$ to the first two, resp. to the last two,
tensor factors, agree. *Claim: the functor from $A$-modules to
$B$-modules with descent datum (an $A$-module $M$ goes to
$M\otimes_AB$ with the canonical swap isomorphism) is an equivalence.*

The classical proof (EGA 0$_{IV}$, (2.5.7); Bourbaki, Alg. comm. V,
§1, no. 9; this is the argument of Stacks, Descent,
Proposition 35.3.9, Tag [023N](https://stacks.math.columbia.edu/tag/023N), which states that for a faithfully flat
$R\to A$ the functor $M\mapsto(A\otimes_RM,\mathrm{can})$ from
$R$-modules to modules with descent datum is an equivalence),
which we reproduce: given $(N,\psi)$, put

$$
N_0:=\ker\bigl(N\longrightarrow B\otimes_AN\bigr),
\qquad
n\longmapsto\psi(n\otimes1)-1\otimes n .
$$

The cocycle condition says precisely that the (twisted) Amitsur-type
complex

$$
0\to N_0\to N\to B\otimes_AN\to B\otimes_AB\otimes_AN\to\cdots
$$

(the differentials are the alternating sums of the cyclic permutations
of the tensor factors, with the first map $N\to B\otimes_AN$ the
difference above; in degree $r$, $\sum_{j=0}^{r+1}(-1)^j$ of the
$r$-fold multiplications with $\psi$ applied to the appropriate
factors) is a complex, and the maps

$$
s(b_1\otimes\cdots\otimes b_p\otimes n):=b_1\otimes\cdots\otimes
b_{p-1}\otimes\psi^{-1}(b_p\otimes n)
$$

satisfy $ds+sd=\mathrm{id}$ (the two double sums cancel pairwise;
only the top and bottom terms – which are $\mathrm{id}$ and
$N_0$-inclusion-composed terms – remain; the cocycle condition is
what makes the $\psi$-twisted pieces cancel). Hence the complex is
split exact; in particular the composite

$$
N_0\otimes_AB\longrightarrow N\otimes_AB\cong B\otimes_AN
$$

has image the kernel of $B\otimes_AN\to B\otimes_AB\otimes_AN$, which
by the exactness is $N_0\otimes_AB$; the exactness in degree zero
says this kernel is mapped isomorphically onto its image, and the
cocycle argument with the contracting homotopy identifies this image
with all of $N$: $N_0\otimes_AB\cong N$, compatibly with the descent
data. The faithfulness (an $A$-map vanishing after $\otimes_AB$
vanishes) and the fullness (a map of descent data is determined by –
and arises from – the induced map on the kernels, by the same
exactness) are then immediate: a morphism $N\to N'$ compatible with
the data maps the kernel $N_0$ into $N_0'$; conversely a map
$N_0\to N_0'$ yields a map of the $\otimes_AB$-modules which is
compatible with the kernels and the exactness shows it comes from a
unique such $A$-map. This proves the claim.

*Step 2: properties in the affine case.* Let $A\to B$ be faithfully
flat and $M$ an $A$-module; put $M_B:=B\otimes_AM$. If $M$ is flat,
finitely presented, or finite locally free of rank $r$, then so is
$M_B$ (base change). Conversely:

- *Flatness.* Let $N'\to N$ be an injective map of $A$-modules. As $B$ is
  flat, $B\otimes_AN'\to B\otimes_AN$ is injective, and
  $B\otimes_A(M\otimes_AN')=M_B\otimes_B(B\otimes_AN')\to
  M_B\otimes_B(B\otimes_AN)=B\otimes_A(M\otimes_AN)$ is injective when
  $M_B$ is $B$-flat. By faithful flatness (a map of $A$-modules is
  injective as soon as it is so after $B\otimes_A-$),
  $M\otimes_AN'\to M\otimes_AN$ is injective: $M$ is flat.
- *Finite generation.* If $M_B$ is generated by finitely many elements,
  each is a finite sum $\sum b\otimes m$; let $M'\subseteq M$ be the
  submodule generated by the finitely many $m$'s occurring. Then
  $B\otimes_AM'\to M_B$ is surjective, i.e. $B\otimes_A(M/M')=0$, so
  $M/M'=0$ by faithful flatness: $M$ is finite.
- *Finite presentation.* If $M_B$ is finitely presented, then $M$ is
  finite by the previous item; choose a surjection $A^n\to M$ with
  kernel $K$. By flatness $0\to B\otimes_AK\to B^n\to M_B\to0$ is exact,
  and the kernel of a surjection from a finite free module onto a
  finitely presented module is finite (Schanuel's lemma); so
  $B\otimes_AK$ is finite, hence $K$ is finite by the previous item, and
  $M$ is finitely presented.
- *Finite local freeness of rank $r$.* A module is finite locally free
  if and only if it is finitely presented and flat (Stacks, Algebra,
  Lemma 10.78.2), so this follows from the two previous items. Its rank
  at $\mathfrak p\in\operatorname{Spec}(A)$ is the dimension of
  $M\otimes\kappa(\mathfrak p)$, and for $\mathfrak q\in\operatorname{Spec}(B)$ over
  $\mathfrak p$ (which exists as $\operatorname{Spec}(B)\to\operatorname{Spec}(A)$ is surjective)
  $M_B\otimes\kappa(\mathfrak q)=(M\otimes\kappa(\mathfrak p))
  \otimes_{\kappa(\mathfrak p)}\kappa(\mathfrak q)$ has the same dimension;
  so $M$ has constant rank $r$ when $M_B$ does.

In particular, as invertible modules are exactly the finite locally
free modules of rank $1$ ([def-sc-invertible-module]), an $A$-module
$M$ is invertible if and only if $M_B$ is; so the descended module
$N_0$ of Step 1 is invertible whenever $N$ is.

*Step 3: the general covering.* Now let $\{S_i\to S\}_{i\in I}$ be
an fpqc covering and $\xi=(\mathcal{M}_i,\varphi_{ii'})$ a descent
datum of quasi-coherent modules. The datum and the statement are local
on $S$ (the descent data restrict along morphisms $S'\to S$, i.e. along
the base changed covering; base changes of fpqc coverings are fpqc,
Topologies, Lemma 34.9.8, Tag
[022D](https://stacks.math.columbia.edu/tag/022D)), so it suffices
to treat $S$ affine; by definition of an fpqc covering
(Topologies, Definition 34.9.1, Tag
[022B](https://stacks.math.columbia.edu/tag/022B)) the affine
$S=\operatorname{Spec}(A)$ is covered by standard fpqc coverings of finite
subfamilies, and a finite standard fpqc covering
$\{V_k=\operatorname{Spec}(B_k)\to\operatorname{Spec}(A)\}_k$ is precisely a faithfully flat map
$A\to B:=\prod_kB_k$ (the product over the finitely many $k$:
$\operatorname{Spec}(\prod B_k)=\bigsqcup_k\operatorname{Spec}(B_k)$). The restriction of the
datum to the $V_k$ is a descent datum for the covering
$\{\operatorname{Spec}(B)\to\operatorname{Spec}(A)\}$ (the covering is the sum of the
$V_k$; a quasi-coherent module on the affine $\operatorname{Spec}(B)$ is a
$B$-module $N$, namely the product of the modules of global sections
on the pieces, and the isomorphisms are the product of the pieces; the
cocycle condition is the compatibility over the intersections, checked
on the original $S_i$'s by the refinement: the standard argument of
Stacks 35.5.2: the descent data pull back along refinements and agree
on common refinements), which is effective by Step 1. This yields a
quasi-coherent $\mathcal{O}_S$-module restricting to $\mathcal{M}_i$
with the given $\varphi_{ii'}$; the identification is constructed with
the same standard refinement-compatibility argument (faithfulness over
the common refinements). For a general $S$, glue the modules so
obtained over an affine open cover: on the overlaps the two descended
modules restrict to descents of the same datum, hence are canonically
isomorphic by the full faithfulness of Step 1 applied to the common
refinement, and these isomorphisms satisfy the cocycle condition by the
uniqueness in the full faithfulness. The full faithfulness of the
functor $\mathcal{M}\mapsto(f_i^*\mathcal{M},\mathrm{can})$ follows in the
same way from the affine case, since morphisms of quasi-coherent
modules glue Zariski locally. This proves (1).

For (2): flatness, finite presentation and finite local freeness of rank
$r$ of a quasi-coherent module are Zariski-local on $S$, and each
$f_i^*\mathcal{M}$ has the property if and only if its restrictions to
an affine open cover of $S_i$ have it. Hence, with the reduction above,
it suffices to treat $\mathcal{M}=\widetilde M$ on $S=\operatorname{Spec}(A)$ and a
finite standard covering, i.e. a faithfully flat $A\to B=\prod_kB_k$,
where $B\otimes_AM=\prod_k(B_k\otimes_AM)$ has the property if and only
if each factor has it; this is Step 2.

For (3): an invertible module is a finite locally free module of rank
$1$ ([def-sc-invertible-module]), so by (1) the datum descends to a
quasi-coherent $\mathcal{L}$, which is invertible by (2). For the last
assertion: the compatible trivializations form an isomorphism of descent
data between $(f_i^*\mathcal{L},\mathrm{can})$ and
$(\mathcal{O}_{S_i},\mathrm{id})=(f_i^*\mathcal{O}_S,\mathrm{can})$, which by
the full faithfulness in (1) comes from an isomorphism
$\mathcal{L}\cong\mathcal{O}_S$.
