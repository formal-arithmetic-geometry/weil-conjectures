+++
id = "lem-wf-same-lie-closed-subgroup"
kind = "lemma"
title = "Smoothness, dimension and Lie algebras of matrix groups"
order = 2491
uses = ["def-wf-algebraic-components", "def-wf-lie-algebra-derivation", "lem-ag-equal-dimension-subgroup", "lem-sc-translation-automorphism", "lem-wf-smooth-components-disjoint"]
+++
Let $K$ be a closed matrix group over $\overline{\mathbf Q}_\ell$.

1. If $K$ is connected, then $K$ is irreducible. Moreover, if $K$ is
   connected, $L\subseteq K$ is a closed algebraic subgroup and
   $\operatorname{Lie}(L)=\operatorname{Lie}(K)$, then $L=K$.
2. $K$ is smooth, and
   $\dim\operatorname{Lie}(K)=\dim K$.
3. The identity component $K^\circ$ of [def-wf-algebraic-components]
   is open (and closed) in $K$, and
   $\operatorname{Lie}(K^\circ)=\operatorname{Lie}(K)$.
4. The differential at $(1,1)$ of the multiplication
   $K\times K\to K$ is the map
   $\operatorname{Lie}(K)\oplus\operatorname{Lie}(K)\to\operatorname{Lie}(K)$,
   $(X,Y)\mapsto X+Y$.

## Proof

*Smoothness.* A reduced finite-type variety over the characteristic-zero field
$\overline{\mathbf Q}_\ell$ has a nonempty smooth locus by the
elementary Jacobian criterion. In an algebraic group, translation
carries a smooth point to the identity and then the identity to every
other point. Thus every closed point of the reduced closed matrix groups $K$ and
$L$ is a smooth point; since the nonsmooth locus is closed
([Stacks 01V5](https://stacks.math.columbia.edu/tag/01V5)) and a
nonempty closed subset of a finite-type $\overline{\mathbf Q}_\ell$-scheme
contains a closed point, $K$ and $L$ are smooth. In particular every local ring of $K$ is regular, hence
is an integral domain. If two distinct irreducible components of
$K$ met at a point $x$, the local ring $\mathcal O_{K,x}$ would
have at least two minimal prime ideals, one from each component, and
could not be a domain. Therefore the finitely many irreducible
components of $K$ are pairwise disjoint
([lem-wf-smooth-components-disjoint]); each is consequently both
open and closed.

*Dimension.* Smoothness at the identity makes
$\mathcal O_{K,1}$ regular, so
$\dim_k\mathfrak m_1/\mathfrak m_1^2=\dim\mathcal O_{K,1}$, and the
left side is the dimension of the tangent space at the identity, which
is $\operatorname{Lie}(K)$ by [def-wf-lie-algebra-derivation].
Translations are automorphisms of the variety $K$
([lem-sc-translation-automorphism]), so the local
dimensions $\dim\mathcal O_{K,g}$ at all closed points $g$ agree, and
the dimension of $K$ is their maximum. Hence
$\dim\operatorname{Lie}(K)=\dim K$, and likewise
$\dim\operatorname{Lie}(L)=\dim L$. This proves (2).

*Identity component.* Let $K_1$ be the unique irreducible component
containing the identity.
The image of the irreducible variety $K_1\times K_1$ under
multiplication is irreducible and contains the identity, so its closure
lies in the unique component $K_1$. Hence $K_1K_1\subseteq K_1$.
Inversion sends $K_1$ to an irreducible component containing the
identity, hence to $K_1$. Thus $K_1$ is a subgroup. Translation by
$g\in K$ sends $K_1$ onto the irreducible component containing
$g$. Since $K_1$ is irreducible, it is connected; being open and
closed, it is the connected component of the identity, so
$K^\circ=K_1$ is open and closed in $K$. The local ring of the open
subscheme $K^\circ$ at the identity is $\mathcal O_{K,1}$, so its
tangent space at the identity is unchanged:
$\operatorname{Lie}(K^\circ)=\operatorname{Lie}(K)$. This proves (3).
If $K$ is connected in the sense of [def-wf-algebraic-components], the
nonempty open and closed subset $K_1$ must be all of $K$; thus $K$ is
irreducible.

*Equal Lie algebras.* Let $K$ be connected, hence irreducible, and
$L\subseteq K$ with $\operatorname{Lie}(L)=\operatorname{Lie}(K)$.
By (2), equality of Lie algebras gives $\dim L=\dim K$, so
[lem-ag-equal-dimension-subgroup], applied to the irreducible matrix
group $K$ and its closed subgroup $L$, gives $L=K$.
This proves (1).

*Multiplication.* The tangent space at the identity is the space of
$X$ with $1+\varepsilon X\in K(k[\varepsilon]/\varepsilon^2)$ lying
over the identity. Points of a product with values in
$k[\varepsilon]/\varepsilon^2$ are pairs of such points, so the tangent
space of $K\times K$ at $(1,1)$ is
$\operatorname{Lie}(K)\oplus\operatorname{Lie}(K)$. Multiplication
sends the pair $(1+\varepsilon X,1+\varepsilon Y)$ to

$$
(1+\varepsilon X)(1+\varepsilon Y)=1+\varepsilon(X+Y),
$$

since $\varepsilon^2=0$. Hence its differential at $(1,1)$ is
$(X,Y)\mapsto X+Y$, which proves (4).
