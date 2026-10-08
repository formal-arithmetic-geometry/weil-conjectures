+++
id = "d-ab-field"
kind = "definition"
title = "Finite fields, Frobenius and abelian varieties"
lean = ["FiniteField.geometricFrobeniusAlgEquivOfAlgebraic", "AlgebraicGeometry.IsAbelianScheme"]
order = 466
+++
Fix distinct primes $p,\ell$, an integer $a\ge1$, a field $k_0$ with
$q=p^a$ elements, and an algebraic closure $\bar k$.
Arithmetic Frobenius is $\sigma:x\mapsto x^q$ on $\bar k$; geometric
Frobenius is $F=\sigma^{-1}$. They act on geometric points by coordinates.
The group of automorphisms fixing $k_0$ is $\Gal(\bar k/k_0)$.
A scheme is a locally ringed space locally isomorphic to
$\operatorname{Spec}R$ for a commutative ring $R$, with the structure
sheaf given by localizations of $R$; a scheme over $k_0$ has a morphism
to $\operatorname{Spec}k_0$. Finite type means a finite affine cover
whose coordinate rings are finitely generated $k_0$-algebras.
A morphism is separated if its diagonal is a closed immersion, and is
proper if it is separated, of finite type, and universally closed
(every base change maps closed subsets to closed subsets).
For a finite-type scheme over the perfect field $k_0$, smoothness means
that after extension to $\bar k$ every local ring $R$ is regular:
$\dim_{R/\mathfrak m}(\mathfrak m/\mathfrak m^2)=\dim R$.
Here $\mathfrak m$ is its maximal ideal and $\dim R$ is the supremum
of lengths of strict chains of prime ideals.
A group scheme over $k_0$ is a scheme with multiplication, identity and
inverse morphisms satisfying the group identities; these induce a group
on its points over each $k_0$-algebra. An abelian variety $A_0/k_0$ is a
proper, smooth, geometrically connected, commutative group scheme of
finite type. Geometric connectedness means connectedness after extension
to $\bar k$. Write $A=A_0(\bar k)$ additively.
def:ab-scheme;def:ab-points;def:ab-proper-smooth;def:ab-finite-field;def:ab-group-scheme;def:ab-abelian-variety;def:ab-finite-type
