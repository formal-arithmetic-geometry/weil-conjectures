+++
id = "cor-fd-origin-stationary-phase"
kind = "theorem"
title = "The origin fiber is the stationary-phase contribution"
order = 2781
tags = ["latex:corollary"]
uses = ["def-fd-nonexceptional", "def-fd-transform", "def-weil-ordinary-compact-cohomology", "def-wf-middle-extension", "lem-a1-unramified-nonexceptional", "lem-fd-stalk-at-origin", "lem-wf-boundary-stalk-invariants", "prop-a1-fourier-middle-extension"]
+++
Let $j:U_0\hookrightarrow\mathbf A^1_{k_0}$ and let $\mathcal M$ be
irreducible and lisse on $U_0$, unramified at infinity, with
Fourier-nonexceptional middle
extension. Then the Fourier transform of [def-fd-transform] takes the
middle-extension shape
$\operatorname{FT}_\psi(j_{!*}\mathcal M[1])=j'_{!*}\mathcal M'[1]$,
and the degree $-1$ part of the fiber at
the origin of the dual line is the $H_c^1$-term of the local Fourier
exact sequence at the origin:

$$
\mathcal H^{-1}\Bigl(\operatorname{FT}_\psi(j_{!*}\mathcal M[1])_{0'}\Bigr)
\cong H_c^1(\mathbf A^1_{k_0},j_*\mathcal M)\;\cong\;(j'_*\mathcal M')_{0'}\;=\;\bigl(\mathcal M'_{\bar\eta}\bigr)^{I_{0'}},
$$

the last identification being the invariants of the local inertia
$I_{0'}$ at the origin of the dual line (trivial if $0'\in U'_0$): the
stationary phase term is therefore the origin part of the transformed
middle extension. Moreover $H_c^2(\mathbf A^1_{k_0},j_*\mathcal M)=0$.
All these identifications are *Frobenius-equivariant*: the origin $0'$
is a $k_0$-rational point, and the geometric Frobenius of $k_0$ acting
on $H_c^1(\mathbf A^1_{k_0},j_*\mathcal M)$ corresponds to the local
Frobenius $F_{0'}$ on the stalk $(j'_*\mathcal M')_{0'}$ of the Weil
sheaf $j'_*\mathcal M'$, and to the action of a Frobenius lift on
$(\mathcal M'_{\bar\eta})^{I_{0'}}$.

## Proof

The shape: Fourier-nonexceptionality says in particular that
$\mathcal M$ is not geometrically constant, so, being unramified at
infinity, $\mathcal M$ is constituent-nonexceptional by
[lem-a1-unramified-nonexceptional], and
[prop-a1-fourier-middle-extension] gives an isomorphism of Weil
complexes
$\operatorname{FT}_\psi(j_{!*}\mathcal M[1])\cong j'_{!*}\mathcal M'[1]=j'_*\mathcal M'[1]$
with $\mathcal M'$ nonzero, irreducible and lisse.

The first identification is [lem-fd-stalk-at-origin]: the fiber of
the transform at the origin is $R\Gamma_c(\mathbf A^1,j_*\mathcal M[1])[1]$,
whose degree $-1$ part is $H_c^1(\mathbf A^1_{k_0},j_*\mathcal M)$,
while its degree $0$ part is
$H_c^2(\mathbf A^1_{k_0},j_*\mathcal M)$. This identification is
Frobenius-equivariant. Indeed, the Weil structure of
$\operatorname{FT}_\psi(K_0)$ is the one transported from those of
$K_0$ and of the kernel of [def-fd-transform] through $p_1^*$,
$\otimes$ and $p_{2,!}$, and the isomorphism of
[lem-fd-stalk-at-origin] at the rational point $0'$ is composed of
the base change isomorphism for $p_{2,!}$ along
$0'\hookrightarrow V^\vee$ and the trivialisation of the kernel on
the fibre $\mathbf A^1\times\{0'\}$ (the kernel of the zero function
$x\cdot0$ is the constant Weil sheaf). Both are natural isomorphisms
defined over $k_0$, so they commute with the Weil descent data, and the
stalk Frobenius $F_{0'}$ of the transform corresponds to the geometric
Frobenius on $R\Gamma_c(\mathbf A^1_{k_0},j_*\mathcal M)$.

For the second identification, the transformed object has the shape
$j'_*\mathcal M'[1]$ of [def-wf-middle-extension], a single
sheaf placed in degree $-1$; its fiber at the point $0'$ of the dual
line is therefore concentrated in degree $-1$, where it is the stalk
$(j'_*\mathcal M')_{0'}$, and the isomorphism of Weil complexes above
induces a Frobenius-equivariant isomorphism of the fibres at the
rational point $0'$. Comparing the two descriptions of the same fiber
gives $H_c^1(\mathbf A^1_{k_0},j_*\mathcal M)\cong(j'_*\mathcal M')_{0'}$
equivariantly, and $H_c^2(\mathbf A^1_{k_0},j_*\mathcal M)=0$
because the degree $0$ part vanishes. If $0'\notin U'_0$, the
boundary-stalk description of
[lem-wf-boundary-stalk-invariants] gives
$(j'_*\mathcal M')_{0'}=\bigl(\mathcal M'_{\bar\eta}\bigr)^{I_{0'}}$,
Frobenius-equivariantly; if $0'\in U'_0$, the inertia $I_{0'}$ acts
trivially on the lisse sheaf $\mathcal M'$ and the stalk is
$\mathcal M'_{\bar\eta}=(\mathcal M'_{\bar\eta})^{I_{0'}}$. All
cohomology is in the compact-support convention of
[def-weil-ordinary-compact-cohomology].
