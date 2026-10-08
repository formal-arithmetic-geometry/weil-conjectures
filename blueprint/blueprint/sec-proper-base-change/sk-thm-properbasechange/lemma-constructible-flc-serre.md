+++
id = "lemma-constructible-flc-serre"
kind = "lemma"
title = "Kernels, cokernels and extensions of finite locally constant sheaves"
order = 1298
lean = ["AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.cokernel", "AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.kernel"]
uses = ["def-constructible-constant", "def-constructible-finite", "def-constructible-finite-locally-constant", "def-constructible-locally-constant", "def-kun-separably-closed", "lemma-constructible-flc-biproduct", "lemma-constructible-hom-constant-locally", "lemma-constructible-iso-invariance", "lemma-constructible-pullback-constant", "lemma-constructible-pullback-finite", "lemma-constructible-pullback-locally-constant", "lemma-constructible-torsor-trivialises"]
+++
Let $\mathcal A=\mathrm{Mod}_\Lambda$ with $\Lambda$ a finite ring. The
kernel and the cokernel of a morphism between finite locally constant
sheaves, and the middle term of a short exact sequence whose outer terms
are finite locally constant, are finite locally constant. (The kernel and
cokernel statements are formalised, for any ring $\Lambda$; the extension
statement is not.)

## Proof

Restricting to an étale cover trivialising both sheaves
([lemma-constructible-flc-biproduct]), we may assume the morphism is
$\varphi\colon M_X\to N_X$ with $M$, $N$ finite (the stalks of the constant
sheaf $M_X$ are $M$). By [lemma-constructible-hom-constant-locally]
kernel and cokernel are locally constant with finite stalks.

For an extension $0\to M_X\to\mathcal E\to N_X\to0$, again on a
trivialising cover, consider the sheaf $P$ of sections of
$\mathcal E\to N_X$: over $U\to X$ its sections are the morphisms
$s\colon N_U\to\mathcal E|_U$ with $\pi\circ s=\mathrm{id}$. It is a torsor
under the sheaf $\mathcal{H}om(N_X,M_X)=\Hom_\Lambda(N,M)_X$ (two sections
differ by a morphism $N_U\to M_U$, and locally sections exist since the
sequence is locally split in the étale topology: the stalks are finite
modules and a surjection of sheaves is locally surjective on sections).
The group $\Hom_\Lambda(N,M)$ is finite, so by
[lemma-constructible-torsor-trivialises] $P$ has a section over an
étale cover $(U_i\to X)$, and over $U_i$ the sequence splits:
$\mathcal E|_{U_i}\cong M_{U_i}\oplus N_{U_i}=(M\oplus N)_{U_i}$. Hence
$\mathcal E$ is locally constant, with finite stalks $M\oplus N$.
