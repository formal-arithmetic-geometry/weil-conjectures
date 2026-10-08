+++
id = "lem-pc-projective-noetherian-rf-perfect"
kind = "lemma"
title = "Perfect direct image for a projective Noetherian family"
order = 673
uses = ["def-pc-derived-direct-image", "def-pc-morphism-conventions", "def-pc-perfect-complex", "def-pc-projective-morphism", "lem-pc-cech-resolution", "lem-pc-noetherian-flat-complex-perfect", "lem-pc-projective-coherent-finiteness", "pqf-def-coherent"]
+++
Let $S$ be locally Noetherian, let $f:X\to S$ be
projective, and let
$\mathcal G$ be a coherent
$\mathcal O_X$-module flat over $S$.
Then the derived direct image
$Rf_*\mathcal G$ is perfect.

## Proof

The assertion is local on $S$, so take $S=\operatorname{Spec}(A)$
with $A$ Noetherian. A finite affine cover of the quasi-compact
separated scheme $X$ has affine finite intersections. By
[lem-pc-cech-resolution], its bounded Cech complex represents
$Rf_*\mathcal G$ over this affine base.

Each term of this complex is a finite direct sum of flat
$A$-modules. To check this explicitly, write an affine
intersection as $U=\operatorname{Spec}(B)$ and
$\mathcal G|_U=\widetilde M$. For any injection $N'\to N$ of
$A$-modules, let $K$ be the kernel of
$M\otimes_A N'\to M\otimes_A N$. At a prime $\mathfrak q$ of
$B$, with inverse image $\mathfrak p$ in $A$, the module
$M_{\mathfrak q}$ is flat over $A_{\mathfrak p}$ by relative
flatness. Localizing the displayed map at $\mathfrak q$
therefore gives an injection, so $K_{\mathfrak q}=0$ for every
$\mathfrak q$. Consequently $K=0$, proving that $M$ is flat
over $A$.

The cohomology modules of this bounded flat complex are finite
over $A$ by [lem-pc-projective-coherent-finiteness].
Applying [lem-pc-noetherian-flat-complex-perfect] gives a
bounded finite projective representative on $\operatorname{Spec}(A)$.
This proves perfectness locally on $S$.
