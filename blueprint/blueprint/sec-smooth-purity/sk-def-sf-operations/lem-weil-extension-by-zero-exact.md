+++
id = "lem-weil-extension-by-zero-exact"
kind = "lemma"
title = "Exactness of extension by zero"
order = 1492
uses = ["def-weil-extension-by-zero", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Let $A$ be a finite commutative ring. Let $j:U\hookrightarrow\overline X$ be
an open immersion [def-weil-scheme-morphism-properties] of schemes and use
the small pro-etale sites [def-weil-pbc-proetale-site] with the
constant coefficient sheaf $A$, including the finite-torsion coefficient
rings [def-weil-finite-torsion-constructibility] $A_{E,n}$. Then the
extension-by-zero functor [def-weil-extension-by-zero] $j_!$ is exact.

## Proof

In the presheaf construction of [def-weil-extension-by-zero], kernels are
computed objectwise: on an object over $U$ this is the kernel of the
corresponding section map, and on other objects it is zero. Sheafification of
module presheaves is exact, so $j_!$ preserves kernels on the module sheaves
of [def-weil-finite-torsion-constructibility]. For an epimorphism $M\to N$, a
section of $P_N(V)$ is either zero or a section of $N(V)$ with $V$ over $U$.
In the latter case it lifts on a covering of $V$ in $U_{\mathrm{proet}}$.
This is also a covering in the ambient site of
[def-weil-pbc-proetale-site]. Thus $P_M\to P_N$ is locally
surjective; after sheafification it is an epimorphism. Preservation of
kernels and epimorphisms proves exactness.
