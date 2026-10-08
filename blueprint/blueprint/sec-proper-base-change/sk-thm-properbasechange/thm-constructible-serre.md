+++
id = "thm-constructible-serre"
kind = "theorem"
title = "Constructible sheaves form a weak Serre subcategory"
order = 1299
lean = ["AlgebraicGeometry.Scheme.IsConstructibleSheaf.cokernel", "AlgebraicGeometry.Scheme.IsConstructibleSheaf.kernel"]
uses = ["def-constructible-constructible", "def-constructible-finite-locally-constant", "def-constructible-refines", "def-constructible-stratification", "def-weil-pbc-constructible-complexes", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "lemma-constructible-common-refinement", "lemma-constructible-flc-biproduct", "lemma-constructible-flc-serre", "lemma-constructible-iso-invariance", "lemma-constructible-of-refines", "lemma-weil-pbc-geometric-stalk-conservative", "prop-constructible-pullback", "prop-weil-pbc-geometric-stalks-exact"]
+++
Let $\mathcal A=\mathrm{Mod}_\Lambda$ with $\Lambda$ a finite ring. The
kernel and the cokernel of a morphism between constructible sheaves on
$\et X$, finite direct sums of constructible sheaves, and the middle term of
a short exact sequence whose outer terms are constructible, are
constructible. Consequently the constructible sheaves form a weak Serre
subcategory of $\shv{\et X}$. (The kernel and cokernel statements are
formalised, for any ring $\Lambda$, as are the instances
`IsClosedUnderKernels` and `IsClosedUnderCokernels` of
`Etale.constructibleSheaf`; the extension statement is not.)

## Proof

Let $\varphi\colon\mathcal F\to\mathcal F'$ be a morphism of constructible
sheaves. By [lemma-constructible-common-refinement] and
[lemma-constructible-of-refines] there is one stratification
$(\iota_k\colon Z_k\to X)_k$ such that all $\iota_k^*\mathcal F$ and
$\iota_k^*\mathcal F'$ are finite locally constant. Since $\iota_k^*$ is
exact, $\iota_k^*\ker\varphi=\ker(\iota_k^*\varphi)$ and
$\iota_k^*\operatorname{coker}\varphi=\operatorname{coker}(\iota_k^*\varphi)$
are finite locally constant by [lemma-constructible-flc-serre], so
$\ker\varphi$ and $\operatorname{coker}\varphi$ are constructible with
respect to the same stratification. The same argument, using exactness of
$\iota_k^*$ and the extension part of [lemma-constructible-flc-serre],
handles extensions, and [lemma-constructible-flc-biproduct] handles
finite direct sums. A full subcategory of an abelian category closed under
kernels, cokernels and extensions is a weak Serre subcategory.

## Detailed form

For a scheme $T$ and a finite ring $\Lambda$, the constructible
$\Lambda$-module sheaves on $T_{\Et}$ form a weak Serre subcategory of
$\Mod(T_{\Et},\Lambda)$: kernels, cokernels, and extensions of constructible
sheaves are constructible.

*Source:* Stacks Project, Etale Cohomology, Lemma 59.71.6, [Tag
03RZ](https://stacks.math.columbia.edu/tag/03RZ). The pro-etale counterpart
of the weak-Serre assertion, stated there for a Noetherian coefficient ring,
is Stacks Project, Section 61.27, [Tag
09AI](https://stacks.math.columbia.edu/tag/09AI); the form used here is the
etale statement just cited, for a finite ring $\Lambda$.

## Proof

Work on an affine open of $T$, and refine the finitely many partitions of
the given constructible sheaves to one common partition, as in the
definition of a constructible complex. Inverse image to a part is exact, by
the stalkwise exactness of geometric stalks. It suffices to prove the
assertions for finite locally constant sheaves on each part, locally for the
topology of the small etale site.

For a map between two such sheaves, trivialize both near a geometric point.
The images of the finitely many elements of the first constant module are
sections of the second. After an etale refinement each is a specified
constant section. The map is then induced by a map of finite modules, whose
kernel and cokernel give the constant kernel and cokernel sheaves. These
descriptions prove the first two assertions.

Consider an extension $0\to F'\to F\to F''\to0$ with $F'$ and $F''$ finite
locally constant. Fix a geometric point $\bar t$ and trivialize both outer
sheaves on an etale neighbourhood. By the exactness of geometric stalks, the
middle stalk $B=F_{\bar t}$ is an extension of two finite modules and is
finite. Represent each of its finitely many elements by a section of $F$ on
a common pointed etale neighbourhood. All addition, zero and
scalar-multiplication relations of $B$ hold after a further common
refinement: there are only finitely many relations since $B$ and $\Lambda$
are finite, and equality in a stalk means equality on such a neighbourhood.
Also impose the finitely many equalities identifying the chosen sections of
the submodule with the constant sections of $F'$, and their images with the
constant sections of $F''$. We obtain a map from the constant exact sequence
of stalk modules to the given exact sequence, which is the identity on the
outer terms. The kernel--cokernel argument for a map of short exact
sequences makes the middle map an isomorphism; equivalently, apply the same
argument on every stalk and conservativity of geometric stalks. Thus $F$ is
finite locally constant near every point. Applying this on the common
partition proves extension closure and completes the proof.

## Detailed form

Let $X$ be a scheme and $\Lambda$ a finite ring. The category of
constructible $\Lambda$-module sheaves on $X_{\Et}$ is closed under
kernels, cokernels, and extensions inside $\Mod(X_{\Et},\Lambda)$.

## Proof

This is [thm-constructible-serre] of the proper-base-change chapter,
restated in the notation of this chapter.
