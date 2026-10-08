+++
id = "lem-chow-scheme-theoretic-closure"
kind = "lemma"
title = "Scheme-theoretic closure of a dense open"
order = 1052
lean = ["AlgebraicGeometry.Scheme.Opens.iInf_preimage_imageι", "AlgebraicGeometry.Scheme.Opens.iSup_preimage_imageι_eq_top", "AlgebraicGeometry.Scheme.Opens.isAffineOpen_preimage_imageι", "AlgebraicGeometry.Scheme.Opens.isIso_morphismRestrict_imageι", "AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDominant_preimage_imageι", "AlgebraicGeometry.Scheme.Opens.surjective_imageι_ι"]
uses = ["def-nagata-dense-compactification", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-weil-pbc-scheme-conventions", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-scheme-image-ideal-qc"]
+++
Let $X$ be a scheme and let $U\subseteq X$ be a dense open subscheme such that
the inclusion $u\colon U\to X$ is quasi-compact and quasi-separated. Let
$X^{*}\subseteq X$ be the scheme-theoretic image of $u$. Then:

1. $X^{*}\to X$ is a surjective closed immersion which is an isomorphism
over $U$;
1. $U\subseteq X^{*}$ is a scheme-theoretically dense open subscheme;
1. if $X=U_1\cup\dots\cup U_m$ is a finite affine open covering, then the
opens $U_i^{*}:=X^{*}\cap U_i$ are affine, cover $X^{*}$, and satisfy
$U_1^{*}\cap\dots\cap U_m^{*}=U$.

## Proof

By construction $X^{*}\to X$ is a closed immersion, and $U$ factors through it.
Its image is a closed subset containing the dense subset $U$, hence is all of
$X$, so $X^{*}\to X$ is surjective. The quasi-coherent ideal sheaf of $X^{*}$
is $\ker(\mathcal O_X\to u_*\mathcal O_U)$, whose restriction to $U$ is
$\ker(\mathcal O_U\to\mathcal O_U)=0$; hence $X^{*}\cap U=U$ and $X^{*}\to X$
is an isomorphism over $U$. This proves (1). Since formation of the
scheme-theoretic image commutes with restriction to opens, the
scheme-theoretic image of $U\to X^{*}$ is $X^{*}$, which is (2). For (3), each
$U_i^{*}$ is a closed subscheme of the affine scheme $U_i$, hence affine, and
$U_1^{*}\cap\dots\cap U_m^{*}=X^{*}\cap U=U$.

In Lean, $X^{*}$ is `U.ι.image`, the scheme-theoretic image of the
inclusion `U.ι`, and $U_i^{*}$ is the open
`U.ι.imageι ⁻¹ᵁ Uᵢ` of $X^{*}$; the copy of $U$ in $X^{*}$ is
`U.ι.imageι ⁻¹ᵁ U`. Surjectivity comes from the identification of the
underlying set of a scheme-theoretic image with the closure of the set-theoretic image
(`AlgebraicGeometry.Scheme.Hom.range_imageι`), and being an isomorphism
over $U$ is expressed as `IsIso (U.ι.imageι ∣_ U)`. Only
quasi-compactness of $u$ is used: quasi-separatedness is automatic for an open immersion, and
Mathlib's kernel ideal sheaf theory needs only quasi-compactness.

## Detailed form

Let $X$ be quasi-compact and let $U\subseteq X$ be a dense open subscheme. Let
$X^{*}\subseteq X$ be the scheme-theoretic closure of $U\to X$ in the sense of
[def-nagata-scheme-theoretic-image]. Then $X^{*}\to X$ is a
surjective closed immersion, an isomorphism over $U$, and $U$ is
scheme-theoretically dense in $X^{*}$. If moreover $X=U_1\cup\dots\cup U_m$ is
a finite affine open cover and $U_i^{*}:=X^{*}\cap U_i$, then each $U_i^{*}$
is affine and $U_1^{*}\cap\dots\cap U_m^{*}=U$.

## Proof

By [def-nagata-scheme-theoretic-image], $X^{*}\to X$ is a closed
immersion. Its image is a closed subset containing $U$, whose underlying set
is dense in $X$; hence the image is all of $X$, i.e. $X^{*}\to X$ is
surjective. The ideal sheaf of $X^{*}$ in $X$ is $\ker(\mathcal O_X\to
u_*\mathcal O_U)$ where $u:U\to X$; its restriction to the open $U$ is
$\ker(\mathcal O_U\to\mathcal O_U)=0$, so $X^{*}\cap U=U$: the closed
immersion is an isomorphism over $U$. By definition the scheme-theoretic image
of $U\to X^{*}$ is $X^{*}$, i.e. $U$ is scheme-theoretically dense in $X^{*}$.
Each $U_i^{*}$ is a closed subscheme of the affine scheme $U_i$, and a closed
subscheme of an affine scheme is affine, so $U_i^{*}$ is affine; and

$$
 U_1^{*}\cap\dots\cap U_m^{*}=X^{*}\cap U_1\cap\dots\cap U_m
 =X^{*}\cap U=U,
$$

the last equality because $U\subseteq X^{*}$.
