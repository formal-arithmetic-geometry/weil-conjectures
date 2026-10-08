+++
id = "the-general-case-via-zariski-s-main-theorem--remark-2"
kind = "remark"
title = "Formalization route: Tag 081S from Theorem 2.4 and Zariski's Main Theorem"
order = 227
uses = ["cor-nagata-blowup-product-common-refinement", "lemma-nagata-admissible-blowup-comp", "lemma-nagata-conrad-schematically-dense-blowup", "lemma-nagata-strict-transform-closure-characterization", "thm-nagata-conrad-elimination"]
+++
[lemma-nagata-elimination-indeterminacy] (Stacks Tag 081S) is
formalized along this section, not along a module-flattening argument. The bridge is the
following argument, which uses no further input; it is carried out as the
construction [def-nagata-elimination-indeterminacy] and the proof of
[lemma-nagata-elimination-indeterminacy] at the end of this section.

Let $X$ be qcqs, let $U\subseteq X$ be a quasi-compact open and let
$q\colon Z\to X$ be separated and of finite type with a chosen isomorphism
$q^{-1}(U)\cong U$ over $U$.

1. By [lemma-nagata-conrad-schematically-dense-blowup], replace $X$
by the $U$-admissible blow-up along a finite type ideal with zero scheme
exactly $X\setminus U$, and $Z$ by its strict transform. The new $q$ is
still separated and of finite type and is still an isomorphism over $U$,
and now $U$ is scheme-theoretically dense in $X$; in particular the
density hypothesis of [thm-nagata-conrad-elimination] holds. The
final centre is recombined with this one by
[lemma-nagata-admissible-blowup-comp].
1. Apply [thm-nagata-conrad-elimination] with $V=U$ and with $f$
the section $U\cong q^{-1}(U)\hookrightarrow Z$: it produces a
$U$-admissible blow-up $\operatorname{Bl}_{\mathcal I}(X)$ and a
quasi-domination $(W,\widetilde f)$ of it over $Z$ extending $f$.
1. Enlarge the centre from $\mathcal I$ to $\mathcal I\cdot\mathcal I_0$
with $V(\mathcal I_0)=X\setminus U$, and let
$X'=\operatorname{Bl}_{\mathcal I\mathcal I_0}(X)$. By
[cor-nagata-blowup-product-common-refinement] it dominates
$\operatorname{Bl}_{\mathcal I}(X)$, so $W$ pulls back to an open
$W'\subseteq X'$ containing $U$ and $\widetilde f$ pulls back to
$f'\colon W'\to Z$ with $\Gamma_{f'}$ closed in $X'\times_XZ$. Now
$X'\setminus V(\mathcal I\mathcal I_0)=U$, so $U$ is
scheme-theoretically dense in $X'$ and hence in $W'$.
1. The strict transform $Z'$ of $Z$ in $X'$ is, by
[lemma-nagata-strict-transform-closure-characterization], the
scheme-theoretic closure of the part of $X'\times_XZ$ lying over
$X'\setminus V(\mathcal I\mathcal I_0)=U$, that is, the
scheme-theoretic closure of $\Gamma_f$. It is therefore contained in
the closed subscheme $\Gamma_{f'}\cong W'$. So $Z'$ is a closed
subscheme of $W'$ containing $U$ as a scheme-theoretically dense open
subscheme, whence $Z'=W'$ and $Z'\to X'$ is an open immersion.

This is exactly the conclusion of
[lemma-nagata-elimination-indeterminacy]. The two external inputs are
Zariski's Main Theorem, used once in the proof of
[thm-nagata-conrad-elimination] and available in Mathlib as
`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`, and the
immersion of a quasi-affine scheme into relative affine space (Stacks Tag
04II), used in [lemma-nagata-conrad-quasi-affine-affine-base] and
already formalized as
`AlgebraicGeometry.exists_immersion_affineSpace_of_quasiAffine`.
