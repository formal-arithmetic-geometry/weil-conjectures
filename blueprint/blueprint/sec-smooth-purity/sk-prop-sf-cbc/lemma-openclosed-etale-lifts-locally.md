+++
id = "lemma-openclosed-etale-lifts-locally"
kind = "lemma"
title = "Étale morphisms lift locally along a closed immersion"
order = 1520
lean = ["AlgebraicGeometry.Etale.exists_isPullback_of_isClosedImmersion", "AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion"]
uses = ["lemma-openclosed-standard-etale-lift"]
+++
Let $i\colon Z\to X$ be a closed immersion, let $q\colon W\to Z$ be étale
and let $w\in W$. Then there are an open subscheme $W_0\subseteq W$
containing $w$, a scheme $V$ étale over $X$, and an isomorphism of
$Z$-schemes

$$
W_0\cong V\times_XZ.
$$

In the pointed form used below, if $\bar w\colon\Spec\Omega\to W$ is a point
of $W$ with values in a field, then there are a scheme $V$ étale over $X$
and a morphism $V\times_XZ\to W$ of $Z$-schemes through which $\bar w$
factors: apply the above at the image point of $\bar w$ and compose the
isomorphism with the open immersion $W_0\subseteq W$.

## Proof

The assertion is local at $w$, so we may shrink $X$, $Z$ and $W$ around
$i(q(w))$ and $w$. Choose an affine open $\Spec R\subseteq X$ containing
$i(q(w))$; then $Z$ meets it in $\Spec R/I$, and we may choose an affine open
$\Spec B\subseteq W$ containing $w$ and lying over $\Spec R/I$, so that $B$
is an étale $R/I$-algebra.

By the local structure of étale algebras, after replacing $\Spec B$ by a
basic open subscheme containing $w$ we may assume that $B$ is a standard
étale $R/I$-algebra. By
[lemma-openclosed-standard-etale-lift] there is a standard étale
$R$-algebra $A$ with $(R/I)\otimes_RA\cong B$. Put
$V:=\Spec A$, mapping to $X$ through $\Spec A\to\Spec R\subseteq X$; this is
étale, being an étale morphism followed by an open immersion. Finally

$$
V\times_XZ=\Spec A\times_{\Spec R}\Spec R/I=\Spec\bigl((R/I)\otimes_RA\bigr)
\cong\Spec B=:W_0,
$$

which is an open subscheme of $W$ containing $w$.
