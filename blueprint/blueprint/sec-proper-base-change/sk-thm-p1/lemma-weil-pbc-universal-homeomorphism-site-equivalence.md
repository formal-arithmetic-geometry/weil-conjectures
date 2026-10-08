+++
id = "lemma-weil-pbc-universal-homeomorphism-site-equivalence"
kind = "lemma"
title = "Base change equivalence for universal homeomorphisms"
order = 1110
lean = ["AlgebraicGeometry.Scheme.Hom.etaleEquivalence", "AlgebraicGeometry.Scheme.Hom.isEquivalence_etale"]
uses = ["lem-weil-pbc-closed-immersion-from-composite", "lemma-nagata-affine-finite-type-is-quasi-affine"]
+++
Let $u:X_0\to X$ be a universal homeomorphism. Base change gives an
equivalence between etale $X$-schemes and etale $X_0$-schemes.

## Proof

This is Tag `04DZ`; the formalization follows its second proof.

*Full faithfulness* (Tag `04DY`). Faithfulness only uses that
$u$ is surjective and that etale morphisms are unramified: two
$X$-morphisms $T\to V$ into an etale $X$-scheme that agree after composing
with the surjection $T\times_XX_0\to T$ factor jointly through the diagonal
of $V$, an open immersion. For fullness, an $X_0$-morphism
$a:T\times_XX_0\to V\times_XX_0$ is descended through its graph: the graph
is a section of the etale projection $(T\times_XV)\times_XX_0\to T\times_XX_0$,
hence an open immersion, and since $(T\times_XV)\times_XX_0\to T\times_XV$ is
a homeomorphism the image of the graph is the base change of an open
subscheme $O\subset T\times_XV$. The projection $O\to T$ is etale and becomes
an isomorphism after base change along $T\times_XX_0\to T$; surjectivity and
universal injectivity descend along surjections, so $O\to T$ is an etale
universally injective surjection, hence an isomorphism, and $T\cong O\to V$
is the required morphism.

*Essential surjectivity.* Being in the essential image is local on the
source: the descended pieces of a cover of $V_0$ by descendable opens form a
locally directed diagram of open immersions of etale $X$-schemes, by full
faithfulness, and its colimit is the descent of $V_0$. So it suffices to
treat an affine etale $V_0\to X_0$ over affine $X$, and after shrinking one
may assume that $V_0$ is standard etale, so that its fibre degrees are
bounded by some $n$. One then proves by induction on $n$ that every affine
etale $V_0$ over $X_0$ with fibre degrees at most $n$, for $X$ quasi-affine, is
the base change of a quasi-affine etale $X$-scheme. Shrinking $X$ to the
open image of $V_0$ one may assume $V_0\to X_0$ surjective. Property (C) of
Tag `04DW` produces an affine etale $W\to X$ and a surjective
$X_0$-morphism $W\times_XX_0\to V_0$: after passing to an etale neighbourhood
of $X$ realizing the separable closure of the residue field of a point, and
after a further etale neighbourhood splitting off the corresponding point of
the finite algebra (Tag `00UJ`), the relevant piece of $V_0$ becomes
finite etale of rank one, i.e. isomorphic to the base. Its section splits
$V_0\times_{X_0}(W\times_XX_0)$ as $W\times_XX_0$ together with a complement
of fibre degrees at most $n-1$, which descends to $W$ by induction. The
resulting quasi-affine etale $W$-scheme descends along the etale cover
$W\to X$: its ring of global sections carries the canonical descent datum
(defined by full faithfulness along the universal homeomorphism
$W\times_XX_0\to W$, using flat base change of global sections), which is
effective by faithfully flat descent of algebras, and the quasi-affine scheme
descends as an open subscheme of the spectrum of the descended algebra.
