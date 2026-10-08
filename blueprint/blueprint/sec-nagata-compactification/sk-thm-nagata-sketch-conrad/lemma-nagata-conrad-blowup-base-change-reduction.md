+++
id = "lemma-nagata-conrad-blowup-base-change-reduction"
kind = "lemma"
title = "Reduction by base change along an admissible blow-up"
order = 218
lean = ["AlgebraicGeometry.exists_isAdmissible_extend_partialSection_of_blowup"]
uses = ["def-nagata-admissible-blowup", "def-nagata-conrad-quasi-domination", "def-nagata-global-blowup", "lemma-nagata-admissible-blowup-comp", "prop-nagata-global-blowup-cover-independent"]
+++
Let $X$ be qcqs, let $U,V\subseteq X$ be open, let $p\colon Y\to X$ be a
morphism and let $f\colon U\to Y$ be a section of $p$ over $U$. Let
$q\colon X'\to X$ be a $V$-admissible blow-up, write $p'\colon Y\times_XX'\to X'$ for the base change of $p$ and $f'\colon q^{-1}(U)\to Y\times_XX'$ for the
base change of $f$. If the conclusion of
[thm-nagata-conrad-elimination] holds for the data
$(X',q^{-1}(U),q^{-1}(V),p',f')$, then it holds for $(X,U,V,p,f)$.

## Proof

Let $X''\to X'$ be a $q^{-1}(V)$-admissible blow-up solving the problem
upstairs. By [lemma-nagata-admissible-blowup-comp] the composite
$X''\to X'\to X$ is again a $V$-admissible blow-up of $X$: there is a
$V$-admissible centre $K$ on $X$ and an isomorphism
$X''\cong\operatorname{Bl}_K(X)$ over $X$. The conclusion of the theorem
depends on the blow-up only through its total space over $X$, so it suffices
to produce it for $X''\to X$. The extension of $f$ is the extension of $f'$
followed by the projection $Y\times_XX'\to Y$; that it is a section of $p$ and
extends $f$ follows from the two projection formulas defining $f'$. For the
closedness of the graph, the square exhibiting $Y\times_XX''$ as
$(Y\times_XX')\times_{X'}X''$ is cartesian, and the two graphs correspond
under the resulting isomorphism.
