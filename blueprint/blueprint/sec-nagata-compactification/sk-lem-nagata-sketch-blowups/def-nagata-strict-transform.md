+++
id = "def-nagata-strict-transform"
kind = "definition"
title = "Strict transform"
order = 136
lean = ["AlgebraicGeometry.strictTransform"]
uses = ["def-nagata-global-blowup", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-scheme-image-ideal-qc"]
+++
Let $Z\to X$ be a morphism and let $X'\to X$ be the blow-up of a
finite-presentation center $C\subseteq X$. Put $U=X\setminus C$; then
$U\hookrightarrow X$ is quasi-compact. The *strict transform* of $Z$
is the scheme-theoretic closure of

$$
(Z\times_XU)\times_U(X'\times_XU)
$$

in $Z\times_XX'$, in the sense of
[def-nagata-scheme-theoretic-closure]. It is not enough to use only
the topological closure.
