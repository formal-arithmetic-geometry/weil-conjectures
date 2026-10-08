+++
id = "lemma-nagata-graph-extension"
kind = "lemma"
title = "Properties of the graph-extension construction, [stacks-project]"
order = 243
lean = ["AlgebraicGeometry.Compactification.nonempty_properExtension"]
uses = ["def-nagata-admissible-blowup", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-elimination-indeterminacy", "def-nagata-global-blowup", "def-nagata-graph-extension", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-nagata-strict-transform", "lem-weil-pbc-closed-immersion-from-composite", "lemma-nagata-admissible-blowup-over-open", "lemma-nagata-blowup-proper", "lemma-nagata-elimination-indeterminacy", "lemma-nagata-open-immersion-qc-over-separated-target", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-partial-section", "lemma-nagata-scheme-image-strict-transform", "lemma-nagata-strict-transform-ambient-closed", "lemma-nagata-strict-transform-closure-characterization", "lemma-nagata-strict-transform-over-complement", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
The map $Y^{\mathrm{gr}}\to Y$ is $V$-admissible,
$V\subseteq V^{\mathrm{gr}}\subseteq Y^{\mathrm{gr}}$ is open, and
$\psi^{\mathrm{gr}}\colon V^{\mathrm{gr}}\to U$ is proper. Its
restriction to $V$ is the original inclusion, its inverse image of $V$ is
exactly $V$, and this restriction is an isomorphism.

## Proof

Apply Stacks Project, Tag 0F3Z (Lemma 38.33.6), to the separated
finite-type morphism $U\to S$, the quasi-compact open $V\subseteq U$, and
the chosen compactification $V\hookrightarrow Y\to S$. The theorem forms
the scheme-theoretic image of the graph
$V\to Y\times_SU$, exactly the object $Z_V$ in
[def-nagata-graph-extension], and after a $V$-admissible blow-up it
makes the strict transform an open subscheme of
$Y^{\mathrm{gr}}\times_SU$. The open-immersion assertion is the
elimination statement in
[lemma-nagata-elimination-indeterminacy]; the closed-subscheme
assertion is
[lemma-nagata-strict-transform-ambient-closed]. Since
$Y^{\mathrm{gr}}\to S$ is proper by
[thm-nagata-global-blowup-proper], the projection to $U$ is proper,
and its restriction is the transported map $\psi^{\mathrm{gr}}$.
Finally,
[lemma-nagata-scheme-image-partial-section] identifies the graph
image over the open $V\subseteq Y$ with $V$, while
[lemma-nagata-strict-transform-over-complement] identifies the
admissible blow-up with the identity over that open. Therefore

$$
V^{\mathrm{gr}}\cap
(Y^{\mathrm{gr}}\times_YV)=V
$$

as schemes, the second projection agrees with the original inclusion on
this open, and its inverse image of $V\subseteq U$ is exactly $V$.
