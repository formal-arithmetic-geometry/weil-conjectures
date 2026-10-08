+++
id = "thm-weil-pbc-stein-inputs"
kind = "remark"
title = "The two classical inputs of Stein connectedness"
order = 1093
uses = ["def-weil-pbc-henselian-terminology", "def-weil-pbc-stein-factorization", "lemma-weil-pbc-spectral-restriction"]
tags = ["latex:openproblem"]
+++
Let $(A,I)$ be an affine henselian pair with $S=\operatorname{Spec}A$, and in
the Stein factorization $p=s\circ q$ of
[def-weil-pbc-stein-factorization] of a proper $p:Y\to S$ let
$S'=\operatorname{Spec}B$. The two inputs are:

- (i) *finiteness.* $A\to B$ is finite, equivalently $p_*\mathcal O_Y$ is a
  coherent, hence finitely generated, $\mathcal O_S$-algebra. For $A$
  Noetherian this is Stacks Project, More on Morphisms, Section 37.53 (Tag
  [03GX](https://stacks.math.columbia.edu/tag/03GX)); for a general affine
  base it is not proved in this blueprint. The route available here is the
  approximation chain of this chapter: descend $Y\to S$ to a finitely
  presented model over a Noetherian base
  ([lem-weil-pbc-etale-finite-data-descent]), apply the Noetherian statement
  there, and use the affine limit formula of
  [lem-weil-pbc-etale-section-continuity] for the structure sheaf to identify
  $H^0(Y,\mathcal O_Y)$ with the base change of the model. That chain is not
  written out.
- (ii) *connectedness.* Every irreducible closed subset of $Y$ meets
  $Y_0=Y\times_SS_0$ in a nonempty connected subset. This is the
  henselian-pair proper-base-change input, Stacks Project, Etale Cohomology,
  Lemma 59.91.1 (Tag [0A0B](https://stacks.math.columbia.edu/tag/0A0B), the
  comparison $\Gamma(X,\mathcal F)=\Gamma(Z,\mathcal F|_Z)$ for sheaves on
  the underlying topological space of a henselian pair; the connectedness
  consequence used here is the Stein-factorization step of its proof, Theorem
  37.53.5, Tag [03H2](https://stacks.math.columbia.edu/tag/03H2)); it is a
  classical theorem about henselian pairs and is not proved in this
  blueprint.

A third input, used by Stage 1 of the degree-zero comparison, is the Zariski
comparison $\Gamma(Y,G)\cong\Gamma(Y_0,G|_{Y_0})$ for the *constructible*
torsion sheaf $G$ that occurs there. The locally constant form proved in
[lemma-weil-pbc-spectral-restriction] does not give it, its statement carrying
a counterexample for sheaves that are not locally constant, so that
comparison is an obligation as well.
