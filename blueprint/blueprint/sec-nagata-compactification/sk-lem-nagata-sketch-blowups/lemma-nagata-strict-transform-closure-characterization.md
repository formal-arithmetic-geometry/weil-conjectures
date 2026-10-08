+++
id = "lemma-nagata-strict-transform-closure-characterization"
kind = "lemma"
title = "Scheme-theoretic closure characterization"
order = 159
lean = ["AlgebraicGeometry.strictTransform"]
uses = ["def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-power-torsion-kernel-localization", "lemma-nagata-power-torsion-quotient-torsionfree", "lemma-nagata-scheme-image-ideal-qc", "prop-nagata-strict-transform-closed-fiber-product"]
+++
Let $f\colon Y\to X$, let $\mathcal I$ be a finite-type quasi-coherent
ideal on $X$, put $X'=\operatorname{Bl}_{\mathcal I}(X)$, and let
$U=X\setminus V(\mathcal I)$. The strict transform is the smallest
closed subscheme of $Y\times_XX'$ through which

$$
Y\times_XU\longrightarrow Y\times_XX'
$$

factors. In particular it is the scheme-theoretic closure of this open
part.

## Proof

On an $a$-chart put $C=C_a(A,B,I)$. A closed subscheme containing the
preserved open is given by a quotient $C\twoheadrightarrow C/K$ for which
$K_a=0$. By
[lemma-nagata-power-torsion-kernel-localization], this says exactly
that $K\subseteq\Gamma_{(a)}(C)$. Therefore the quotient
$C\twoheadrightarrow C/\Gamma_{(a)}(C)$ factors through every such
quotient, which is precisely the containment of the corresponding closed
subschemes in the required direction. It becomes an isomorphism after
inverting $a$, again by the kernel description. The quotient has no
residual $a$-power torsion by
[lemma-nagata-power-torsion-quotient-torsionfree], so this local
characterization is stable under further restriction. The chart
descriptions glue by
[prop-nagata-strict-transform-closed-fiber-product], proving the
asserted minimality globally.
