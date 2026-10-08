+++
id = "sk-lem-nagata-sketch-blowups"
kind = "section"
title = "Blow-ups and strict transforms"
order = 87
uses = ["sk-def-nagata-sketch-data", "sk-lem-nagata-sketch-closure"]
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isProper_blowupMap", "AlgebraicGeometry.strictTransform", "AlgebraicGeometry.IsAdmissible.exists_extend", "AlgebraicGeometry.IsAdmissible.isSchemeTheoreticallyDominant_preimage_ι"]
+++
*Lemma (sketch).*

Finite-type ideal blow-ups are proper. Admissible blow-ups can be
composed, refined simultaneously, and extended from a quasi-compact open
to a qcqs ambient scheme while preserving a specified open on which they
are trivial. For $T\to X$ and $b:X'\to X$ with centre $C$, the
*strict transform* of $T$ is the scheme-theoretic closure of
$T\times_X(X\setminus C)$ in $T\times_XX'$; it is the blow-up of $T$
in the pulled-back ideal. Scheme-theoretic density of a preserved open
survives an admissible blow-up.

## Proof

Use the Rees algebra $\bigoplus_{n\geq0}\mathcal I^n$ and its Proj.
For $I=(a_1,\ldots,a_r)$ on $\Spec A$, the charts are
$\Spec A[I/a_i]$; quotienting the pulled-back chart by its
$a_i$-power torsion gives the strict transform. These descriptions
commute with localization. Finite-type ideals extend across
quasi-compact opens; product ideals give common refinements, and the
composition construction combines successive centres. The same charts
show that a scheme-theoretically dense preserved open remains so.
Moreover, choosing a finite-type ideal with zero set exactly
$X\setminus U$ makes $U$ scheme-theoretically dense in its blow-up,
even when $U$ was not dense in $X$.

Uses: [sk-def-nagata-sketch-data], [sk-lem-nagata-sketch-closure]
