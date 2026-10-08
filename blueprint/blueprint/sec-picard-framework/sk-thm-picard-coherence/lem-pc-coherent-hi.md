+++
id = "lem-pc-coherent-hi"
kind = "lemma"
title = "Coherence and finiteness of higher direct images"
order = 659
uses = ["def-pc-morphism-conventions", "lem-pc-finite-support-hi", "lem-pc-projective-coherent-higher-images"]
lean = ["AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage"]
+++
(Cohomology of Schemes, Proposition 30.19.1 (Tag
[02O5](https://stacks.math.columbia.edu/tag/02O5)) and Lemma 30.19.2
(Tag [02O6](https://stacks.math.columbia.edu/tag/02O6)); and Lemma
30.4.5, Tag [01XJ](https://stacks.math.columbia.edu/tag/01XJ).)
Let $f:X\to S$ be a proper morphism with $S$ locally Noetherian and let
$\mathcal{F}$ be a coherent $\mathcal{O}_X$-module. Then $R^if_*\mathcal{F}$ is coherent for all
$i$; locally on $S$ (and globally if $S$ is quasi-compact)
$R^if_*\mathcal{F}=0$ for $i\gg0$; if $S=\operatorname{Spec}(A)$ with $A$ Noetherian
then the $H^i(X,\mathcal{F})$ are finite $A$-modules. (No bound uniform
over a non-quasi-compact $S$ exists in general: for
$S=\coprod_{n\ge1}\operatorname{Spec}k$, $X=\coprod_n\mathbf P^n_k$ and
$\mathcal F=\mathcal O(-n-1)$ on the $n$-th piece, $R^nf_*\mathcal F\ne0$
for every $n$.)

## Proof

The vanishing for sufficiently large $i$, over each affine (or
quasi-compact) open of $S$, follows from the finite
affine-cover bound of [lem-pc-finite-support-hi].
If $f$ is projective, coherence and finite generation are
[lem-pc-projective-coherent-higher-images], applied locally on
the base.
For a general proper $f$ over a locally Noetherian base the assertion is
the recorded classical input named in the statement: Cohomology of
Schemes, Proposition 30.19.1 (Tag
[02O5](https://stacks.math.columbia.edu/tag/02O5)) reads ``Let $S$
be a locally Noetherian scheme. Let $f:X\to S$ be a proper morphism.
Let $\mathcal{F}$ be a coherent $\mathcal{O}_X$-module. Then
$R^if_*\mathcal{F}$ is a coherent $\mathcal{O}_S$-module for all
$i\geq0$.'', and its proof reduces to the projective case by Chow's
lemma (Cohomology of Schemes, Lemma 30.18.1, Tag
[0200](https://stacks.math.columbia.edu/tag/0200)) together with the
twisting vanishing and the relative Leray spectral sequence; the affine
finiteness clause is Lemma 30.19.2 (Tag
[02O6](https://stacks.math.columbia.edu/tag/02O6)). The statement of
this lemma, whose base is locally Noetherian, is exactly the proposition
cited, so it is discharged by the recorded input; the vanishing bound and
the projective case are in addition proved here, and every use below is
over a locally Noetherian base.
