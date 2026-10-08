+++
id = "lem-exc-punctured-curve-branches"
kind = "lemma"
title = "The punctured strictly local curve has DVR branches"
order = 1918
uses = ["def-exc-local-curve-branches", "def-weil-pbc-henselian-terminology", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-finite-stalk-formula"]
+++
Let $R$ be a reduced excellent one-dimensional
strictly henselian
local ring with algebraically closed residue field of
characteristic $p>0$. Its punctured spectrum is a finite
disjoint union of spectra of fraction fields of excellent
strictly henselian DVRs with that same residue field.
These fields are the factors obtained from the
branch algebra.

## Proof

Excellence implies the Nagata property, so the normalization
$B=B(R)$ of [def-exc-local-curve-branches] is finite
over $R$. Here we use the finite-normalization theorem
for excellent local rings from commutative algebra. The
one-dimensional calculation is recorded in
[Stacks
Project, Tag 0C3S](https://stacks.math.columbia.edu/tag/0C3S) (Lemma 33.39.2, stated there for a reduced Nagata
one-dimensional local ring, the case reached here through the Nagata
property above). Quotients and finite algebras of
excellent rings are excellent.

A finite algebra over a henselian local ring decomposes
as a finite product of local algebras, by lifting the
idempotents of its Artinian closed fibre. This is the
algebra calculation in
[lemma-weil-pbc-finite-stalk-formula], using the henselian
property of [def-weil-pbc-henselian-terminology].
Each factor $B_b$ here is a Noetherian normal local
domain of dimension one. Indeed its integral finite
map lies over a component $R/\mathfrak p_a$, and integral
extensions preserve this dimension. The commutative-algebra
DVR criterion for one-dimensional Noetherian normal local
domains therefore applies; see
[Tag 00PD](https://stacks.math.columbia.edu/tag/00PD).
The factors are henselian; their residue fields are finite
extensions of the algebraically closed residue field of
$R$, hence equal to it. Thus each $B_b$ is strictly
henselian and excellent.

Choose $f\in\mathfrak m_R$ outside every minimal prime,
by finite prime avoidance. In a one-dimensional local
ring every prime other than the maximal ideal is minimal.
Thus $D(f)$ is exactly the punctured spectrum, with
$D(f)$ in the scheme conventions of
[def-weil-pbc-scheme-conventions]. The reduced
Noetherian zero-dimensional algebra $R_f$ is a product
of fields and equals $Q(R)$. Integral closure commutes
with localization, so $B_f=R_f$. In each DVR factor
$B_b$, the nonzero element $f$ belongs to its maximal
ideal; inverting it gives $\operatorname{Frac}B_b$.
Consequently

$$
\operatorname{Spec}R\setminus\{\mathfrak m_R\}
=\operatorname{Spec}R_f
\simeq\coprod_b\operatorname{Spec}\operatorname{Frac}B_b,
$$

as asserted.
