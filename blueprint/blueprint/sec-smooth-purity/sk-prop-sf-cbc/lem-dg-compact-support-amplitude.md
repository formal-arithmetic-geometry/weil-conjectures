+++
id = "lem-dg-compact-support-amplitude"
kind = "lemma"
title = "The compact-support bound uses the original fibres"
order = 1625
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-amb-etale-compact-support", "def-weil-pbc-derived-categories", "def-weil-pbc-scheme-conventions", "lem-kun-cd-sep-closed-point", "lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-geometric-stalk-conservative", "thm-nagata-compactification", "thm-sc-finite-type-torsion-cd"]
+++
Let $f:X\to Y$ be a separated finite-type morphism of finite-type
schemes over a field, with geometric fibres of dimension at most $d$.
Let $A$ be a finite ring whose additive exponent is invertible on
$Y$. For every etale $A$-module sheaf $F$, its
compact-support direct image
satisfies

$$
R^qf_!F=0\qquad(q>2d).
$$

All functors here act on ordinary
derived categories.

## Proof

Choose $X\xrightarrow{j}\overline X\xrightarrow{r}Y$ by
[thm-nagata-compactification]. By
[def-amb-etale-compact-support], $Rf_!F=Rr_*j_!F$.
For a geometric point $\bar y$, proper base change
[cor-weil-pbc-geometric-fiber-finite] computes its stalk as

$$
H^q(\overline X_{\bar y},j_{\bar y!}F|_{X_{\bar y}}).
$$

Let $C$ be the reduced closure of the open subscheme
$X_{\bar y}$ in $\overline X_{\bar y}$.
Every irreducible component of $C$ meets $X_{\bar y}$ in a
dense open. For a finite-type scheme over a field, a dense open in
an irreducible component has the same dimension, by the dimension
formula for finitely generated algebras. Hence $\dim C\leq d$.
The sheaf $j_{\bar y!}F$ is zero outside $C$; it is the closed
direct image of its restriction to $C$, since this assertion is
the identity or the zero map at every geometric stalk.
Closed direct image is exact by
[lemma-weil-pbc-finite-direct-image-exact], and therefore its
cohomology on $\overline X_{\bar y}$ is the cohomology on $C$.
The algebraically closed base field has torsion cohomological
dimension zero in the sense of the vanishing used here, a separably
closed field being the case of [lem-kun-cd-sep-closed-point], so
[thm-sc-finite-type-torsion-cd] kills this cohomology above $2\dim C\leq2d$.
All geometric stalks now vanish; use
[lemma-weil-pbc-geometric-stalk-conservative].
This argument puts no bound on the dimension of the entire
compactified fibre $\overline X_{\bar y}$.
