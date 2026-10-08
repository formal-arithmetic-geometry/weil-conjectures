+++
id = "lem-weil-pbc-grothendieck-spectral-sequence"
kind = "lemma"
title = "Grothendieck spectral sequence for a composite"
order = 1186
uses = ["def-sp-composite-acyclicity", "def-sp-etale-dictionary", "def-weil-pbc-direct-image", "lem-weil-pbc-direct-image-preserves-injectives", "thm-sp-grothendieck", "thm-sp-grothendieck-base-change"]
+++
Let $X\xrightarrow{f}Y\xrightarrow{h}Z$ be morphisms of schemes and let $F$ be
a sheaf on $X_{\Et}$. There is a functorial first-quadrant spectral sequence

$$
 E_2^{p,q}=R^ph_*R^qf_*F
 \Longrightarrow R^{p+q}(hf)_*F.
$$

No acyclicity hypothesis on $F$ is needed: the construction is via an
injective resolution of $F$, and $f_*$ preserves injectives because $f^{-1}$
is exact (the standard Grothendieck spectral sequence for the left exact
functors $f_*$, $h_*$; for bounded-below complexes with torsion cohomology the
same statement holds for the derived pushforwards by the same argument). It is
compatible with inverse image in a cartesian base change.

## Proof

The pair $(f_*,h_*)$ is a composable pair, with the hypothesis of the
statement asserting that $f_*F$ is $h_*$-acyclic; for $F$ injective this
hypothesis holds by [lem-weil-pbc-direct-image-preserves-injectives].
Therefore the Grothendieck spectral sequence theorem of the spectral-sequence
chapter supplies the functorial first-quadrant spectral sequence
$E_2^{p,q}=R^ph_*R^qf_*F\Longrightarrow R^{p+q}(hf)_*F$, whose $E_2$-page,
edge maps and convergence are those of the composite of left exact functors;
the compatibility with inverse image in a cartesian base change is the
naturality of its base-change form, in the dictionary of the
spectral-sequence chapter.
