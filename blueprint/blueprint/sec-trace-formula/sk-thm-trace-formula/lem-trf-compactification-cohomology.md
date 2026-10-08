+++
id = "lem-trf-compactification-cohomology"
kind = "lemma"
title = "Cohomology on a chosen compactification"
order = 2377
uses = ["def-compact-support-direct-image-detailed", "def-trf-coefficient-conventions", "def-weil-compact-support-candidate", "def-weil-compactifications-refinements", "def-weil-extension-by-zero", "def-weil-finite-coefficient-point", "def-weil-finite-torsion-constructibility", "def-weil-ordinary-compact-cohomology", "def-weil-pbc-etale-origin-witness", "prop-compactification-coherence-detailed"]
+++
Use the finite coefficient
ring $A$, and let $j:X\hookrightarrow\bar X$ be a
compactification
of $a_X:X\to s=\Spec k$, with proper map $\bar a:\bar X\to s$.
For a bounded
constructible complex $K$ equipped with an
explicit etale-origin
witness, there is a canonical natural isomorphism

$$
C_{j,K}:R\Gamma_c(X,K)\xrightarrow{\sim}
R\Gamma(\bar X,j_!K).
$$

Here $j_!K$ is extension by
zero, and the ordinary
and compact-support cohomology use the
fiber over $s$.
The comparison respects changes of compactification.

## Proof

For the chosen compactification,
[def-weil-compact-support-candidate] gives
$Ra_{X!}^{\,j}K=R\bar a_*j_!K$. The comparison in
[def-compact-support-direct-image-detailed], with the cocycle identity
of [prop-compactification-coherence-detailed], identifies $Ra_{X!}K$
with this candidate. The witness $K\simeq\nu_X^*L$, with
$L\in D^+(X_{\mathrm{et}},A)$, from
[def-weil-pbc-etale-origin-witness] puts $K$ in precisely
the domain on which compactification coherence has been proved.
Neither etale descent of all constructible pro-etale complexes nor
coherence for arbitrary pro-etale objects is asserted here.
Apply the fiber functor of
[def-weil-finite-coefficient-point]. By
[def-weil-ordinary-compact-cohomology], the source becomes
$R\Gamma_c(X,K)$ and the target becomes
$R\Gamma(\bar X,j_!K)$. This is $C_{j,K}$.
Naturality is the naturality of the candidate comparisons.
Their cocycle identity proves the asserted compatibility when the
compactification is changed.
