+++
id = "sk-thm-picard-cech"
kind = "section"
title = "Čech-to-derived"
order = 599
uses = ["sk-def-groth-ss"]
lean = ["CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence"]
+++
*Theorem (sketch).*

Let $\mathcal C$ be a site with fibre products, $X\in\Ob(\mathcal C)$
and $\mathfrak U=\{U_i\to X\}_{i\in I}$ a covering. For
$F\in\Sh(X)$ there is a first-quadrant spectral sequence

$$
E_2^{p,q}=\Cech^p\bigl(\mathfrak U,\ \mathcal H^q(F)\bigr)
\ \Longrightarrow\ H^{p+q}(X,F),
$$

where $\mathcal H^q(F)$ is the presheaf $V\mapsto H^q(V,F)$.

## Proof

Write $C^\bullet(\mathfrak U,-)$ for the (alternating) Čech complex of
the covering,

$$
C^p(\mathfrak U,G)=\prod_{i_0,\dots,i_p}
G\bigl(U_{i_0}\times_X\dots\times_XU_{i_p}\bigr),
$$

so that $\Cech^p(\mathfrak U,G)=H^p\bigl(C^\bullet(\mathfrak U,G)\bigr)$.

*Step 1 (the double complex).* Choose an injective resolution
$F\to I^\bullet$ of abelian sheaves on $\mathcal C/X$ and put
$D^{p,q}=C^p(\mathfrak U,I^q)$, a first-quadrant double complex of
abelian groups. By [sk-def-groth-ss] its two filtrations give two
spectral sequences, both abutting to $H^\bullet(\operatorname{Tot}D)$
with the image filtration, which is finite in each degree.

*Step 2 (one filtration gives the $E_2$-page).* Fix $p$ and take
cohomology of $D^{p,\bullet}$ in the $q$-direction. Products of
complexes of abelian groups have the product of the cohomologies, and for
each $V=U_{i_0}\times_X\dots\times_XU_{i_p}$ the restriction
$I^\bullet|_V$ is again an injective resolution, restriction along the
localization $\mathcal C/V\to\mathcal C/X$ having an exact left adjoint.
Hence $H^q\bigl(I^\bullet(V)\bigr)=H^q(V,F)$ and

$$
E_1^{p,q}=C^p\bigl(\mathfrak U,\mathcal H^q(F)\bigr),\qquad
E_2^{p,q}=\Cech^p\bigl(\mathfrak U,\mathcal H^q(F)\bigr),
$$

for the presheaf $\mathcal H^q(F)$ of the statement.

*Step 3 (the other filtration gives the abutment).* Fix $q$ and
consider the column $C^\bullet(\mathfrak U,I^q)$. An injective abelian
sheaf is injective as a *presheaf*
([Stacks `03F6`](https://stacks.math.columbia.edu/tag/03F6)),
the Čech complex only sees presheaf values, and the Čech complex
of an injective presheaf is acyclic in positive degrees: it is
$\Hom(\Z_{\mathfrak U,\bullet},-)$ applied to the complex of free
presheaves of the covering, and $\Hom(-,I^q)$ is exact. So
$C^\bullet(\mathfrak U,I^q)$ has cohomology $I^q(X)$ in degree $0$ and
$0$ above
([Stacks `03AW`](https://stacks.math.columbia.edu/tag/03AW)).
This filtration therefore collapses onto the bottom edge and

$$
H^n(\operatorname{Tot}D)\cong H^n\bigl(I^\bullet(X)\bigr)=H^n(X,F).
$$

*Step 4 (the edge map).* Combining Steps 2 and 3 gives the
displayed sequence. When $\mathcal H^q(F)$ vanishes for $q>0$ the
sequence collapses onto the row $q=0$ instead, and the edge maps
$\Cech^q(\mathfrak U,F)\to H^q(X,F)$ are isomorphisms; this is the
collapse used in [sk-lem-picard-cech-computes].

This is Stacks, Cohomology on Sites, Lemma 21.10.6
([`03AZ`](https://stacks.math.columbia.edu/tag/03AZ)); the
detailed form is Blueprint 06, `lem-sc-cech-spectral`.

Uses: [sk-def-groth-ss]
