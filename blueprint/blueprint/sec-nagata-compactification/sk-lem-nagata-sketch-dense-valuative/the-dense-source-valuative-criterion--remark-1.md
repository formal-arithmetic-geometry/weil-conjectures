+++
id = "the-dense-source-valuative-criterion--remark-1"
kind = "remark"
title = "Formalization route"
order = 283
uses = ["lemma-nagata-composite-valuation-ring", "lemma-nagata-dense-flat-pullback", "lemma-nagata-dense-valuation-probe", "lemma-nagata-reduced-dense-image-schematic", "lemma-nagata-valuation-intersection", "lemma-nagata-valuation-ring-extension"]
+++
In Lean the two conclusions are split into
`ValuativeCriterion.universallyClosed_of_isDominant` and
`ValuativeCriterion.isSeparated_of_isDominant`; both are fully
proved. The ingredients — the valuation probe
(Tag 02JQ, `nonempty_valuationProbe`), the
composite valuation ring (`ValuationSubring.comapResidue`), the
intersection lemma (Tag 052K,
`ValuationSubring.comap_eq_of_le_comap`) and the extension lemma
(Tag 00IA, `ValuationSubring.exists_comap_eq`, via
Mathlib's Chevalley extension theorem rather than the Zorn argument) — live
in the `WeilConjectures.Mathlib` helper files. The formalized proof
deviates from the Stacks Project text in two reductions: instead of
replacing $U,X,S$ by their reductions, the morphism $h$ is factored through
its scheme-theoretic image — the factor map `Scheme.Hom.toImage` is
scheme-theoretically dominant with no reducedness hypothesis, and the
valuative data factors through the image because $\operatorname{Spec}$ of a
valuation ring or of a field is reduced
(`Scheme.IdealSheafData.le_ker_of_range_subset_support`); and the
polynomial presentation of a field-valued point is inlined via
`MvPolynomial.eval₂Hom`. The flat-pullback and reduced-density
inputs ([lemma-nagata-dense-flat-pullback],
[lemma-nagata-reduced-dense-image-schematic]) are provided by Mathlib's
`IsSchemeTheoreticallyDominant` API.

## Proof

We first verify the existence part of the valuative criterion for $f$.
Start with an arbitrary square

$$
\operatorname{Spec}(K)\longrightarrow X,
\qquad
\operatorname{Spec}(A)\longrightarrow S.
$$

Valuation rings and fields are reduced, so replacing $U,X,S$ by their
reductions does not change this lifting problem. After this replacement,
topological density of $h(U)$ says that the scheme-theoretic image of
$h$ is all of $X$ by
[lemma-nagata-reduced-dense-image-schematic]. We may also replace
$S$ by an affine open through
which $\operatorname{Spec}(A)\to S$ factors; write it as
$\operatorname{Spec}(R)$.

Choose an affine open $\operatorname{Spec}(B)\subseteq X$ through which
the generic map factors. Choose the polynomial $B$-algebra $P$ and
surjection $P\twoheadrightarrow K$ presenting the field-valued point. The map
$\operatorname{Spec}(P)\to X$ is flat. Therefore

$$
U\times_X\operatorname{Spec}(P)\longrightarrow\operatorname{Spec}(P)
$$

is scheme-theoretically dense by
[lemma-nagata-dense-flat-pullback].

Apply [lemma-nagata-dense-valuation-probe] to the point
$\operatorname{Spec}(K)\subseteq\operatorname{Spec}(P)$. We obtain a
valuation ring $A'$, with fraction field $K'$, whose generic point maps
to $U\times_X\operatorname{Spec}(P)$ and whose closed point maps to the
chosen $K$-point of $\operatorname{Spec}(P)$. If
$k'=A'/\mathfrak m_{A'}$, this gives a field embedding
$K\to k'$. Choose a valuation ring $A''\subseteq k'$ dominating the
image of $A$, with fraction field $k'$, by
[lemma-nagata-valuation-ring-extension].

Form the inverse-image ring

$$
C=\{a\in A'\mid a\bmod\mathfrak m_{A'}\in A''\}.
$$

By [lemma-nagata-composite-valuation-ring], $C$ is a valuation ring
with fraction field $K'$, and $C/\mathfrak m_{A'}=A''$. Since
$A''$ contains the image of $A$, the map $R\to A'$ factors through
$C$. Thus the generic map
$\operatorname{Spec}(K')\to U$ and the map
$\operatorname{Spec}(C)\to S$ form a diagram covered by the hypothesis.
Let $g_C\colon\operatorname{Spec}(C)\to X$ be its unique lift.

There are now two maps $\operatorname{Spec}(A')\to X$: one is obtained
from $\operatorname{Spec}(A')\to\operatorname{Spec}(P)\to X$, and the
other by composing $\operatorname{Spec}(A')\to\operatorname{Spec}(C)$
with $g_C$. They have the same generic map through $U$ and the same
composite to $S$. Applying the assumed uniqueness to the valuation ring
$A'$ shows that the two maps are equal.

Restrict $g_C$ along the closed immersion
$\operatorname{Spec}(A'')\to\operatorname{Spec}(C)$ induced by
$C/\mathfrak m_{A'}\cong A''$. Its generic point is
$\operatorname{Spec}(k')$, the residue field of the prime
$\mathfrak m_{A'}\subset C$. The preceding equality on
$\operatorname{Spec}(A')$ identifies this generic map with the closed-point
residue map of $\operatorname{Spec}(A')\to X$ and hence with the base
change of the original $\operatorname{Spec}(K)\to X$. Let $x\in X$ be the image
of the closed point. The image of the induced local homomorphism
$\mathcal O_{X,x}\to A''$ lies in the subfield $K\subseteq k'$.
By [lemma-nagata-valuation-intersection],
$K\cap A''=A$. Hence the local homomorphism factors through $A$, and
therefore defines the required lift $\operatorname{Spec}(A)\to X$.
The existence part of the valuative criterion now shows that $f$ is
universally closed.

Finally suppose $f$ is quasi-separated. Then its diagonal
$\Delta_f\colon X\to X\times_SX$ is quasi-compact. A map
$\operatorname{Spec}(A)\to X\times_SX$ is a pair of maps to $X$.
If their common generic restriction factors through $U$, the uniqueness
hypothesis for $f$ forces the pair to be equal, hence to factor uniquely
through $\Delta_f$. Applying the universally-closed part just proved to
$\Delta_f$ and $h\colon U\to X$ makes the diagonal universally closed.
Since every diagonal is an immersion, a universally closed diagonal is a
closed immersion. Thus $f$ is separated.
