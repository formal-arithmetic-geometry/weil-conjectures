+++
id = "sbc-lem-bc-integral-surjective"
kind = "lemma"
title = "Integral surjective base change on the target"
order = 1394
uses = ["lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-five-lemma-transfer", "sbc-def-base-change-map", "sbc-def-base-change-property", "sbc-lem-bc-injectivity", "sbc-lem-integral-etale-direct-image-exact"]
+++
With $f:X\to S$ and $n$ as in [sbc-def-base-change-property] assume for
some $q\geq1$ that $\mathrm{BC}(f,n,q-1)$ holds universally (in the
single degree $q-1$, which is all that [sbc-lem-bc-injectivity]
needs).
Consider commutative
diagrams

$$
\begin{array}{ccccccc}
X & \xleftarrow{\;\;} & X' & \xleftarrow{\;\;} & Y & \xleftarrow{\pi'} & Y'\\
f\big\downarrow & & \big\downarrow f' & & \big\downarrow e & &
\big\downarrow e'\\
S & \xleftarrow{\;\;} & S' & \xleftarrow{\;\;} & T
\xleftarrow{\;\pi\;} & T' &
\end{array}
\quad\text{and}\quad
\begin{array}{ccccc}
X' & &\xrightarrow{h'=h\circ\pi'}& &Y'\\
f'\big\downarrow & & & & \big\downarrow e'\\
S' & &\xrightarrow{g'=g\circ\pi}& &T'
\end{array}
$$

where all squares are Cartesian, $g$ is quasi-compact and
quasi-separated, and $\pi:T'\to T$ is integral surjective. Let
$\mathcal F$ be an abelian sheaf on $T_{\Et}$ annihilated by $n$ and set
$\mathcal F'=\pi^{-1}\mathcal F$. If

$$
f'^{-1}R^qg'_*\mathcal F'\xrightarrow{\ \sim\ }
R^qh'_*(e')^{-1}\mathcal F'
$$

is an isomorphism, then
$f'^{-1}R^qg_*\mathcal F\to R^qh_*e^{-1}\mathcal F$ is an isomorphism.
(*Stacks Project, Lemma 59.88.3, [Tag `0F04`](https://stacks.math.columbia.edu/tag/0F04).*)

## Proof

The maps $\mathcal F\to\pi_*\pi^{-1}\mathcal F$ are injective as $\pi$
is surjective, so by [sbc-lem-bc-injectivity] (2), applied to the base
change $f'$ of $f$ along $S'\to S$ and the quasi-compact
quasi-separated $g:T\to S'$, the task reduces to
showing the base-change map for $\pi_*\mathcal F'$ is an isomorphism.
For an integral morphism $\pi$ the direct image is exact by
[sbc-lem-integral-etale-direct-image-exact] (the finite case being
the one noted in [lemma-weil-pbc-finite-direct-image-exact]),
$R^qg_*\pi_*\mathcal F'=R^qg'_*\mathcal F'$ by the Grothendieck
spectral sequence for the composite, the Cartesian identification gives
$e^{-1}\pi_*\mathcal F'=\pi'_*(e')^{-1}\mathcal F'$, and
$R^qh_*\pi'_*(e')^{-1}\mathcal F'=R^qh'_*(e')^{-1}\mathcal F'$ by that
spectral sequence; the assumption on $\mathcal F'$ then gives the
isomorphism for $\pi_*\mathcal F'$, hence for $\mathcal F$ by the
five-lemma transfer of [lemma-weil-pbc-five-lemma-transfer].
