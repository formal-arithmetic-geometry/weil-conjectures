+++
id = "thm-a1-affine-curve-upper"
kind = "theorem"
title = "Affine compact-support upper bound"
order = 2807
uses = ["def-weil-open-closed-recollement", "def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "lem-a1-affine-hc0", "lem-a1-affine-hc2-pure", "lem-a1-curve-hc2-bound", "lem-a1-extension-bounds", "lem-a1-finite-boundary-cohomology", "lem-a1-finite-boundary-weights", "lem-a1-finite-map-curve", "lem-a1-reduction-composition", "lem-a1-reduction-lisse-pure", "lem-a1-subquotient-extension-bounds", "lem-a1-unramified-at-infinity", "lem-a1-weight-bound-constant-extension", "lem-wf-boundary-semicontinuity", "lem-zl-affine-curve-range", "prop-a1-curve-boundary-sequence", "prop-sf-open-closed-triangle-all-stages", "thm-a1-line-middle-extension-upper"]
+++
Let $C_0$ be a smooth geometrically connected affine curve and let
$\mathcal F$ be a lisse Weil sheaf that is punctually $\iota$-pure of
weight $w$. Then every
compactly supported cohomology group
$H_c^i(C,\mathcal F)$ has weights at most $w+i$. More precisely,
$H_c^0(C,\mathcal F)=0$, $H_c^2(C,\mathcal F)$ is $\iota$-pure of
weight $w+2$, and $H_c^i(C,\mathcal F)=0$ for $i\notin\{0,1,2\}$.

## Proof

The bounds in degrees zero and two are
[lem-a1-affine-hc0], [lem-a1-curve-hc2-bound]; the first is the
vanishing $H_c^0(C,\mathcal F)=0$, and the purity of weight $w+2$ in
degree two is [lem-a1-affine-hc2-pure].
There is no cohomology outside degrees zero through two, by the
cohomological range [lem-zl-affine-curve-range] of an affine curve
applied to the (constructible) lisse sheaf $\mathcal F$.

For degree one choose the finite map of
[lem-a1-finite-map-curve]. By
[lem-a1-reduction-composition], the cohomology to be bounded is
$H_c^1(\mathbf A^1,\mathcal K)$, where
$\mathcal K=g_*j_!\mathcal F$.
On the open
$W_0=\mathbf A^1\setminus(B\cup g(C'_0\setminus C_0))$
the restriction of the transported complex is lisse and pure of weight
$w$, by [lem-a1-reduction-lisse-pure].
For the inclusion $a:W_0\hookrightarrow\mathbf A^1$,
the open–closed triangle of [def-weil-open-closed-recollement] (at $\Qlb$ for Weil complexes,
[prop-sf-open-closed-triangle-all-stages]) and the finite-boundary
vanishing [lem-a1-finite-boundary-cohomology] give

$$
H_c^1(W,a^*\mathcal K)\twoheadrightarrow
H_c^1(\mathbf A^1,\mathcal K).
$$

It suffices to bound the source.

Apply [lem-a1-unramified-at-infinity] to the lisse sheaf
$a^*\mathcal K$ on $W_0$. After a finite constant extension it gives a
dense open $v:V_0\hookrightarrow\mathbf A^1$ and a lisse sheaf
$\mathcal E$ on $V_0$, punctually $\iota$-pure of weight $w$ and
unramified at infinity, with a Frobenius-equivariant surjection
$H_c^1(V,\mathcal E)\twoheadrightarrow H_c^1(W,a^*\mathcal K)$. It
suffices to bound $H_c^1(V,\mathcal E)$ by $w+1$.

Pass to the middle extension $v_*\mathcal E$, as in the sketch. Let
$i:Z_0\hookrightarrow\mathbf A^1$ be the finite complement of $V_0$.
The boundary sequence [prop-a1-curve-boundary-sequence] for $v$ gives
the Frobenius-equivariant exact sequence

$$
H_c^0(Z,i^*v_*\mathcal E)\longrightarrow H_c^1(V,\mathcal E)
\longrightarrow H_c^1(\mathbf A^1,v_*\mathcal E)\longrightarrow0 .
$$

The stalks of $i^*v_*\mathcal E$ have weights at most $w$ by the
boundary semicontinuity [lem-wf-boundary-semicontinuity] (with
$\beta=w$), so $H_c^0(Z,i^*v_*\mathcal E)$, and hence its image in
$H_c^1(V,\mathcal E)$, has weights at most $w$ by
[lem-a1-finite-boundary-weights] and
[lem-a1-subquotient-extension-bounds]. The right-hand group has
weights at most $w+1$ by the affine-line estimate for the middle
extension [thm-a1-line-middle-extension-upper]; this is where the
composition filtration, the exactness of the middle extension at a
fixed pure weight, and the Fourier bound of each factor enter. By
[lem-a1-extension-bounds], $H_c^1(V,\mathcal E)$ has weights at most
$w+1$.

The successive surjections preserve this bound by
[lem-a1-subquotient-extension-bounds].
Finally finite constant extensions preserve and reflect weight
bounds, as verified in [lem-a1-weight-bound-constant-extension].
This proves the degree-one assertion over the original field and
completes the proof.
