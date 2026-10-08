+++
id = "thm-coef-integral-verdier"
kind = "theorem"
title = "Integral Verdier biduality"
order = 2146
uses = ["def-weil-derived-complete", "lem-coef-integral-hom-reduction", "lem-coef-integral-residue-tor", "lem-weil-duality-pairing", "lem-weil-finite-duality-site-comparison", "lem-weil-verdier-preservation-strata", "prop-coef-integral-dualizing", "thm-fix-general-biduality"]
+++
Set

$$
D_{X,R}K=R\mathcal Hom_R(K,\omega_{X,R}).
$$

This is an exact contravariant anti-equivalence of
$D^b_c(X,R)=D^b_{ctf}(X,R)$. Its canonical comparisons satisfy

$$
(D_{X,R}K)\otimes_R^L A_n\cong D_{X,n}K_n,
\qquad D_{X,R}K\cong R\varprojlim_n\operatorname{Res}_nD_{X,n}K_n.
$$

If $\dim X\leq d$ and the reductions of $K$ have Tor interval
$[a,b]$, those of $D_{X,R}K$ have interval
$[-b-2d,-a]$. The comparisons preserve evaluation and identify
the reduction of the actual double-dual map
$\delta_K:K\to D_{X,R}D_{X,R}K$ with $\delta_{K_n}$.
In particular $\delta_K$ is an isomorphism.

## Proof

The dualizing object and its reductions are
[prop-coef-integral-dualizing]. Apply
[lem-coef-integral-hom-reduction]; it proves both displayed
identifications and completeness of the ambient internal Hom.
By [lem-coef-integral-residue-tor], all input reductions are
finite-Tor constructible. The finite bound
[lem-weil-verdier-preservation-strata] and the comparison
[lem-weil-finite-duality-site-comparison] prove constructibility
and the uniform interval stated for every reduction of the output.
This establishes preservation in the actual integral category.

Apply the internal-Hom comparison twice. Its evaluation
compatibility identifies the reduction of $\delta_K$, defined by
the tensor–Hom evaluation as in [lem-weil-duality-pairing],
with the canonical finite double-dual map. Those maps are
isomorphisms by [thm-fix-general-biduality].
The cone of $\delta_K$ is derived complete and all its
reductions are zero. Its reconstruction in
[def-weil-derived-complete] is therefore zero.
Thus $\delta_K$ is an isomorphism. The evaluation identity
$D_{X,R}(\delta_K)\circ\delta_{D_{X,R}K}=\operatorname{id}$
shows that these natural isomorphisms exhibit the stated
anti-equivalence. The argument proves a property of ambient
internal Hom, not a replacement definition of that functor.
