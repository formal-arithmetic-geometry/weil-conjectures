+++
id = "lem-coef-finite-direct-image"
kind = "lemma"
title = "Finite coefficient change for ordinary direct image"
order = 2130
uses = ["lem-sf-comparison-tor-amplitude", "lem-sf-etale-direct-image-vanishing", "lem-sf-projection-finite-constant", "prop-weil-pbc-comparison-direct-image", "thm-sf-direct-image-tor-amplitude"]
+++
Let $f:T\to X$ be separated of finite type, and let
$K\in D^b_{ctf}(T,A)$. The canonical projection map is an
isomorphism

$$
c_{f,K}:(Rf_{*,A}K)\otimes_A^LB
\xrightarrow{\sim}Rf_{*,B}(K_B).
$$

It is natural in $K$, compatible with composition of morphisms
and successive coefficient quotients, and has the same assertion
on finite constructible pro-etale realizations.

## Proof

The bound $R^qf_*M=0$ for all etale $A$-module sheaves and
$q>2\dim T$ is [lem-sf-etale-direct-image-vanishing].
The module $B$ is finite over the Noetherian ring $A$.
Consequently [lem-sf-projection-finite-constant] applies to
this constant module and gives the asserted map as an isomorphism.
Here is the relevant truncation estimate from that proof.
Choose a resolution $P\to B$ by finite free $A$-modules in
nonpositive degrees, and set $P_t=\sigma_{\geq-t}P$.
Its error $C_t=\operatorname{Cone}(P_t\to B)$ lies in
$D^{\leq-t-1}(A)$. If $K\in D^{\leq b}$ and
$N=2\dim T$, then uniform cohomological dimension gives
$Rf_*D^{\leq r}\subseteq D^{\leq r+N}$ on bounded-above
complexes. The two error terms

$$
(Rf_*K)\otimes_A^LC_t,
\qquad Rf_*(K\otimes_A^LC_t)
$$

therefore lie in $D^{\leq b+N-t-1}$. For each fixed degree,
take $t$ large enough; the coefficient comparison for $P_t$
is an isomorphism by finite sums, shifts and cones from $A$,
and the error terms no longer affect that degree. This is an
argument in $D^-$ with a fixed cohomological-dimension bound;
finite length of the resolution of $B$ is not asserted. Both outputs are bounded
constructible of finite Tor amplitude by
[thm-sf-direct-image-tor-amplitude] and by derived scalar
extension. Direct image computed with $B$-module coefficients
has the same underlying $A$-module derived object: the usual
etale sections, acyclic resolutions, or hypercover computation of
sheaf cohomology do not change when the coefficient action is
forgotten. This identifies the projection formula with the
displayed comparison between the two coefficient categories.

The map is the projection transformation defined by tensor
adjunction and the pullback counit. In a successive quotient
$A\to B\to C$, reassociating the threefold tensor product makes
the one-step and two-step maps have the same transpose. The same
argument with the composite pullback counit proves compatibility
with composition of $f$'s. These identities hold before a
free resolution is chosen, hence also after the truncation proof.
Finally [prop-weil-pbc-comparison-direct-image] and
[lem-sf-comparison-tor-amplitude] transport the objects and
these specified maps to the finite pro-etale categories.
