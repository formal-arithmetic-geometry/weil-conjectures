+++
id = "lem-amb-cartier-kummer-map"
kind = "lemma"
title = "A Cartier divisor gives a supported Kummer map"
order = 1569
uses = ["def-coefficient-twists-detailed", "def-sc-effective-cartier-divisor", "def-sc-kummer-sequence", "def-weil-pbc-derived-categories", "lem-amb-closed-support-hom", "lem-amb-kummer-any-base"]
+++
Let $i:D\hookrightarrow T$ be an effective Cartier divisor.
There is a natural morphism in the ordinary derived category

$$
c_D:i_*A_D\longrightarrow A_T(1)[2].
$$

Its image after forgetting support is
$c_1(\mathcal O_T(D))$. For any base change under which
the pullback divisor remains Cartier, the map pulls back to
the corresponding map for that divisor.
The notation refers to Kummer connecting maps, and Tate twists.

## Proof

First take coefficients $\mathbf Z/n$. Write
$v:T-D\hookrightarrow T$. The line bundle
$\mathcal O_T(D)$, together with its canonical trivialization
on $T-D$, defines an element of

$$
H^1\bigl(\operatorname{Cone}(R\Gamma(T,\mathbf G_m)
\longrightarrow R\Gamma(T-D,\mathbf G_m))[-1]\bigr).
$$

For completeness, choose local equations $f_a$ of $D$.
The transition units $f_a/f_b$ define the line bundle,
and the invertible functions $f_a$ on the complement give
its specified trivialization. The equality
$(f_a/f_b)(f_b/f_c)=f_a/f_c$ is the cocycle equation,
and restriction of the transition units is the coboundary of
these trivializing functions. These two assertions are exactly
the cocycle equation in the displayed relative cone. Replacing
$f_a$ by a unit times $f_a$ changes that cocycle by a
coboundary. Refining the covering preserves its class. One may
compute the cone on an injective resolution, or on etale
hypercovers refining this covering; the description gives the
same class in either computation.

Apply the connecting map of the Kummer sequence
[lem-amb-kummer-any-base] to this relative class. It gives
$c_D\in H_D^2(T,\mu_n)$. Forgetting the relative
trivialization sends it to the Kummer boundary of the line
bundle, namely its first Chern class. The support triangle in
[lem-amb-closed-support-hom] identifies

$$
H_D^2(T,\mu_n)
=\operatorname{Hom}_{D(T,\mathbf Z/n)}
(i_*\mathbf Z/n,\mu_n[2]).
$$

This identification uses the sheaf-level adjunction between
$i_*$ and sections supported on $D$, derived by
injective resolutions; it does not assert a purity isomorphism.
All the cone maps and Kummer boundaries commute with pullback
of the pair and its trivialized line bundle. This proves the
asserted base-change compatibility whenever the pulled-back
pair is again the Cartier pair of
[def-sc-effective-cartier-divisor].
Finally apply derived scalar extension from $\mathbf Z/n$
to $A$. Its source is $i_*A_D$, as seen on stalks,
and its target is $A_T(1)[2]$ by
[def-coefficient-twists-detailed]. No flatness of $A$ over
$\mathbf Z/n$ is needed.
