+++
id = "thm-pur-finite-reduction-of-purity"
kind = "theorem"
title = "Finite reduction of purity"
order = 2022
uses = ["cor-pur-affine-space-zero-section-purity", "def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-smooth-purity-map", "def-pur-smooth-trace", "def-sbc-smooth-morphisms", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-exceptional-inverse-image", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-cbc-proetale-stalk-conservative", "lem-pur-kunneth-supported", "lem-pur-lisse-uniqueness", "lem-sf-flat-model", "lem-sf-reduction-flat-model", "thm-pur-affine-line-orientation", "thm-pur-composition-coherence", "thm-pur-diagonal-dualizing-object", "thm-pur-dnc-invariance", "thm-pur-smooth-base-change-coherence"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$m\leq n$, and write $\operatorname{red}_{n,m,T}$ for the finite
reduction functor

$$
K\mapsto K\otimes^L_{A_{E,n}}A_{E,m}:\
D^b_{ctf}(T,A_{E,n})\longrightarrow D^b_{ctf}(T,A_{E,m})
$$

on a $k$-scheme $T$. For a smooth separated $f:X\to Y$ of relative
dimension $d$ and $K\in D^b_{ctf}(Y,A_{E,n})$, the square

$$
\begin{array}{ccc}
\operatorname{red}_{n,m,X}\bigl(Lf^*K(d)[2d]\bigr)
& \xrightarrow{\ \operatorname{red}_{n,m}(\gamma_{f,K})\ }
& \operatorname{red}_{n,m,X}(Rf^!K)\\
\big\downarrow\ \sim
& & \big\downarrow\ \sim\\
Lf^*\operatorname{red}_{n,m,Y}K(d)[2d]
& \xrightarrow{\ \gamma_{f,\operatorname{red}_{n,m}K}\ }
& Rf^!_{A_{E,m}}\operatorname{red}_{n,m,Y}K
\end{array}
$$

commutes, the vertical isomorphisms being the finite-reduction
compatibilities of the six-operations package. The same is true for the
affine orientations of [thm-pur-affine-line-orientation], the smooth
traces of [def-pur-smooth-trace], the composition coherence of
[thm-pur-composition-coherence], and the base-change squares of
[thm-pur-smooth-base-change-coherence].

## Proof

Step 1: the purity map is determined fibrewise, so the comparison may be
made on the geometric fibres. The value of the smooth purity map
[def-pur-smooth-purity-map] over a geometric point $\bar y\to Y$
is prescribed by the purity of the geometric fibre $X_{\bar y}$, which
is the affine-space case [cor-pur-affine-space-zero-section-purity]
together with the rank-one computation
[thm-pur-affine-line-orientation]. Two natural transformations
between the same pair of exact functors of $K$ that agree on every
geometric fibre agree: the strict henselizations of $Y$ at its
geometric points are pro-etale over $Y$ and jointly surjective, hence
form a pro-etale covering family, and isomorphy of a morphism of
complexes of pro-etale sheaves is local for covering families, clause
(1) of [lem-cbc-proetale-stalk-conservative]; it is
therefore enough to compare the two composites of the square fibrewise,
which the compatibilities below do.
Step 2: the reduction compatibilities of the operations. All these
constructions are built from the operations of the six-operations
package, whose finite-reduction compatibilities

$$
(Lf^*K)_m\cong Lf_m^*K_m,\qquad
(Rf^!K)_m\cong Rf_m^!K_m,\qquad
(K(d))_m\cong K_m(d)
$$

are natural in $K$ and in the morphism, by
[def-weil-derived-tensor] and
[def-weil-derived-pullback-tensor-hom] (finite reduction is the derived tensor product along
$A_{E,n}\to A_{E,m}$; this ring map need not be flat, and the
finite-Tor condition is essential for boundedness). The reduction
functor does land in $D^b_{ctf}(T,A_{E,m})$ with the same Tor interval:
if $K$ has Tor amplitude in $[a,b]$ it has a bounded flat model in
degrees $[a,b]$ by [lem-sf-flat-model], and the reduction of that model
is a bounded flat model of $K_m$ in $[a,b]$ by
[lem-sf-reduction-flat-model]. Compatibility
with pullback and the invertible twist follows from associativity
of derived tensor. For the smooth exceptional inverse image use
the previously constructed tensor formula and its coefficient
compatibility, rather than flat base change. The composition
identifications are those of
[def-weil-exceptional-inverse-image] (the functoriality of
$R^!$ and of the composition isomorphisms), and by
[def-coefficient-twists-detailed] (the coefficient twists are reduced
coefficient twists). Step 3: the glueing data reduce. The sheaf
axiom gluing used in [thm-pur-dnc-invariance] is a statement
about finite locally constant rank-one sheaves, and the reduction of a
finite locally constant rank-one sheaf is again one; the local
normalizations of [thm-pur-dnc-invariance] are the reductions of
the normalizations, the lisse-uniqueness of
[lem-pur-lisse-uniqueness] reduces, and the splitting-principle
descent of one element of an abelian group used in
[thm-pur-diagonal-dualizing-object] reduces for the same reason
(the Künneth and supported-cohomology groups of
[lem-pur-kunneth-supported] are compatible with the coefficient
reduction, the boundary of the Kummer class reducing to the boundary
of the reduced Kummer class). Hence the vertical isomorphisms of the
square identify $\operatorname{red}_{n,m}(\gamma_{f,K})$ with
$\gamma_{f,\operatorname{red}_{n,m}K}$, which is the commutativity
of the displayed square. Step 4: the remaining statements. The
affine orientations of [thm-pur-affine-line-orientation] are
constructed from the Kummer boundary, whose reduction is the boundary
of the reduced Kummer class, i.e. the reduction of the orientation;
the smooth trace of [def-pur-smooth-trace] reduces because the
counit of the adjunction reduces (the adjunction itself is compatible
with the finite reduction of the coefficient ring); the composition
and base-change coherence statements are the compatible systems
obtained from Steps 1–3 applied to the constituents of the two
squares.
