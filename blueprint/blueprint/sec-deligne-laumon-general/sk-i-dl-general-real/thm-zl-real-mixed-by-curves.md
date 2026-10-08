+++
id = "thm-zl-real-mixed-by-curves"
kind = "theorem"
title = "Mixedness of real sheaves by reduction to the proved curve case"
order = 2834
lean = ["AlgebraicGeometry.WeilSheaf.IsReal.isMixed"]
uses = ["def-weil-pbc-constructible-complexes", "def-weil-punctual-weights", "def-wf-iota-real", "i-topology", "lem-a1-mixed-direct-summand", "lem-zl-curve-testing-irreducibility", "lem-zl-finite-pushforward", "lem-zl-geometric-constituents-any-base", "thm-rp-real-lisse-purity-affine"]
+++
Every constructible $\iota$-real $\Qlb$-Weil sheaf on a separated
finite-type scheme over a finite field is $\iota$-mixed, with a
finite filtration in the sense of [def-weil-punctual-weights].

## Proof

First suppose $X_0$ is smooth geometrically connected affine of
positive dimension and $\mathcal G$ is lisse in
[def-weil-pbc-constructible-complexes] and real in
[def-wf-iota-real]. We construct the finite Weil filtration
required by [def-weil-punctual-weights]. By
[lem-zl-geometric-constituents-any-base], after one finite
constant extension its Weil filtration has geometrically irreducible
quotients $\mathcal S_1,\ldots,\mathcal S_r$.
The extension preserves reality: local Frobenius becomes a positive
integral power of the old one, and powering preserves conjugation-stable
spectra. Work over this new finite field.

Fix a closed point $x_*\in X_0$. For any other closed point
$x$, apply [lem-zl-curve-testing-irreducibility] through chosen
geometric points above $x_*$ and $x$. On the resulting smooth
geometrically connected affine curve, over a further finite field,
$\mathcal G$ is real and each $\mathcal S_j$ remains geometrically,
hence arithmetically, irreducible. Pullback is exact, so it is an
irreducible constituent of the restricted real sheaf. The already
proved curve theorem [thm-rp-real-lisse-purity-affine] makes it
punctually pure there.

The weight obtained on this curve is independent of the curve.
Indeed, if its point over $x_*$ has residue degree $e$ over
$\kappa(x_*)$, its Frobenius eigenvalues are $\alpha^e$, where
$\alpha$ runs through the eigenvalues of $\mathcal S_j$ at
$x_*$; its residue cardinality is $q_{x_*}^e$. Thus curve purity
forces all those $\alpha$ to have one common modulus and fixes the
weight as

$$
w_j=2\log_{q_{x_*}}|\iota(\alpha)|.
$$

The same power calculation at $x$ proves that every eigenvalue
there has modulus $q_x^{w_j/2}$. As $x$ was arbitrary,
$\mathcal S_j$ is pure of weight $w_j$ on all of $X_0$.
The actual Weil filtration, rather than separately chosen stalk
filtrations, now proves that $\mathcal G$ is mixed.

To descend the initial constant extension $g:X'_0\to X_0$, push
this filtration forward. Finite pushforward is exact and preserves
pure weights by [lem-zl-finite-pushforward]. The diagonal unit
$\eta:\mathcal G\to g_*g^*\mathcal G$ is split as follows.
Write $d=\deg(g)$. Etale-locally the finite etale map $g$ is a
disjoint union of $d$ copies of the base, so summation on the copies
defines a map $\operatorname{Tr}:g_*g^*\mathcal G\to\mathcal G$.
Summation is unchanged by permuting the copies; hence these local maps
glue and commute with Frobenius. They satisfy
$\operatorname{Tr}\circ\eta=d\operatorname{id}$.
Since $d$ is invertible in $\Qlb$,
$d^{-1}\operatorname{Tr}$ is a Weil-equivariant retraction. Thus
[lem-a1-mixed-direct-summand] descends mixedness.

For a general constructible sheaf, pass by [i-topology] to the reduction of the
geometric scheme and form a finite chain of reduced closed subschemes

$$
X=Z_0\supset Z_1\supset\cdots\supset Z_t=\varnothing
$$

such that $U_a=Z_a\setminus Z_{a+1}$ is a disjoint union of smooth
connected affine pieces on which the sheaf is lisse. To construct a
step, take in each irreducible component of $Z_a$ a dense smooth
affine open inside the lisse locus, avoiding all the other components.
Their disjoint union is open in $Z_a$; its closed complement has
smaller dimension. Constructibility and Noetherian induction give
the finite chain. This also arranges the frontier condition needed
for successive open–closed gluing.

All these finitely many subschemes, affine pieces, and inclusions are
of finite presentation over $\overline{\mathbf F}_q$. Their
defining equations therefore descend to one finite constant-field
extension. Choose that extension large enough to define each
geometric component individually. Its Frobenius is a power of the
original Frobenius and preserves every piece, so restriction of the
original Weil structure supplies the required Weil structures there.
The pieces are geometrically connected over this field. The preceding
argument applies to those of positive dimension; in dimension zero a
Jordan filtration of each invertible Frobenius operator gives pure
factors of weights $2\log_{q_x}|\iota(\alpha)|$. On a finite disjoint
union, extend the filtrations of its components by zero and concatenate
them; this gives a mixed filtration even if their weights differ.

Mixed filtrations glue across a closed complement: for an open
$j:U_0\hookrightarrow X_0$ and closed complement $i:Z_0\hookrightarrow X_0$, use the exact sequence

$$
0\longrightarrow j_!j^*\mathcal G\longrightarrow\mathcal G
\longrightarrow i_*i^*\mathcal G\longrightarrow0.
$$

Both $j_!$ and $i_*$ are exact and preserve purity of a sheaf
already pure on its support, since their other stalks are zero.
Splice the resulting finite filtrations using inverse images under
the quotient map. Apply this to each pair
$U_a\subset Z_a$, with closed complement $Z_{a+1}$, starting
at the last nonempty member of the chain. All inclusions are defined
over the chosen finite field, so every extension and inverse image is
Weil-equivariant. The finite induction gives a global finite Weil
filtration. Finally descend the common constant extension as above.
