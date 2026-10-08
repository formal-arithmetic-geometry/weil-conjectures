+++
id = "lem-weil-geometric-generic-exchange"
kind = "lemma"
title = "Geometric generic restriction and the boundary operations"
order = 2126
uses = ["def-weil-open-closed-recollement", "def-weil-site-perfect-complex", "lem-exc-closed-amplitude", "lem-exc-closed-support-triangle", "lem-weil-bounded-finite-tor-perfect", "lem-weil-pbc-derived-cohomology-continuity", "lem-weil-stratum-ambient-hom", "sbc-thm-bounded-below-derived-smooth-base-change", "thm-dg-finite-type-constructibility", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $B$ be a smooth integral curve over $k$, let
$\bar\eta=\operatorname{Spec}\overline{k(B)}$, and let $g$
denote geometric generic pullback on a finite-type $B$-scheme.
For a separated finite-type $B$-morphism $h:T\to X$, a closed
immersion $i:Z\hookrightarrow X$, and bounded constructible
complexes in the expressions below, the natural comparisons are
isomorphisms:

$$
g_X^*Rh_*L\cong Rh_{\bar\eta,*}g_T^*L,
\qquad
g_Z^*Ri^!M\cong Ri_{\bar\eta}^!g_X^*M.
$$

For $K\in D^b_{ctf}(X_{\Et},A)$ and
$M\in D^b_c(X_{\Et},A)$, one also has

$$
g_X^*R\mathcal Hom_A(K,M)
\cong R\mathcal Hom_A(g_X^*K,g_X^*M).
$$

The comparisons preserve evaluation and tensor adjunction.

## Proof

First replace $\overline{k(B)}$ by a separable closure of $k(B)$.
It is the inverse limit of nonempty opens in the normalizations of
$B$ in finite separable extensions of its function field, after
removing their branch loci. These are etale over opens of $B$;
one may choose affine opens, so all transition maps are affine.
At every such stage the first comparison is smooth base change,
[sbc-thm-bounded-below-derived-smooth-base-change].
Every affine etale test object over the generic fibre descends to a
stage. On it, [lem-weil-pbc-derived-cohomology-continuity]
identifies the filtered colimit of the stagewise cohomology groups
with the cohomology on the generic fibre. Exactness of filtered
colimits thus passes the canonical comparison to the limit in each
degree. Passing from the separable closure to the algebraic closure
is a purely inseparable extension; its base changes are universal
homeomorphisms and induce equivalences of etale topoi by
[thm-weil-pbc-universal-homeomorphism-invariance]. This proves
the first assertion, with no properness assumption on $h$.

Let $j$ be the open complement of $i$. Pull back the triangle

$$
i_*Ri^!M\longrightarrow M\longrightarrow Rj_*j^*M\longrightarrow
$$

of [lem-exc-closed-support-triangle]. Inverse image is exact,
commutes with closed direct image by its stalkwise description, and
commutes with $Rj_*$ by the first assertion. The resulting triangle
is the corresponding closed-support triangle on the generic fibre.
The full faithfulness of $i_{\bar\eta,*}$ gives the second comparison.
Only the closed-support formula is used here, not boundary duality.

For the internal-Hom comparison, use the finite smooth stratification
and the site-perfect restrictions of $K$ from the argument of
[lem-weil-bounded-finite-tor-perfect] and the definitions in
[def-weil-site-perfect-complex]. The open–closed triangles
[def-weil-open-closed-recollement] reduce the assertion to
$K=Rs_!P$, for a locally closed immersion $s:S\hookrightarrow X$
and site-perfect $P$. The ambient identity

$$
R\mathcal Hom_X(Rs_!P,M)
\cong Rs_*R\mathcal Hom_S(P,Rs^!M)
$$

is [lem-weil-stratum-ambient-hom]. Factor $s$ into an open
and a closed immersion. Its exceptional inverse image is a composite
of ordinary open restriction and the closed-support functor just
treated. Hence it commutes with $g^*$. Internal Hom from $P$
is $P^\vee\otimes^L-$, which commutes with inverse image, and
$Rs_*$ commutes with $g^*$ by the first assertion. This proves
the comparison on each generator and therefore on $K$.
All intermediate complexes are bounded constructible: this follows
for $Rj_*$ from [thm-dg-finite-type-constructibility], for
closed $Ri^!$ from the same closed-support triangle or
[lem-exc-closed-amplitude], and for internal Hom from $P$
from its bounded finite-projective model. Thus each preceding
bounded-below comparison is applied in its proved domain.
All maps are the maps obtained by tensor adjunction from evaluation;
the smooth, limit, and closed-support comparisons used above are
natural in those maps. Thus these are the specified canonical
comparisons, compatible with evaluation, rather than merely
isomorphisms between the underlying objects.
