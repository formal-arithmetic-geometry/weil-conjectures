+++
id = "thm-fin-projective-curve-constant"
kind = "theorem"
title = "Constant coefficients on projective families of dimension at most one"
order = 1616
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-pc-projective-morphism", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-fin-finite-morphism", "lem-fin-generic-curve-model", "lem-finrepair-constant-finite-comparison", "lem-weil-pbc-constructible-subobjects-noetherian", "lem-weil-pbc-noetherian-finite-components", "lemma-weil-pbc-finite-stalk-formula", "thm-fin-projective-smooth-curve-finiteness", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $f:X\to S$ be projective
between schemes of finite type
over a field. Assume its geometric fibres have dimension at most one,
and let $\ell$ be a prime invertible on $S$.
Every higher direct image
$R^qf_*\mathbf F_\ell$ is
constructible.

## Proof

First suppose $S$ is integral. After restriction to a nonempty open,
[lem-fin-generic-curve-model] gives a finite surjection $p:S'\to S$
and a finite comparison $Y\to T=(X_{S'})_{\mathrm{red}}$, an isomorphism
away from a closed subset finite over $S'$.
Each component of $Y$ is either a smooth projective curve family
or finite etale. Its constant-coefficient higher direct images are
constructible by
[thm-fin-projective-smooth-curve-finiteness], [lem-fin-finite-morphism].
Their finite direct sum has the same property.
Apply [lem-finrepair-constant-finite-comparison] to $Y\to T$.
The equivalence for the nilpotent closed immersion
$T\hookrightarrow X_{S'}$ in
[thm-weil-pbc-universal-homeomorphism-invariance]
identifies direct images and constant coefficients, proving
constructibility for $X_{S'}\to S'$.

Put $E_q=R^qf_*\mathbf F_\ell$.
Proper base change [cor-weil-pbc-geometric-fiber-finite]
identifies $p^*E_q$ with the just computed sheaf.
Finite direct image preserves constructibility by
[lem-fin-finite-morphism], so $p_*p^*E_q$ is constructible.
The unit $E_q\to p_*p^*E_q$ is injective: on stalks it is the
diagonal into a nonempty finite product, by
[lemma-weil-pbc-finite-stalk-formula].
Consequently [lem-weil-pbc-constructible-subobjects-noetherian]
makes $E_q$ constructible on this open of $S$.
This proves the required dense-open assertion over every integral base.

For completeness, pass from it to all of $S$ as follows.
Fix $q$ and use Noetherian induction on reduced closed subsets $Z\subset S$.
Proper base change identifies $E_q|_Z$ with the direct image for
the projective family $X_Z\to Z$, whose fibres still have dimension
at most one. If $Z$ is irreducible, it is integral; the preceding
argument gives a nonempty open where $E_q|_Z$ is constructible.
Apply induction to its proper closed complement and combine the
two finite locally closed partitions.
If $Z$ is reducible, it has finitely many components $Z_i$ by
[lem-weil-pbc-noetherian-finite-components]; induction applies
to each, since it is a proper closed subset.
Restrict their partitions to
$Z_i\setminus\bigcup_{j<i}Z_j$ to make them disjoint.
This gives constructibility on $Z$ in the precise sense of
[def-weil-pbc-constructible-complexes].
Reduction of $S$ has the same etale topos by the same invariance
theorem. Thus the argument also covers a nonreduced $S$.
