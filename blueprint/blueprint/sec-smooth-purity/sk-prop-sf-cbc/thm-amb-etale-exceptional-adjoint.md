+++
id = "thm-amb-etale-exceptional-adjoint"
kind = "theorem"
title = "The ordinary ambient exceptional adjoint"
order = 1565
uses = ["def-amb-etale-compact-support", "def-weil-compactifications-refinements", "def-weil-pbc-derived-categories", "lem-amb-etale-compact-comparisons", "lem-amb-proper-coproducts"]
+++
Let $f:X\to S$ admit a compactification
$X\xrightarrow{j}\overline X\xrightarrow{r}S$ between
Noetherian schemes, with $j$ open and $r$ proper of finite
type. The ambient functor $Rf_!=Rr_*j_!$ on ordinary derived
categories of etale $A$-module sheaves has a right adjoint,
denoted $f^\times$. No restriction to a constructible
subcategory is made in this assertion.
The notation refers to ordinary derived categories, and ordinary etale compact supports.

## Proof

The extension by zero in [def-amb-etale-compact-support]
is exact and commutes with coproducts, as is checked at geometric
stalks. The fibre dimensions of the fixed finite-type proper
morphism $r$ have a finite bound, so
[lem-amb-proper-coproducts] makes $Rf_!$ an
exact coproduct-preserving functor. Apply the ordinary
Brown representability theorem for the derived category of a
Grothendieck abelian category: an exact functor out of such a
derived category which preserves coproducts has a right adjoint.
Here the abelian category consists of sheaves of $A$-modules;
it is Grothendieck since filtered colimits are exact and the free
module sheaves on a small set of site objects form a generating
set. The precise homological-algebra input is
[Stacks Project,
Proposition 19.15.2, Tag 0F5Y](https://stacks.math.columbia.edu/tag/0F5Y) (Section 19.15, Brown representability
and Grothendieck abelian categories), about ordinary triangulated
categories.

Representability is applied to the functor
$M\mapsto\operatorname{Hom}(Rf_!M,K)$, for each $K$.
Yoneda makes the representing objects functorial in $K$,
and the identity of a representing object gives the counit.
The representing bijection then gives the unit, and the two
triangle identities follow by applying that bijection to an
identity map. Finally the coherent comparisons of the left
functors in [lem-amb-etale-compact-comparisons] give the
corresponding unique comparisons of right adjoints. Thus this
construction makes no additional assumption about $f^\times K$.
