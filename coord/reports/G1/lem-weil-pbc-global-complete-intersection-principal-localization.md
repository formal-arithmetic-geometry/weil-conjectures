# Worker report: principal localization of a global complete intersection

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-global-complete-intersection-principal-localization.json`: split in four steps following Stacks Algebra 00SA, `lemma-localize-lci`.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-homeomorphism-krull-dimension.json`: exact Mathlib leaf, `IsHomeomorph.topologicalKrullDim_eq`, `Mathlib/Topology/KrullDimension.lean:53-59`.

## Attachments

None. The item's Lean audit is `none` on both branches.

## WANTED

None. Stacks `algebra.tex` and `topology.tex` were read from the shared checkout.

## Source and split

Stacks Algebra 00SA, `lemma-localize-lci` at `algebra.tex:35852-35881`, has precisely the item's global-complete-intersection localization claim in part (1). Definition 00S9, `definition-lci-field` at lines 35817-35831, supplies the zero-ring convention and the presentation with `dim T = n-c`. The paragraph after 00S9 at lines 35833-35849 supplies the dimension conclusion used by 00SA. The existing `lem-weil-pbc-global-complete-intersection-equidimensional` states that local dimension is `n-c` at every point. For nonzero `T_g`, `Spec T_g` is homeomorphic to `D(g)` by the existing principal-localization open-immersion node. An exact Mathlib homeomorphism-dimension leaf applied to each open neighborhood, then the existing open-subspace local-dimension node and dimension-supremum node, gives `dim T_g = n-c`. This expands the source's sentence "by the remarks following the definition".

For the presentation, choose `alpha : k[x_1,...,x_n] -> T` with kernel `(f_1,...,f_c)` and a lift `h` of `g`. The existing polynomial-coefficient-kernel leaf gives `ker alpha[y] = (f_1,...,f_c)`, and the existing localization-away-polynomial-quotient leaf gives `ker(T[y] -> T_g) = (gy-1)`. Lifting a coefficient polynomial shows `ker(k[x_1,...,x_n,y] -> T_g) = (f_1,...,f_c,hy-1)`. There are `n+1` variables and `c+1` equations, and their difference is `n-c = dim T_g`. The displayed `T_g` is the exact object in the statement.

The new leaf is self-contained and statement-only. Its source is Topology Definition 0055, `definition-Krull`, at `topology.tex:1392-1418`; a homeomorphism identifies the chains in clause (3). LeanSearch and Loogle returned `IsHomeomorph.topologicalKrullDim_eq`; the Mathlib source at lines 53-59 was read and gives exactly the stated equality. A DAG search for `IsHomeomorph.topologicalKrullDim_eq` found mentions but no existing node stating this theorem. There is no other new mathematical claim.

Edge cases: if `T=0` or `g` is nilpotent, then `T_g=0` and step 1 applies. If `g=1`, `D(g)=Spec T` and the added relation is `y-1`, giving the original dimension. If `g=0`, localization is zero. If `n=c=0` and `T=k`, any nonzero `g` yields a field, and the count remains zero. The nonzero case uses a point of `Spec T_g`; this exists for every nonzero commutative ring. No source error was found.

## Issues found

The source compresses the dimension preservation into a reference to remarks after Definition 00S9. The original unsplit DAG item likewise did not name the topological ingredients. The split adds those dependencies without changing the statement or the unit route.

## Unfinished

None in this item. The newly introduced Mathlib leaf needs no Stage 1 split.

## Review by G1

I read Algebra Definition 00S9 (`definition-lci-field`) and Lemma 00SA (`lemma-localize-lci`) in `algebra.tex:35817-35881`. Part (1) of 00SA is exactly this item's statement, with the same field, global complete intersection, element and principal localization. The definition's zero-ring convention justifies step 1. For a nonzero localization, 00S9 supplies a polynomial quotient of dimension n-c; step 1 obtains a lift h of g from the stated surjection. The citation to the polynomial-ring and dimension definitions matches those objects.

For step 2 I read the statements of the principal-localization open-immersion, global complete-intersection equidimensionality, local dimension under open restriction, and dimension-as-supremum nodes. The first identifies Spec(T_g) with D(g); the new homeomorphism leaf applied to each paired open neighborhood identifies its dimension, so the local dimensions at corresponding points agree. The open-restriction node identifies those with the local dimensions in Spec(T), each n-c by the equidimensionality node. The supremum node therefore gives dim(T_g)=n-c for nonempty Spec(T_g). This spells out the dimension sentence that 00SA attributes to the remarks after 00S9. In step 3, the existing coefficient-map kernel and polynomial presentation of localization state precisely the two kernels used. The displayed lift-and-subtract calculation proves that the composite kernel is (f_1,...,f_c,hy-1), rather than assuming a kernel formula for a composite. Step 4 applies the exact presentation-and-dimension clause of 00S9.

The new node is statement-only, self-contained, and cites the topological Krull dimension definition that supplies its notion. Its source is Topology 0055 (`definition-Krull`), and I read `IsHomeomorph.topologicalKrullDim_eq` at pinned `Mathlib/Topology/KrullDimension.lean:53-59`; it states exactly the claimed equality. A DAG search for that declaration and homeomorphism dimension found uses but no existing standalone node. No cross-unit tool or route change occurs. I checked g=0, g=1, nilpotent g, the zero localization, and the n=c=0 field presentation. At step 2 the nonzero ring supplies a prime, and at step 3 the chosen h maps to g, so the localization relation is the correct object. The worker required no mathematical repair; the four steps pass B–E and the DAG has no new cycle.
