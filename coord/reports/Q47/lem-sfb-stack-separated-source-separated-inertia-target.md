# Stage-1 delivery: lem-sfb-stack-separated-source-separated-inertia-target

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-separated-source-separated-inertia-target.json`: item, split into four explicit steps; original statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-inertia-separated-diagonal.json`: statement-only input, Stacks 0CL0(1), not in Mathlib.
- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-fibre-product-separated-comparison.json`: statement-only input, Stacks 050H(3), not in Mathlib.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-cancellation.json`: statement-only input, Stacks 04NX(2), not in Mathlib.
- `citations.json`: one exact statement quote for every step-node citation.

All new nodes inherit the item's chapter and unit. Their proofs and proof dependencies are empty. The assembly has 2130 characters in total; no step exceeds 2000 characters.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag, new ids, algebraic stacks, Deligne--Mumford stacks, and separation/inertia terminology. The inertia hits concern number theory or sheaves, not this assertion. No finished project declaration was found. No Lean was written or compiled.

## WANTED

None. All mathematical sources needed here are present locally.

## Corrections and provenance

The item had no proof. Its absolute separatedness hypothesis was retained; it cannot be silently replaced by separatedness over a field or over an arbitrary nonseparated S. The existing `lem-sfb-separated-source-finite-inertia-target` starts with a field base and therefore cannot establish the present absolute statement over Spec Z. It was read, but not used as an unsupported generalization.

The newest blueprint is `literature/blueprint/latest/` (main-20261023-1620). I read the current chapter and sk-thm-sf-ctf-stability unit, and the direct-images proof, especially (3). This item supports the already inherited alteration/moduli subroute to that step. No chapter or unit route is changed. `tools/blueprint_refs.py ancestor` returns `None`: the inherited creation chain terminates at `lem-sfb-admissible-direct-image`, created for a module name. The item already has `from.node: null`. I preserve it and its explicit inherited place, prepend the item to each new node's via chain, and add each actual source place. The blueprint-wide searches for inertia, diagonal, fibre product, 0CL0, 050H, and 04NX yielded no blueprint statement equal to these inputs; `same_as` remains empty.

## Source error

In the local proof of Stacks 050M(3), the sentence justifying properness of A to T says the composite was assumed “quasi-separated”. That word is a typo: the hypothesis of part (3) is **separated**, which means its diagonal is proper. Quasi-separatedness alone cannot give that inference: a nonproper quasi-compact diagonal need not be proper (for example the diagonal of the line with doubled origin over a field). Our step 3 uses the item's actual proper absolute diagonal, not the erroneous proof wording. The source statement itself and our item are correct. The final pullback along the section T to Q is also made explicit rather than treating E to Q as the desired scheme test without a further base change.

## Mathlib searches

Every new node and the item have two distinct LeanFinder phrasings, LeanSearch, Loogle, and a source grep run through the required `batch2/msearch.py` command. Exact queries and full returned results are retained in `search-*.json`; the command also recorded them in `searches.jsonl`. Every service answered. Scheme-only hits are not algebraic-space or stack theorems. In particular I read `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` including the `Scheme` variables and `IsProper.of_comp` at line 124. It proves cancellation only for schemes. Likewise the ordinary-category pullback theorem `pullback_map_diagonal_isPullback` at `Mathlib/CategoryTheory/Limits/Shapes/Diagonal.lean:309` does not state algebraicity, representability, separatedness, or a 2-pullback theorem for stacks. The new nodes are unsplit, with no claimed Mathlib matches. Existing Mathlib leaf `lem-weil-pbc-finite-proper` is reused; no duplicate scheme leaf is created.

## Review by Q47

I checked B through E of delivery-errors against the files and the following open sources. For the item I read Stacks `stacks-more-morphisms.tex`, 0DUE's final paragraph; `stacks-morphisms.tex`, 050M(3)'s full factorization argument; and 0CL0(1). For the inertia node I read 0CL0's three equivalent conditions and its proof through the neutral section; this concerns separatedness of the representable diagonal, not properness of that diagonal. For the fibre-product node I read 050H's square and part (3); its smaller content is the representable separated comparison, not separatedness of the original morphism. For algebraic-space cancellation I read `spaces-morphisms.tex`, 04NX(2) and its closed-graph proof. Its spaces need not be schemes, finitely presented or Noetherian. These are genuine auxiliary results with independent hypotheses, not clauses of the item renamed as new nodes.

Step 1 uses exactly the existing finite-proper statement, the separated clause of the properness definition, and the new inertia criterion. The finite inertia hypothesis supplies finite scheme maps on **all** scheme tests, so it legitimately proves separated inertia. The criterion's absolute clause gives a separated absolute target diagonal; it does not assume B separated. Step 2 uses precisely the representability and separatedness conclusion of the new comparison lemma, with X=Y=A, Z=B, base Spec Z. The factorization of diagonals is written on objects and is an elementary identity. Properness of its composite is a hypothesis, not an extra cancellation fact.

In step 3 the scheme test is T to P, and its map to R is explicitly the composite. E is the pullback of the **absolute** source diagonal and Q is the pullback of the comparison. The new comparison statement supplies separated Q to T. The new algebraic-space cancellation supplies proper E to Q, because its composite E to T is proper by the source hypothesis. I checked the statement of each cited node for exactly those conclusions; no proof-internal assertion is borrowed. In step 4 the existing proper-base-change node says precisely that arbitrary algebraic-space base change of a proper map is proper. Both E and Q are algebraic spaces; T is a scheme, hence an algebraic space. The section comes from the original T to P. I wrote the 2-fibre-product identification with A times over P T, including the comparison object, and agreement of the projection to T. It is a routine associativity identity, not an uncited descent or representability theorem. This yields every required scheme test of the relative diagonal.

I tested empty X and empty T (the argument is vacuous and the empty maps remain proper); identity maps (the comparison becomes an identity case); finite classifying stacks BG (finite inertia does not mean trivial stabilizers, and the criterion asserts separated diagonal only); nonseparated scheme targets (trivial inertia is allowed, and the proof never assumes their separatedness); and arbitrary non-Noetherian bases. No finite type assumption on f, local quasi-finiteness, field base, or separation of S is used. The algebraic-space properness definition includes quasi-compactness, so no hidden finite-type bound is inferred from merely local finite type. The three new statements are independently well formed on these cases.

I also read the statements of the two reused lemmas and the properness definition directly, and generated the citation quotes from their exact text with substring assertions. Off-unit finite-proper is already a Mathlib leaf. The algebraic-space proper-base-change node is a generic tool; it is in this item's unit, and its specific use is also explained in split_report. No circular dependence on any finite-inertia cover theorem is introduced. The only source correction is the proof typo described above; the item statement has not changed.

## Unfinished work

None for this one-level split. The three statement-only inputs intentionally remain future stage-1 items, as the brief requires.

## Not duplicates

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-dm-pointed-finite-groupoid-neighbourhood: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns Pointed finite-groupoid etale neighbourhoods of finite-inertia DM stacks, not the criterion or comparison asserted by the new node.

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-unramified-pseudo-torsor: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns A locally finite type pseudo torsor under an unramified group is unramified, not the criterion or comparison asserted by the new node.

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-stack-separated-source-separated-inertia-target: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns properness of the relative diagonal from an absolutely separated source and finite target inertia, assembled using this criterion.

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-smooth-atlas-automorphism-diagonal-test: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns unramifiedness of a diagonal detected on a smooth atlas (0CL0(4)), not separatedness (0CL0(1)).

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-finite-inertia-local-affine-covers: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns Stabilizer-preserving etale local finite flat affine covers, not the criterion or comparison asserted by the new node.

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-finite-inertia-pointwise-groupoid-chart: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns Pointwise finite-flat groupoid chart with one identified stabilizer, not the criterion or comparison asserted by the new node.

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-finite-inertia-etale-affine-charts: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns Finite-inertia stacks have stabilizer-preserving finite-flat affine charts, not the criterion or comparison asserted by the new node.

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-algebraic-stack-dm-point-stabilizer: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns Stabilizer criterion for membership in the DM locus, not the criterion or comparison asserted by the new node.

lem-sfb-stack-inertia-separated-diagonal vs lem-sfb-separated-source-finite-inertia-target: the new statement is the separated inertia / separated diagonal / closed neutral-section equivalence over any scheme and absolutely; the existing statement concerns cancellation of separated stack morphisms over a field; its inertia clause is over that field, not the equivalence over arbitrary scheme bases and absolute base here.

lem-sfb-stack-fibre-product-separated-comparison vs lem-sfb-stack-separation-composition: the new statement gives the representable separated comparison of two 2-fibre products; the existing statement concerns Composition preserves proper relative diagonals, not the criterion or comparison asserted by the new node.

lem-sfb-space-proper-cancellation vs lem-sfb-universal-closed-immersion-open: the new statement is properness cancellation for arbitrary algebraic spaces; the existing statement concerns The universal closed-immersion locus in the base is open, not the criterion or comparison asserted by the new node.

lem-sfb-space-proper-cancellation vs lem-sfb-closed-graph-universally-closed-diagram: the new statement is properness cancellation for arbitrary algebraic spaces; the existing statement concerns a universally closed diagram of schemes and a self-product, not properness cancellation for arbitrary algebraic spaces.
