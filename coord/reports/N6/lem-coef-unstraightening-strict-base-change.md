# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-unstraightening-strict-base-change.json`: six proof steps, with a correction specifying the normalized representative in which equality holds. No new nodes and no Mathlib leaves.
- `citations.json`: statement excerpts for each node used in each step.

## Attachments

None. Searching the entire read-only `WeilConjectures/` source for the item's tag and for `unstraighten`, `straightening`, and `conePresheaf` found no declaration stating this construction. Upstream sorry declarations are not treated as finished proofs.

## WANTED

WANTED: Lurie, *Higher Topos Theory*, §2.2.1 and Proposition 2.2.1.1 (printed pp.73–74), Remark 2.2.2.12 (p.78), and Proposition 2.2.3.11 (pp.83–85), for the archival literature collection. I read these places through the author's online PDF, https://people.math.harvard.edu/~lurie/papers/HTT.pdf . The sandbox has no saved HTT PDF or text; the inherited source note claiming such copies was inaccurate and has been corrected. The proof remains agent-written: it expands the source comparisons in specific coordinates.

## Statement corrected

STATEMENT-DISPUTED: Passing a raw simplicial set over a base to its presheaf of simplex fibers alone does not turn the base-change isomorphism for raw natural-transformation sets into literal equality. For example, take S to be two discrete vertices, T one of them, and F the terminal diagram. The raw transformations L_S(Delta^0)->F have components indexed by both vertices of S, whereas L_T(Delta^0)->u*F has components indexed by the one vertex of T. Each transformation set is a singleton, but its elements have different function domains. Presheaf reindexing retains these raw elements; it does not replace them by equal functions. HTT Proposition 2.2.1.1 states natural isomorphisms, not this raw equality.

I preserved the intended strict comparison by specifying normalized cone-label coordinates: a simplex is a family of maps from the last-vertex cone mapping spaces of C[Delta^(n+1)] into F(sigma i), with the action equations written explicitly. Step 1 gives the canonical isomorphism from the raw coordinates to these coordinates; strict equality, including all enriched and base-composite clauses, is asserted for these specified representatives. Raw coordinates retain the corresponding canonical isomorphism. No base, fibrancy or size hypothesis is added, and no preservation or coherence clause is dropped.

## Not duplicates

No new node is proposed. `lem-coef-simplicial-right-fibration-presentation` has a broader classification theorem and a natural base-change isomorphism. It also depends through homotopy descent on this item, so it cannot prove this item. The existing external-products and target-change nodes likewise lead back to this item through the unmarked straightening theorem; I checked those dependency paths and avoided the cycles. The existing `lem-coef-cone-boundary-projective-cells` supplies the old-object and cone-object mapping sets needed for the direct mapping-out calculation. Whole-DAG keyword searches and `blueprint_refs.py search unstraightening` found no independent blueprint duplicate.

## What was wrong and what remains

The saved four-step proof called different raw cone-label sets equal without constructing common coordinates. It also asserted the constant-parameter factor without deriving it, omitted a step-3 pinched-cube citation from citations.json, and attributed the detailed cone calculation to blueprint paragraph 2. I repaired all four. That blueprint paragraph contains a derived coefficient-adjunction calculation, not this foundational cone argument; it is ancestry only. No source error in HTT is alleged.

The inherited Mathlib search records and all existing logged searches are retained. The new normalized-coordinate searches were run through msearch.py; their returned StrictSegal, ordinary sheaf-cone, and Cech-nerve statements have different objects and do not state this construction. No new node is being introduced. No unfinished mathematical clause remains in this split; the underlying cited nodes retain their independent stage-1 tasks.

## Review by N6

I read HTT §2.2.1, Proposition 2.2.1.1, Remark 2.2.2.12, and the restriction comparisons of Proposition 2.2.3.11. I also read the current chapter and unit records and blueprint ancestor paragraph 2: the item is an extracted coherent-diagram foundation for the derived coefficient-adjunction calculation, rather than a new geometric route. There are no new nodes requiring separate source checks.

For Step 1 I opened the statements of `lem-coef-cone-presheaf-adjunction` and `lem-coef-cone-boundary-projective-cells`. The first states the precise cone pushout and the raw natural-transformation simplices. The second states that its old full subcategory is A, reverse mapping sets are empty, and the cone endomorphism set is the point. Those facts make a transformation exactly a functor to the explicitly constructed collage. The pushout universal property then says that its free components are precisely the normalized cone labels. The inverse functions and compatibility with operators are described, rather than assumed as a base-change theorem.

Step 2 uses `lem-coef-pinched-cube-latching` for realization and the action of monotone maps. After the Step 1 coordinate choice, both sides have the same domains B_n(i,v), codomains F(u tau i), and action equations. This is an equality of formulas; it does not invoke right-fibration classification.

Step 3 uses that same node's definitions of J^n and Q^n, and the cone-boundary node's old/cone mapping sets. I wrote the mapping-out argument showing that realization preserves the particular pushout; collapsing the old face then gives exactly a map Q^n->K. Step 4 uses the cone-presheaf node's definition of enriched natural maps and the pinched-cube node's natural Q^n->Delta^n maps. Pairing and projection prove the product formula, and the displayed expression c(a(b,k q_n),h q_n) checks composition. This repairs the saved assertion of the product formula without relying on the cyclic external-products node.

Step 5 cites the pinched-cube functoriality and the degreewise product/pullback convention of `def-cbc-enhanced-diagrams-cones`. It checks both diagram restriction and parameterized slice maps by precomposition, including identity and successive base maps. Step 6 uses the cone-presheaf node's characterization of projective fibrancy as Kan values, the right-horn lifting condition in `def-coef-infinity-fibrations`, and degreewise pullbacks in the enhanced-diagram definition. The actual filler is paired with the prescribed T-simplex, and the fiber projection is explicitly identified. No general preservation of arbitrary weak equivalences by arbitrary pullback is asserted: only the stated vertex-fiber equivalences are used.

I checked the empty base (all label presheaves empty), the base Delta^0 (labels reduce to maps Q^n->F(s)), n=0 (Q^0 is the point), identity maps, and composites. Empty values F(s) cause no exception: there may simply be no labels. All objects are small in the stated enlarged universes; no colimit indexed by a non-small category is used. No Kan condition is used until the projective-fibrancy preservation clause. I checked every citation against its current statement, regenerated the literal quotation file, and checked that no proof step exceeds 2000 characters. The six steps consist of mapping-out, coordinate, product, precomposition, and filler calculations; no new lemma or copy of an item clause has been hidden in a new node.

## Final continuation review by N6

I retained the previous split, report, citations and search log, compared the item against the current shared unsplit node, and started with the required dry run. It completed successfully at b9e668db58. A fresh read of the current five cited statements confirms the assumptions used: the cone-boundary lemma applies with A=C[S] and a the identity in Step 1, and with S=Delta^0 in Step 3. I reread the author's online HTT construction on printed pp.73–74, Remark 2.2.2.12 on p.78, and the restriction diagram on pp.84–85; the current main-20261015 ancestor proof still supplies the derived coefficient-adjunction ancestry, rather than an inline proof of this foundational comparison. A renewed whole-project declaration search returned no matches for the item tag or unstraightening keywords, and the blueprint search returned no duplicate. No new statement or node requires new Mathlib searches; the saved searches and their actual recorded results were retained.

I corrected the Step 3 conclusion to retain the base factor: constant-diagram labels over each fixed simplex are Hom(Q^n,K), while the total slice object is S times Sing_Q(K). For a discrete two-point base and K=Delta^0 the total object has two vertices, confirming why the omitted factor would be wrong. In Step 4 I wrote the maps from each cone mapping space to Q^n and the formula for each component of successive parameterized maps. This checks the parameter domains and the composition equality directly. The correction changes no assertion of the item's statement or dependency list beyond the normalized-representative correction already documented above.

I checked delivery-errors B through E against the saved artifacts: no new nodes, elementary restatements, or clause nodes were introduced; every cited statement supplies the precise fact taken from it; the cone and parameter calculations use explicit universal properties and component formulas; the horn filler uses exactly the right-horn hypotheses; no classification theorem, slice model structure, or quasicategory hypothesis is used. All six proof steps remain below 2000 characters. The constant-factor and normalized-label comparisons are direct mapping-out expansions of the cited pushout definitions, and the enriched identities are the displayed component calculation, rather than an appeal to an uncited standard lemma.
