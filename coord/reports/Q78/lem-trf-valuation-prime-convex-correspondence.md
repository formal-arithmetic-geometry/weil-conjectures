Files written:

- `dag/nodes/sec-trace-formula/lem-trf-valuation-prime-convex-correspondence.json`: statement split into four proof steps; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-ring-ideal-correspondence.json`: new statement-only node; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-ordered-group-prime-ideal-convex-correspondence.json`: new statement-only node; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/def-trf-totally-ordered-abelian-group.json`: Mathlib leaf for the ordered-group notion; Mathlib represents it by the `[AddCommGroup] [LinearOrder] [IsOrderedAddMonoid]` combination in the `LinearOrderedAddCommGroup` namespace.
- `citations.json`: verbatim citations for every non-elementary node use.

Attachments: none.

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, §2.1 pp. 7--8, for the item's valuation-ring/value-group and convex-subgroup correspondence. The local archive is absent; the imported node records the author's online v3 PDF as the checked source.

No statement or blueprint error was found. The imported item was unsplit and its proof fields were empty. I retained its statement and source, corrected the creation record to Q78, and supplied the missing proof route. The Mathlib search hits concern valuation-subring overrings or valuation ideals and do not state the required correspondence.

## Not duplicates

- `lem-trf-valuation-ring-ideal-correspondence` vs `lem-trf-valuation-prime-convex-correspondence`: the new node concerns ideals of a valuation ring versus positive-cone ideals of its value group; the item additionally identifies prime ideals with convex subgroups and gives the chain consequence.
- `lem-trf-ordered-group-prime-ideal-convex-correspondence` vs `lem-trf-valuation-prime-convex-correspondence`: the new node is purely an ordered-group translation for prime positive-cone ideals; the item starts with a valuation ring and composes this with the ring/value-group correspondence.
- `lem-trf-valuation-ring-ideal-correspondence` vs `lem-trf-ordered-group-prime-ideal-convex-correspondence`: one is the valuation-ring/value-group ideal correspondence (Tag 00IH), while the other is the separate ordered-group anti-isomorphism from prime positive-cone ideals to convex subgroups.
- `def-trf-totally-ordered-abelian-group` vs `def-sc-discrete-valuation-ring`: the existing node defines DVRs and mentions $\mathbf Z$ as a special value group; the new definition is the general ordered-abelian-group notion.
- `def-trf-totally-ordered-abelian-group` vs `lem-sc-dvr-nonnegative-valuation-in-ring`: the existing lemma is a membership consequence for normalized DVR valuations; the new node defines the ambient ordered-group structure.
- `def-trf-totally-ordered-abelian-group` vs `lem-sc-dvr-valuation-arithmetic`: the existing lemma proves arithmetic identities for integer-valued DVR valuations; the new node defines arbitrary totally ordered abelian groups.
- `def-trf-totally-ordered-abelian-group` vs `lem-sc-dvr-valuation-ring-characterization`: the existing lemma characterizes DVR elements and a uniformizer; the new node gives only the general ordered-group definition.
- `def-trf-totally-ordered-abelian-group` vs `def-weil-pbc-cohen-ring`: the existing node defines complete Cohen rings, a special DVR application; the new node defines no ring or completeness notion.
- `def-trf-totally-ordered-abelian-group` vs `lem-trf-ordered-group-prime-ideal-convex-correspondence`: the definition node introduces the ordered-group notion; the child proves the prime positive-cone ideal/convex-subgroup correspondence using it.
- `lem-trf-ordered-group-prime-ideal-convex-correspondence` vs `def-sc-discrete-valuation-ring`: the existing node defines discrete valuation rings and only mentions value group $\mathbf Z$ as an equivalent characterization; the new node treats arbitrary totally ordered abelian groups and proves the prime-cone/convex-subgroup anti-isomorphism.
- `lem-trf-ordered-group-prime-ideal-convex-correspondence` vs `lem-sc-dvr-nonnegative-valuation-in-ring`: the existing node is the one-way nonnegative-valuation membership criterion for a DVR; the new node is an arbitrary ordered-group correspondence.
- `lem-trf-ordered-group-prime-ideal-convex-correspondence` vs `lem-sc-dvr-valuation-arithmetic`: the existing node records arithmetic identities for a normalized integer valuation; the new node concerns prime ideals and convex subgroups for general ordered groups.
- `lem-trf-ordered-group-prime-ideal-convex-correspondence` vs `lem-sc-dvr-valuation-ring-characterization`: the existing node characterizes elements and a uniformizer in a DVR; the new node establishes the prime-positive-cone/convex-subgroup anti-isomorphism.
- `lem-trf-ordered-group-prime-ideal-convex-correspondence` vs `def-weil-pbc-cohen-ring`: the existing node defines complete Cohen rings as a special DVR with uniformizer $p$; the new node is the general ordered-group correspondence and defines no Cohen ring.

- `def-trf-totally-ordered-abelian-group` vs `def-sc-discrete-valuation-ring`: the new node defines arbitrary abelian-group laws; the existing node defines a discrete valuation ring and only specializes its value group to $\mathbf Z$.
- `def-trf-totally-ordered-abelian-group` vs `lem-sc-dvr-nonnegative-valuation-in-ring`: the new node defines the ambient abelian-group structure; the existing lemma proves a nonnegative valuation membership criterion in a DVR.
- `def-trf-totally-ordered-abelian-group` vs `lem-sc-dvr-valuation-arithmetic`: the new node defines arbitrary abelian groups; the existing lemma proves arithmetic identities for a normalized DVR valuation.
- `def-trf-totally-ordered-abelian-group` vs `lem-sc-dvr-valuation-ring-characterization`: the new node defines only abelian-group operations; the existing lemma characterizes elements of a DVR and its uniformizer.
- `def-trf-totally-ordered-abelian-group` vs `def-weil-pbc-cohen-ring`: the new node defines no ring, topology, completeness, or uniformizer; the existing node defines complete Cohen rings, a special DVR construction.

## Review by Q78

I read the imported item, its Temkin §2.1 source citation, the ancestor blueprint record, and the existing downstream use in `lem-trf-valuation-height-rank`. I checked that the hypotheses are exactly a field and a valuation ring in that field, that the quotient by units has the stated total order, and that the final chain assertion follows from an order anti-isomorphism.

For Step 1 I checked the quotient-order argument directly: the valuation-ring alternative makes every quotient comparable, units do not change membership in the ring, and multiplication descends. Step 2 cites the new valuation-ring ideal node, whose statement explicitly gives the inclusion-preserving ideal bijection and preservation of prime ideals; its source is Stacks Tag 00IH, `algebra-lemma-ideals-valuation-ring`. Step 3 cites the new ordered-group node, whose statement cites the ordered-group definition node and whose displayed formulas (I_H=\{\gamma\ge0:\gamma\notin H\}) and (H_I=\{\gamma:|\gamma|\notin I\}) are the exact data used. I checked closure of (H_I) under addition using upward closure and primality, and checked convexity by bounding an element between two subgroup elements; the inverse identities and reversed inclusion follow immediately from the formulas. Step 4 composes the two stated correspondences and preserves strict chain lengths.

I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` for the two statement nodes and the new ordered-group definition node. The returned Mathlib declarations (`ValuationSubring.primeSpectrumOrderEquiv`, `Valuation.leIdeal`, `AddGroupCone.nonneg`, and related results) do not state either node, so both remain unsplit. I checked small cases: the trivial valuation has the single prime/zero subgroup correspondence; a rank-one ordered group has the expected zero and whole-group convex subgroups; and a lexicographic rank-two group has the intermediate convex subgroup and corresponding prime-cone ideal. No cited node is a definition standing in for a theorem, and no step cites a fact absent from its node statement.



## Repair of returned points

I repaired the returned B3/C4 and B3/C8 points. The definition `def-trf-totally-ordered-abelian-group` now introduces the abelian-group structure itself and has no dependency on `def-trf-rational-rank`, which does not define group laws. I classified it as a Mathlib leaf: Mathlib represents exactly this notion by `[AddCommGroup \Gamma] [LinearOrder \Gamma] [IsOrderedAddMonoid \Gamma]`; the `LinearOrderedAddCommGroup` additive namespace is recorded at `Mathlib/Algebra/Order/Group/Defs.lean:75`. I reran and recorded the required LeanFinder, Loogle, grep, and LeanSearch queries, and changed their verdicts to record this generalization. The citation quote for the definition is now verbatim. I reread the child statement that depends on this definition and verified that its dependency now points to a Mathlib leaf with the corrected self-contained statement. The definition now cites `def-weil-preadditive-category` for the abelian-group laws; that node states the additive group structure and its laws on every Hom group, while Mathlib supplies the exact ordered-group structure.
