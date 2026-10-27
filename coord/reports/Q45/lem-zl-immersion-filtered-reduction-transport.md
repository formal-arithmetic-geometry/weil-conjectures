## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-immersion-filtered-reduction-transport.json`: statement, now split in seven steps; not a Mathlib leaf. The statement and its statement dependencies are unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement quotations for every citation in the item's steps.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and immersion/filtration concepts, and read `DeligneLaumon/Reduction/FormalSteps.lean` (open and finite upper-weight theorems), `WeilSheaf/ClosedLowerStar.lean`, and the relevant reduction/weight search results. These give native Weil-sheaf/derived-category results or only upper-bound clauses, not every clause of this common-stage fixed-pair-heart statement with a specified filtration and actual adjunction unit. They are not exact attachments.

## WANTED

None.

## Corrections and scope

The imported item had no proof. Its statement is correct, including arbitrary surjective closed immersions, nonreduced bases, zero quotients, and unrelated initial open and closed immersions. I retained it verbatim. I did not use `i-topology` as a common-stage rational Weil equivalence: its statement has finite coefficients and would not support that application. Likewise, the finite-direct-image definition alone does not prove its t-exactness. Instead I reused the existing finite-adic-direct-image theorem and the all-stage localization triangle.

The source read for the item was the latest blueprint `sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, especially “For a general constructible sheaf, pass … to the reduction” and the final exact-extension and filtration-splicing paragraph. I also read the unit and chapter records and the three-level route restriction. This split isolates precisely the source's immersion and reduction argument; it does not alter its curve-testing or Noetherian-induction route. The statement's source metadata is retained; proof step sources point at `literature/blueprint/latest/`.

For the underlying source facts I read Stacks `etale-cohomology.tex`, Tag 03QP, `proposition-finite-higher-direct-image-zero`, including its geometric-point restriction formula and proof; `proetale.tex`, Tags 09AA (`lemma-closed-immersion`), 09AB (`lemma-thickening`) and 09AH (`lemma-ses-associated-to-open`), including the canonical unit/counit construction. The rational/common-stage upgrades are used only through DAG nodes that explicitly state them, not silently attributed to these finite/set-coefficient Stacks results. No SGA source was used.

## Searches and reuse

I searched the whole DAG and used `tools/blueprint_refs.py search` for `extension by zero`, `surjective closed immersion`, `topological invariance`, and `filtration`, and `ancestor` for the item. I read the relevant existing statements, including the finite-coefficient invariance nodes, open extension, immersion local behavior, finite adic direct image, fixed-pair heart exactness, and filtration-splicing nodes. The generic finite adic theorem is stronger than the closed-image stalk input needed here; the open-extension punctual theorem already supplies the open input. A new node for either would duplicate existing work. A separate node for transport along an isomorphism would be elementary. No node was created.

Five searches were actually run with `batch2/msearch.py` under Q45 and this item: two differently phrased LeanFinder searches, Loogle, a source grep, and LeanSearch. Their exact queries, hits, timestamps and digests are in `searches.jsonl`; summaries were appended to the item's prior search records without deleting them. Loogle found abstract short-exact functor theorems, and LeanSearch found abstract adjunction-unit isomorphism theorems. These do not prove the geometric common-stage Weil assertions. I reused the DAG's existing abstract exact-functor Mathlib leaf for the quotient operation. No search was invented and no unavailable answer was interpreted as absence.

## Review by Q45

I checked B–E of `coord/delivery-errors.md`, including their duplicate merged copy, against the actual statements and the sources above. There are no new statement-only nodes needing separate source or definition checks. The item's objects and common-stage coefficients remain those explicitly given in its statement. All seven steps are shorter than 2000 characters.

Step 1 uses `lem-zl-extension-by-zero-punctual`, whose statement explicitly supplies exactness on constructible common-stage Weil hearts and purity at every real weight. Its hypotheses are an open immersion of separated finite-type schemes over the fixed finite field; all are present. Its actual compact-support functor is the same functor as the item's. No complement relation with the given closed immersion is used.

Step 2 uses `lem-weil-pbc-closed-immersion-finite` to meet the finite-morphism hypothesis of `lem-zl-finite-adic-direct-image`. The latter states actual rational/common-stage t-exactness, constructible-heart exactness, and a natural stalk formula. `lem-sf-open-closed-weil-mate-structures` supplies the normalized induced closed Weil structure, using the closed immersion's own complement, which is defined over the finite field. `lem-a1-constructible-pullback-t-exact` applies to Frobenius and its inverse. `lem-zl-texact-fixed-pair-heart-cohomology` supplies exactness and abelianness of the fixed-pair heart, with kernels and cokernels created by forgetting. I checked that this is a category of pairs in the common-stage derived category, and did not replace it with the native derived category of Weil sheaves. The shift-compatible exchanges here are those induced by the actual derived operations.

Step 3 uses the finite-adic theorem's restriction-map formula and its stated naturality both in sheaf morphisms and semilinear diagram isomorphisms. The geometric fibre of a closed immersion is empty or has one point, even for a nonreduced closed subscheme; a point into a quotient ring lifts uniquely when its ideal vanishes. `lem-zl-immersion-weil-local-behavior` explicitly supplies closedness of the corresponding closed point and equality of residue fields. The local-operator definition and `lem-weil-frobenius-point-transport-natural` identify the iterated structure and transport factors, producing the displayed intertwining equation. Thus the assigned weight is unchanged rather than rescaled. The final purity conclusion uses exactly the eigenvalue definition of `def-weil-punctual-weights`.

Step 4 applies clause (a) of the existing Mathlib leaf `lem-sp-exact-functor-preserves-homology` to the abelian Weil hearts established in Steps 1–2. Its statement gives nested subobjects and precisely the quotient comparison required here, compatible with the projections. Hence the comparison is already Weil-equivariant, rather than an unrelated isomorphism of underlying sheaves. The definition of punctual weights allows weak inclusions and supplies the filtration criterion; the proof retains the actual assigned labels and all their upper bounds.

Step 5 uses the canonical, Weil-equivariant second arrow of `prop-sf-open-closed-triangle-all-stages`, not an arbitrary equivalence. This theorem applies to the surjective closed immersion with empty open complement at the common-stage coefficient field. `lem-per-adic-heart-pullback-fibres` gives joint conservativity to justify vanishing on the empty scheme; exact restriction is supplied by immersion local behavior. Clause (5) of `lem-weil-heart-short-exact-triangles` is applied only in the underlying triangulated coefficient category. It makes the unit an isomorphism in the ordinary heart. The explicit inverse equation then makes it a Weil isomorphism. I did not assume the Weil-pair category is triangulated.

Step 6 is elementary assembly from Steps 3–5: the pullback along an isomorphism has the stated representative, these representatives commute with the inclusions, and their cokernels identify by the cokernel universal property. This writes out what “transport the filtration” means, including the quotient map. The eigenvector argument explicitly explains invariance of weights under these Weil isomorphisms. Step 7 cites the actual statement of `lem-weil-pbc-reduction-universal-homeomorphism`, which says the reduction map is a surjective closed immersion, so Steps 5–6 apply without any reduction hypothesis on the base.

For C4 I opened every cited node and put its full verbatim statement in `citations.json`, retaining all relevant hypotheses and clauses. For C1 all geometric/adic comparisons are explicit node citations; elementary inverse-isomorphism and cokernel arguments are written out. Off-unit generic coefficient tools are declared in `split_report.tool_uses` with their purpose, not written into maintainer-owned `tool_uses`. Neither `i-topology` nor a finite-torsion statement is used as an unstated rational comparison.

Edge cases checked: empty source and/or target, identity immersion, support disjoint from the closed subscheme, a thickened point and its reduction, the zero sheaf, filtration length zero, repeated terms and zero quotients, and arbitrary real assigned weights with any common upper bound. In particular a zero stalk contributes no eigenvalues, not a zero eigenvalue. A surjective closed immersion need not identify structure sheaves, but the actual coefficient adjunction unit is what the empty-complement triangle identifies. No hypothesis of reality, reducedness, strict filtration, complementarity of the initially specified pair, or geometric connectedness was introduced.

## Unfinished work

No mathematical subclaim is left unaccounted for. Delivery checks and the final push are performed by the required unmodified launcher tools.
