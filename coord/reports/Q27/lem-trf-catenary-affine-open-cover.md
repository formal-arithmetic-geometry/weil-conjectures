# Stage-1 delivery: lem-trf-catenary-affine-open-cover

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-catenary-affine-open-cover.json`: item, statement unchanged, now split into five elementary deductions from two existing Mathlib correspondence leaves and the definitions. No Mathlib match for the item.
- `citations.json`: twelve entries, one verbatim statement quotation for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log; `write_split.py` is sandbox-only preparation material.

New DAG nodes: 0. New Mathlib leaves: 0. No unit or chapter record changed.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item tag/name and for `catenary` (case-insensitive as well): no project declaration. The read-only upstream master likewise supplies no catenary declaration. No compiler, Lake or build command was run.

## WANTED

None. All sources needed for the split are present locally.

## Corrections and findings

The statement is correct as written, including for schemes not locally Noetherian. The item had no proof; its existing statement dependencies and blueprint ancestry are retained. I read the unit `sk-i-curve-zero`, its chapter, and the current main-20261015 ancestor text. This is a generic commutative-algebra/topology support result in the historically recorded excellence-locality chain, not a replacement for any step of that unit. No SGA source is used.

Stacks properties.tex Tag 02IX (`lemma-catenary-local`), implication (4) to (3), cites topology.tex Tag 02I2 (`lemma-catenary`) and algebra.tex Tag 02IH (`lemma-catenary`). I read all three. The topology proof omits the details, so merely citing it would not be a split. The delivery instead writes out the interval argument using existing nodes. I also read topology.tex Tag 0B7I (`lemma-dimension-supremum-local-dimensions`) and algebra.tex Tag 00ES (`lemma-irreducible`), the sources of the reused correspondences, and algebra.tex Tag 00NI (`definition-catenary`) to check both finite boundedness and equal saturated-chain lengths.

In particular, `V intersect U_i` need not be affine, and the proof never asserts that it is. The correspondence is used on this open subspace twice. Bounds are imposed on individual prime intervals, not on the dimension of the whole scheme. No Noetherian, quasi-separated, finite-cover, or finite-dimensional hypothesis is introduced. There is no statement dispute.

## Unfinished work

None within this stage-1 item. The two substantive correspondences are existing Mathlib leaves, so this split creates no lower items.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Searches of the whole DAG for catenar/02IX/02I2/02IH and of the imported blueprint using `blueprint_refs.py search` for catenary, catenarity, saturated chains, irreducible closed subsets, open covering and irreducible found no second statement of this item. Broader searches for irreducible closed sets in open subspaces found the existing node `lem-weil-pbc-open-subspace-irreducible-closed-correspondence`, which was reused. Likewise `lem-weil-pbc-spec-irreducible-closed-subsets-primes` was reused. The parent `lem-trf-universally-catenary-affine-cover` has a stronger, different ring property and depends on this item; it is not cited backwards.

## Mathlib search assessment

All new recorded queries were actually run through `msearch.py Q27 lem-trf-catenary-affine-open-cover`; their exact query strings and returned log records are in the node and `searches.jsonl`. Inherited searches are retained. Two phrasings for the item and two for the topological condition were considered before concluding no direct match. LeanFinder and LeanSearch returned Noetherianity, sobriety, Jacobson-space locality and Krull-dimension results. None asserts equality of saturated-chain lengths. Loogle's valid quoted-name query `"catenar"` and the whole-Mathlib grep `catenar` both returned zero hits. The inherited Loogle unknown-identifier result remains explicitly unavailable.

The broader irreducible-closed-set search led back to the two existing leaves. I opened `Mathlib/Topology/Sets/Closeds.lean:478` and `:515` to read `IrreducibleCloseds.map` and `orderIsoOfIsOpenEmbedding`, including the closure-image and preimage maps, and `Mathlib/RingTheory/Spectrum/Prime/Topology.lean:971` to read `PrimeSpectrum.pointsEquivIrreducibleCloseds`. These confirm the stored leaf interfaces. Neither leaf needs a new record or an attachment here.

## Review by Q27

I checked the five steps against the statements of every node they cite, rather than relying on their proofs. The relevant definitions are `def-pc-scheme` (including its current blueprint_update), `def-weil-affine-spectrum`, and the explicit chain clause of `def-exc-excellent-ring`. I read the entire statements of both correspondence nodes and generated the citation quotations from those exact statements.

Step 1 uses precisely the definition of affine as isomorphic to a spectrum and the spectrum definition's global-sections ring and functoriality. Applying global sections to an isomorphism and then Spec identifies an affine T with Spec of its actual section ring. Transport through a homeomorphism preserves closed subsets, their irreducibility and inclusion directly from the definitions. No separate reconstruction lemma is hidden here.

Step 2 uses clauses (1) and (2) of `lem-weil-pbc-spec-irreducible-closed-subsets-primes`: they give every irreducible closed subset, uniqueness of its prime, and reversal of inclusion. Restricting this bijection to an interval and reversing a finite chain are elementary. I explicitly checked that insertion of a member on one side corresponds to insertion on the other, so saturation and length both transfer; the catenary definition supplies the exact chain conditions.

Step 3 applies `lem-weil-pbc-open-subspace-irreducible-closed-correspondence` to the open W in V. Its hypothesis is only openness with the subspace topology. The point corresponding to q is in the smallest set Z and in W, so every member of the entire interval meets W. The cited statement gives intersection, inverse closure and preservation/reflection of inclusion, which prove surjectivity on the interval, not just preservation of an individual chain. The spectrum correspondence provides the required nonempty irreducible endpoints. The scheme definition supplies the open-subscheme topology.

Step 4 applies that same open-subspace correspondence with ambient space U_i. It gives irreducible closed endpoint closures C and C', their exact intersections with W, and the inverse inclusion-preserving map. Every intermediate set in U_i contains C and thus meets W. This checks the domain restriction in the cited node and establishes a bijection of the whole intervals; it does not assume that closed sets of V were already closed in U_i or S.

Step 5 uses the actual catenarity hypothesis on the chart ring, the prime correspondence from Step 2, and the two complete interval bijections of Steps 3 and 4. I checked explicitly that they preserve both chain lengths and insertability of intermediate members. A largest attainable length exists because the lengths are a nonempty bounded set of natural numbers; it supplies a saturated chain without an unproved maximal-chain existence claim. Thus the conclusion is exactly catenarity of B for every prime pair. This is an elementary transfer from the cited interfaces, not a new catenary-locality theorem assumed as a black box.

For small cases I checked: equal endpoint primes (the interval has one member and length zero); Spec of a field; the zero ring/empty affine open; empty covering index set (only covers the empty scheme); a one-chart cover; an infinite cover; and the usual D(t), D(t-1) cover of Spec k[t]. The interval argument also applies to non-Noetherian rings and non-separated schemes because it only uses the two open subspace inclusions. Nilpotents do not affect the argument because both correspondences are about prime ideals and the underlying topology.

Against delivery-errors B–E: no new unsplit node or disguised clause was created; every used notion is defined or explicitly expanded; sources are cited by the verified Stacks tags and labels; TeX uses single mathematical backslashes after JSON decoding; all searches were real; every citation says what the step uses; no new non-elementary assertion is left uncited; no step invokes the parent or introduces a cycle. Each step is under 2000 characters. All five are elementary reductions from the cited Mathlib leaves and definitions, with their arguments written out. No cross-unit non-leaf tool use needs declaration. The source and current item statements agree, so no hypothesis or conclusion was changed.
