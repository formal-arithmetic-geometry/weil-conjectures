## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-normal-ascent.json`: item split into five steps using existing nodes, no Mathlib match for the whole scheme theorem.
- `citations.json`: verbatim statement quotations for every step citation.
- `searches.jsonl`: actual Q107 search-command records; item also retains its creating worker's earlier searches.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searching `lean/WeilConjectures/` by the exact blueprint tag, item id, and smooth/normal concepts found no declaration stating the scheme theorem. `RingHom.Smooth.isNormalRing` in `WeilConjectures/RingTheory/SmoothNormalRing.lean` states the ring theorem and already belongs to `lem-weil-pbc-smooth-over-normal-ring-normal`; it is a dependency, not an attachment of this item. The normalization file's stalk-normality declaration concerns a different normalization construction.

WANTED: none; all sources used are present.

The item had an empty proof. Its statement agrees with the ascent assertion in Stacks 034F (`descent.tex`, `lemma-normal-local-smooth`). I corrected doubled TeX escapes in the statement only, without changing any hypothesis or conclusion. In particular the no-Noetherian, no-quasi-compactness, no-connectedness, no-surjectivity clauses and empty cases remain. This is not a statement dispute. The source calls on the arbitrary-ring ascent theorem 033C, not just its Noetherian predecessor 0C22.

The chapter and unit records were read. This is a tool below the inherited alteration/normalization prerequisite of direct-image stability, not a node realizing the unit statement, so no unit record is changed. The inherited blueprint place and via chain are retained. `blueprint_refs.py ancestor` reports no imported ancestor (None) on this existing chain. Searches of the whole imported blueprint for `normality ascends`, `smooth over normal`, `smooth algebra`, `smooth morphism of schemes with normal`, `smooth normal`, and `034F` gave no equivalent blueprint node. The sole `smooth normal` hit concerns curve constant-sheaf extension invariance, not arbitrary smooth normality ascent. `same_as` is therefore empty.

The Q107 Mathlib searches tried LeanFinder in both scheme and ring phrasing, LeanSearch, Loogle, and grep in the scheme and ring smoothness sources. The first semantic hits define smoothness and give stability or normalization properties; the second semantic hits give integral closedness of localizations or normal closures. None states the scheme theorem. Loogle returned an unknown identifier for `AlgebraicGeometry.IsSmooth`; I recorded that diagnostic, not an absence inference from an invalid pattern. The actual pinned source has `AlgebraicGeometry.Smooth`, `smooth_appLE` at lines 63-65, and alias `IsSmooth` at line 69. The whole item requires the existing ring-ascent theorem in addition to this chart criterion, so it is not a Mathlib leaf.

No unfinished task remains within the one-level split.

## Not duplicates

No new node is introduced. DAG searches for 033C and 034F, normality and affine/stalk-localization terminology located the existing ring ascent, affine-open basis, and affine-open stalk-localization nodes. I reused those statements. In particular I did not introduce an affine-normality lemma: the argument from prime localizations and the hypothesis on the scheme is written in step 3.

## Review by Q107

I read the ascent paragraph of Stacks 034F (`descent.tex`, `lemma-normal-local-smooth`), where affine normality ascent is exactly Algebra 033C. I also read 033C (`algebra.tex`, `lemma-normal-goes-up`) including its non-Noetherian reduction, Properties 033I (`definition-normal`) and 033J (`lemma-locally-normal`), Schemes 01IT (`lemma-basis-affine-opens`), 01HV (`lemma-spec-sheaves`, especially (1) and (6)), and 01HF (`example-open-subspace`). These sources agree with the item under arbitrary schemes. There are no new nodes whose source or statement needs review.

For step 1 I opened `lem-weil-pbc-affine-opens-basis`: it explicitly provides an affine neighbourhood inside any given open, so it can be applied first at g(v) and then at v inside g^{-1}(B). No intersection of affine opens is presumed affine, and no finite subcover is used. This is a cited basis theorem, not marked elementary.

For step 2 I opened `def-sbc-smooth-morphisms`. Its first paragraph explicitly records agreement with the affine-local smooth-ring-map definition, in addition to the formally smooth formulation. Applying that recorded equivalent formulation to A and B gives exactly the map R to S. I checked the underlying criterion against Morphisms 01V6 (`lemma-smooth-characterize`, (1) implies (2)) and the pinned Mathlib `Smooth.smooth_appLE`. This step is marked elementary because it instantiates the equivalent definition already in the cited node. It does not invoke the infinitesimal lifting definition alone as a proof of an unrecorded theorem. In particular it does not make the incorrect claim that an arbitrary smooth-morphism stalk map must itself be a finitely presented smooth ring map.

For step 3 I opened `lem-weil-pbc-affine-open-stalk-localization` in full: its affine chart identifies the points with prime ideals, and clause (c) explicitly gives R_p isomorphic to the ambient scheme stalk. I also opened `def-weil-pbc-normal-ring`: its final sentence defines normality by every prime localization being a normal domain, and its first sentence defines normal domains by integral closedness in the fraction field. Thus the hypothesis on W supplies precisely what is needed at each corresponding point. The ring R is not assumed a domain. The elementary preservation argument under a ring isomorphism is spelled out, rather than treating normality of affine sections as an uncited black box.

For step 4 I opened `lem-weil-pbc-smooth-over-normal-ring-normal`: its statement assumes only a smooth homomorphism of commutative rings and normality of the source, and concludes normality of the target. Those are exactly step 2 and step 3. The additional citation of `def-weil-pbc-normal-ring` spells out the prime-localization conclusion. The ring theorem is an existing generic tool in another unit; its use is declared in split_report.tool_uses for the maintainer's review. No current-unit step is replaced by it: this is precisely the algebra input that the item's Stacks source invokes.

For step 5 I reopened clause (c) of the same affine-open stalk theorem for A in V, so it gives S_qv isomorphic to O_(V,v), not a fibre ring or the target stalk. Normality of S from step 4 and the normal-ring definition give the integrally closed domain at that prime. Quantifying over all v then proves the item. The two stalk-identification steps are not marked elementary; the cited theorem carries the non-elementary identification.

I checked the B--E return checklist against the actual files: no clause has been moved into a new node, no source proof or definition is being used for a stronger theorem than its statement supplies, and the dependencies are the union of step uses. Every citation has an exact copied statement in citations.json. All non-elementary steps are shorter than 2000 characters and have no hidden comparison or standard lemma. The only extra inference beyond the quoted statements is invariance under an explicitly given ring isomorphism and choosing/quantifying points, which is written in the steps.

For the edge cases I tested the empty scheme, the unique morphism into an empty target (which forces an empty source), a non-surjective open immersion, and a disconnected normal affine base such as a product of two fields. Step 3 only asserts that every prime localization of R is a normal domain, so the product case is allowed. The whole proof uses single affine neighbourhoods and the arbitrary-ring 033C, so it makes no Noetherian, finite-type-over-a-field, quasi-compactness, or connectedness assumption. No characteristic or fibre dimension is restricted. The only correction required was TeX escaping and expansion of the empty proof; no mathematical source error was found.
