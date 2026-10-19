# Stage-1 delivery: lem-sf-ordinary-triangle-counit-cone

1. Files written: `dag/nodes/sec-smooth-purity/lem-sf-ordinary-triangle-counit-cone.json`, the item, statement unchanged and now split into five proof steps; `citations.json`, with verbatim statement excerpts for every cited node. No new nodes and no Mathlib leaves were created.
2. Attachments: none. I searched the project source for the blueprint tag and the ordinary-triangle/counit-cone terminology; no sorry-free declaration states this item exactly.
3. WANTED: none.
4. The imported statement is retained. It is the abstract Hom-comparison obligation used by `prop-sf-localization-all-stages`, Step 3; no coefficient-specific hypotheses were added and no conclusion was weakened. No statement dispute or unit-record change is needed.
5. Unfinished work: none for this one-level split.

## Sources and searches

I read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-prop-sf-localization.json`, the item node, and the current `main-20261015` statement and proof of `prop-sf-localization-all-stages`. The unit's Hom(-,L) argument and the parent proof's Step 3 both prescribe completing the exceptional counit and identifying its cone by the ordinary complementary triangle. I also read the source statements of `def-weil-triangulated-category`, `lem-weil-pbc-hom-out-of-triangle-exact`, `lem-weil-pbc-five-lemma`, and `lem-coef-joyal-homset-iso-detection`; these are the only DAG facts used. The item's inherited Mathlib searches were read and retained; they found only general triangulated-category infrastructure and no counit-cone localization theorem, so no new search was needed.

## Review by NH

I checked the item against B–E of `coord/delivery-errors.md` and read every cited node in full. The statement introduces all six categories, all four adjunctions, the invertible ordinary counits, the vanishing `j^*i_*`, the ordinary distinguished triangle, the exceptional counit, and the open unit. The source search found no exact Lean declaration, so this is a genuine split rather than an attachment.

Step 1 proves the global orthogonality directly from the assumed adjunction `j^* \dashv j_*`, exactness, and `j^*i_*=0`; it also checks `u e=0` by the triangle identity. This handles every shift and the zero object cases. Step 2 uses exactly the TR1 cone clause in `def-weil-triangulated-category` to complete `e`; no chosen cone data is smuggled into the statement. Step 3 uses the cited Hom-out exactness statement to factor `u` through the cone and then factors a difference through the connecting map; the orthogonality from Step 1 makes that factor zero, so the comparison is unique.

Step 4 applies `Hom(-,K)` to the supplied ordinary triangle and `Hom(M,-)` to the cone triangle. I checked the four adjunction transposes: the closed outer terms become `Hom(M,A)` and `Hom(M,A[1])`, while the open term becomes `Hom(M,B)`. The actual counit and unit give the first two maps after cancelling the adjacent unit–counit pairs; the resulting five-term diagram has identity maps at the other four positions. Hom groups are abelian because the category is additive, so the cited five-lemma node applies and gives bijectivity of `Hom(M,β)` for every `M`. Step 5 then uses the cited Yoneda Hom-set criterion to conclude that `β` is an isomorphism. Every citation quote is copied verbatim into `citations.json`.

I checked edge cases `K=0`, `U=∅`, `Z=∅`, identity immersions, and arbitrary shifts. No step is a clause-restatement node, no duplicate node was created, and every non-elementary step is below 2000 characters. The proof uses no SGA source and respects the route lock.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.
