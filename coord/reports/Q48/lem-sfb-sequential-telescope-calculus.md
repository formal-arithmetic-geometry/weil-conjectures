# Q48: lem-sfb-sequential-telescope-calculus

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-sequential-telescope-calculus.json (statement, split, not a Mathlib match); citations.json; this report. No new nodes or Mathlib leaves.
2. Attachments: none. Searched live lean/WeilConjectures for the exact blueprint tag, hocolim/homotopyColimit/telescope and eventual-stabilization terminology. CompactHomHocolim requires compactness and proves a different Hom comparison; the module and complex telescope results do not state this arbitrary triangulated-category assertion.
3. WANTED: none.
4. The imported statement is correct and unchanged. Its proof was empty. The inherited blueprint ancestor is null: blueprint_refs.py ancestor reports None. Kept the supplied detailed place and via chain, rather than inventing an imported ancestor. Read the current latest blueprint direct-images proof (3), the chapter and unit records, and its semisimplicial-realization parent. This categorical calculation supports the parent's stationary component tower and changes no unit route. The current blueprint direct-image proof is the compactification assembly; the older detailed alteration provenance is retained as history in the inherited field.
5. Unfinished work: no mathematical gap found. Server dry run and push follow this report.

## Searches and existing results

The sandbox was empty apart from brief markers on resumption, with no active deliver.py or msearch.py process. No interrupted delivery was repeated. Read the item's inherited searches and retained them. Additional searches run through msearch.py are recorded in searches.jsonl and appended with their actual query text and result summaries. Both semantic phrasings returned t-structure facts or cones of individual cochain maps. LeanSearch returned ordinary eventually constant limits/colimits; read EventuallyConstant.lean:235-255, which requires a genuine colimit cocone, unavailable for a general mapping telescope without this argument. Loogle homotopyColimit had no hits. The whole-source grep had unrelated finite-sum and metaprogramming telescopes; the focused CategoryTheory grep found no hocolim/homotopyColimit/mapping-telescope declaration. No negative result is inferred from a service failure.

Searched the whole DAG for split-triangle, representable exactness, relevant tags and titles, then read the full statements of both existing Hom exactness nodes. Blueprint searches for split triangle, Hom(-,W), telescope, eventually and homotopy colimit found no duplicate. The four homotopy-colimit hits define the notion or concern complexes, truncations and exact functors, rather than this assertion. No new node was necessary: finite transition composites, finite sums and coproduct extensionality are explicit elementary calculations, while the genuinely non-elementary triangle facts already have Mathlib-leaf nodes.

## Review by Q48

I read derived.tex at definition-derived-colimit (090Z), remark-uniqueness-derived-colimit (0CRH), lemma-hocolim-subsequence (0CRJ), lemma-split, lemma-composition-zero (0146), and lemma-representable-homological (0149). The original source description proposes deleting a prefix and comparing to a constant tail. Instead, below the unit, I supplied the finite-sum contraction explicitly. The proof is marked agent-written and does not silently assume an ordinary-colimit property or a functorial choice of cones.

Step 1 uses exactly the additive-category and shift data from def-weil-triangulated-category and the universal property in def-weil-pbc-category-colimit, specialized to the countable discrete diagram. Its forward composites use arbitrary prefix arrows; inverses occur only between indices at least N, where the hypothesis grants them. Each component of l is a finite sum of arrows into S, so no infinite summation or false description of Hom into a coproduct occurs. The a-components satisfy the compatibility at the boundary N as well as on each side.

Step 2 uses only that same coproduct universal property to check two morphism identities on coprojections. I checked the finite cancellations separately for i<N, i=N, and i>N, including the negative sign on the tail sum. These two routine calculations remain steps, not redundant new nodes. No general comparison lemma or uncited standard fact is hidden in them.

Step 3 uses clause (i) of lem-weil-pbc-hom-into-triangle-exact, whose statement explicitly gives the zero composite, on the supplied triangle and its twice rotated triangle. Rotation and additive shift are explicitly in def-weil-triangulated-category. The sign on the twice rotated first arrow does not affect the zero equality. Shifting lf=1 gives l[1]f[1]=1, so the actual boundary d is zero. No compactness or t-structure enters.

Step 4 uses clause (i) of lem-weil-pbc-hom-out-of-triangle-exact to factor a through the actual p, and clause (ii) to factor the difference 1-pjb through the actual d. I read that node's full statement: it contains both factorizations, including the second one at Z. These yield both inverse identities, rather than just an abstract isomorphism of objects. The final induction uses only pf=0 already proved in step 3 and invertibility of finite composites in the stable tail. citations.json contains verbatim statement text for every use in every step.

I checked the B-E error lists against the actual formulas: no new statement-only nodes, duplicate nodes, clause restatements, concealed comparison assertions, unsupported exactness claims, cycles through children, omitted source hypotheses or coefficient changes. All four steps are below 2000 characters. Small cases checked directly: N=0 (empty prefix), N=1 with a noninvertible or zero u_0, i=N, r=N (empty transition product), the constant identity sequence, and the zero stable object. The formulas work without assuming any prefix transition is invertible. Statement and all inherited import/provenance fields are retained. Both non-elementary proof dependencies are existing Mathlib leaves, so no off-unit route authorization is needed.

## Not duplicates

No new nodes were created.

Dry run 1 found the cases row break adjacent to a TeX command in step 1. Added whitespace after the row break for unambiguous TeX parsing; mathematical content unchanged.
