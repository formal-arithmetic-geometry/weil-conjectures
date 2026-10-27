## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-diagonal.json`: statement, split; no Mathlib match. The statement and its statement dependencies are unchanged.
- New nodes: none. Mathlib leaves: none.
- `citations.json`: nine verbatim citation records, covering every use in the six proof steps.
- `searches.jsonl`: actual Q53 search-command log, retained with the sandbox. `prepare.py` records the construction of the draft; it is scratch material, not a delivered repository file.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the item id, its blueprint tag, coherent-diagonal terminology, coherent modules, and Isom/proper-support terminology. No declaration supplies the statement. General module and scheme isomorphism declarations are not this algebraic-space moduli statement.

## WANTED

None.

## What changed and what was wrong

The imported item was statement-only, with no proof or proof dependencies. I retained its statement, source, creation metadata and blueprint provenance, and supplied the equalizer reduction of Stacks 08W6 followed by the inverse-pair construction in 08K9. I reused the existing Hom theorem 08K6 rather than introducing an Isom theorem that would merely carry most of this item's argument. Only algebraic-space representability is needed, so the stronger affine/finite-presentation conclusion of 08K9 and its closed-section lemmas are unnecessary. The construction uses arbitrary fibre products of algebraic spaces directly.

The current latest blueprint unit and direct-images proof were read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. Its direct-images paragraph (3) uses proper/open direct images and compactification. This item is an inherited coherent-moduli prerequisite in that chain; it does not modify the chapter or replace the unit route. `blueprint_refs.py ancestor` returns None; I retained the imported null ancestor and via history rather than inventing a blueprint id. Whole-blueprint searches for “coherent diagonal”, “isomorphism functor”, “08W6”, “045G”, and “coherent families” revealed no replacement for this item. A broad Hom search was also read; the specific DAG source search found the existing `lem-sfb-space-module-hom-affine`.

The generic off-unit use of `lem-trf-space-fibre-products-etale-covers` is declared in `split_report.tool_uses`: it supplies foundational space products, not a substitute proof of any six-functor preservation claim. All other statement inputs are in the item's unit; the remaining off-unit inputs are definitions.

## Source error

Stacks `quot.tex`, Tag 08K9, names $I=\operatorname{Hom}(F,F)$ and $I'=\operatorname{Hom}(G,G)$, but its displayed composition map to $I\times I'$ writes the composites in the reverse order. With $u:F\to G$ and $v:G\to F$, the correctly typed pair is $(vu,uv)$. For example, $F=k$, $G=k^2$ makes the two endomorphism types visibly different. Step 4 uses this correctly typed order and the corresponding identity section. This is a correction to a proof display, not to the item's mathematical statement or the source theorem. No STATEMENT-DISPUTED item correction is needed.

## Mathlib searches

I preserved the item's imported search records, and appended only queries actually logged for Q53. I ran LeanFinder, LeanSearch, Loogle and grep, with a second natural-language formulation and a second grep formulation. The seven new records in the item have the identical tool/query strings as `searches.jsonl` and name the actual returned declarations. All services answered. The first semantic hits concern scheme flatness/descent, finite-presentation data for quasicoherent modules, general categorical relative diagonals and Zariski local representability. The second semantic hits concern scheme module forgetful functors, affine-space coordinates, ordinary categorical isomorphisms and presheaf module isomorphisms. Loogle found closure of quasicoherence under isomorphisms. The second grep found only the tilde/global-sections characterization at `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:875`. None represents the coherent-family isomorphism functor on algebraic spaces; the item remains a split statement, not a Mathlib leaf. There are no new nodes requiring searches.

## Not duplicates

No new nodes. The DAG already contains 08K6 as `lem-sfb-space-module-hom-affine`, arbitrary finite-presentation base change as `lem-sfb-space-flat-proper-fp-locality`, and module base change as `lem-sfb-space-module-base-change-flat-proper-support`; I cite them rather than making duplicates. The existing `lem-sfb-stack-diagonal-space-source-representability` assumes representability of the diagonal and proves a different consequence, so it cannot prove this item. I expand the definition-level diagonal equivalence instead of citing that implication backwards.

## Review by Q53

I read Stacks `quot.tex` Situation 08KB, Lemma 08W6, Proposition 08K9 and Proposition 08K6; `algebraic.tex` Lemma 045G and its proof of (1) iff (2); `spaces-morphisms.tex` 03XR and 05VW; and `spaces-perfect.tex` 0CZI/0CZJ. I opened the statements of all seven proof dependencies, rather than relying on their titles. Their relevant words are copied verbatim into `citations.json`.

Step 1 uses the representable-diagonal clause of `def-trf-algebraic-space` and the actual sheaf-product existence conclusion of `lem-trf-space-fibre-products-etale-covers`. Pulling that diagonal back along $(b,c)$ gives a scheme E, even when B is nonseparated. The unique factorization condition is the equality of the two maps, not mere equality of point images. An isomorphism in this fibre category really requires that equality.

Step 2 uses the separate finite-presentation base-change assertion of `lem-sfb-space-flat-proper-fp-locality`; that assertion does not assume f flat or proper. I checked the locally-finite-type hypothesis needed by `lem-sfb-space-module-base-change-flat-proper-support`: the maps to T are finitely presented, and a finitely presented algebra is finitely generated. The module lemma explicitly preserves all four conditions under any scheme base change. In particular E need not be flat over T, and none of its non-flat, non-Noetherian or non-quasi-compact possibilities is silently excluded.

Step 3 uses the exact statement of `lem-sfb-space-module-hom-affine`. For each of the four ordered pairs the target is one of the two modules verified in step 2, with precisely the required finite presentation, relative flatness and proper support. Its bijections are natural on every scheme over E, which is necessary for step 4, not only on geometric fibres. The source modules are also finitely presented, although the stronger conclusion using that condition is not needed.

Step 4 uses those natural representing bijections, the definition of algebraic-space morphisms as natural transformations, and the fibre-product node for existence of P, Q and J. Tensor pullback is the functor of `def-trf-space-etale-module-functors`, so preservation of identities and composition proves naturality of the composition/identity maps. I corrected the source's displayed order as explained above. No closed-immersion, affineness, openness-of-invertibility or Artin representability fact is used without a node. The only equations imposed are the two defining inverse identities.

Step 5 is the elementary computation of points of this fibre product. It writes the inverse-uniqueness calculation and the inverse pair assigned to an isomorphism. It also handles T-test schemes without a map to E: both the original Isom set and the represented set are empty. Pullback sends inverses to inverses by the same two equations, proving compatibility with every restriction. No separate comparison theorem is hidden here.

Step 6 uses only the 2-fibre-product and representable-by-spaces definitions in `def-sfb-stable-pointed-moduli-groupoids`. I spell out the equivalence to the discrete Isom groupoid: the triple maps to beta alpha inverse, each isomorphism has a representative, and the compatible arrow between representatives is uniquely alpha-prime inverse alpha. This proves the diagonal equivalence directly, rather than appealing to the uncited theorem 045G as a black box.

Small cases checked: E empty, b=c (E=T), unequal b,c which become equal after a non-flat base change, both modules zero (the inverse-pair space is E), exactly one zero module (inverse identities still detect its vanishing after base change), and a rank-one/rank-two pair (the order of the two composite equations matters). Neither an affine/proper ambient X nor a flat f was used. The ordinary scheme situation is included. For two equal nonzero modules the construction retains their automorphisms; it does not replace the groupoid by isomorphism classes.

Against delivery-errors B--E: no unsplit new nodes or proof-in-statement, no new definition without a cited notion, no duplicate or clause moved into a new node, no proof-of-a-dependency substituted for its statement, and no unexpanded standard argument. All cited statements were checked literally, and their dependency closures do not include this item. Every non-elementary operation is one of the cited statements; the two elementary steps write their computations. No step is over 2000 characters. There is no SGA citation, no compiler invocation, and no change outside the sandbox. I found no statement error and corrected only the proof-display order described above.

## Unfinished work

None in this one-level split. The existing unsplit Hom-representability input remains an item for its own worker; it is deliberately not split here.
