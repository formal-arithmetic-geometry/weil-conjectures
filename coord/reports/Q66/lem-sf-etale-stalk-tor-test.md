# Stage-1 delivery: lem-sf-etale-stalk-tor-test

Group Q66, 2026-10-21. One existing item split; 0 new nodes; 0 Mathlib leaves.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sf-etale-stalk-tor-test.json: statement, split; no Mathlib match.
- citations.json: 11 entries, one per step/node citation, each checked as a literal substring of the cited statement.
- report.md: this report.
- searches.jsonl: the search tool's own log, read and reused in the item's search records.

## Attachments

None. The project search found no declaration with the item's blueprint tag and no declaration giving both the arbitrary-ring stalk criterion and inverse-image consequence. The existing `AlgebraicGeometry.Etale.torAmplitudeIn_leftDerivedUpperStar` in SixFunctors/Etale/Derived/Stability/Basic.lean gives the pullback clause, not the stalk equivalence. It is therefore not an attachment for this item. Generic exact-functor Tor-amplitude results also do not supply the geometric-stalk equivalence as stated.

## WANTED

None. All sources used were available locally.

## Findings and changes

The item was unsplit and had no proof. Its statement is correct and unchanged. The sandbox initially contained no item node, report or previous search log. I retained all existing metadata and Mathlib searches, added five searches actually executed through msearch.py, supplied four proof steps and their dependencies, and recorded the generic off-unit tool uses in split_report.tool_uses. I did not change the unit record: this item is not the unit's key statement.

The chapter and unit records and current main-20261015 blueprint proof were read. The proof supplies the pointwise Tor calculation needed in the opening/closed-immersion and affine-space portions of the unit. It does not replace those geometric reductions or change coefficient layers. In particular, classical geometric points are used only on the small etale site; no conservativity on arbitrary pro-etale sheaves is asserted.

## Searches and reuse

I searched the project Lean source for the item tag, Tor/amplitude terminology and stalk/fibre comparisons, and the whole DAG for stalk tensor, exactness, conservativity, inverse-image and Tor-amplitude statements. The blueprint_refs searches for `tor amplitude` and `stalk`, and its ancestor query, located the existing notions and identified sk-prop-sf-rf-shriek-preservation as ancestor. No whole-item duplicate was found. The existing lem-sfb-geometric-stalk-tensor-constant-single and lem-sfb-etale-derived-tensor-stalk already supply both needed tensor comparisons, so no new tensor lemma was created.

Five fresh searches are copied verbatim from searches.jsonl into mathlib_searches: LeanFinder twice with different semantic phrasings, Loogle, grep and LeanSearch. All services answered. The first LeanFinder hits concern etale morphisms; the second concerns ordinary monoidal complexes and condensed internal projectivity. Loogle found no Tor-amplitude declaration, grep found algebraic rank/stalk tensor identities, and LeanSearch found module-sheaf definitions and categorical instances. None states the item's derived geometric-stalk criterion. No candidate was promoted to a Mathlib leaf.

## Not duplicates

No new nodes were created. The item is not a restatement of a new lemma or a relocation of either of its clauses: the forward direction tests constant module sheaves; the converse tests every sheaf through its stalk modules; the last step proves the pullback consequence from that equivalence.

## Review by Q66

I read Stacks sites-cohomology.tex Tag 0DJJ, label lemma-tor-amplitude-stalk, including both proof paragraphs. Its second direction is the precise argument used here: cohomology of a derived tensor is detected on stalks and the stalk of that tensor is the derived tensor of the stalks. For the constant-coefficient forward direction I wrote the shorter direct argument using the constant sheaf of an arbitrary ordinary module. I also read sites-cohomology.tex Tag 0DEN, label lemma-check-K-flat-stalks, especially its first clause; this confirms that the existing unbounded tensor/stalk comparison has no concealed boundedness assumption. For the inverse-image consequence I read etale-cohomology.tex Tag 03Q1, label lemma-stalk-pullback, clauses (1) and (3), and its proof. For exactness and detection I read Tags 03PT (lemma-stalk-exact) and 03PU (theorem-exactness-stalks), and homology.tex Tag 010N (lemma-exact-functor). There are no new nodes needing separate sources, and no SGA source is used.

For step 1 I opened prop-weil-pbc-geometric-stalks-exact, lem-sp-exact-functor-preserves-homology and lemma-weil-pbc-geometric-stalk-conservative. The first states exactness on abelian sheaves, the second explicitly identifies homology after an exact functor, and the third reflects isomorphisms on every geometric stalk. Applying the third to the map to zero detects zero cohomology sheaves. I made explicit why passing from module sheaves to underlying abelian sheaves is legitimate: kernels and images inherit the module action and the quotient has its induced action. Thus I do not use the Zariski module-stalk exactness lemma for an etale stalk. Exactness on each three-term piece works in every degree, even for unbounded complexes.

For step 2 I opened def-kun-tor-amplitude and lem-sfb-geometric-stalk-tensor-constant-single. The former quantifies over every module sheaf in degree zero, including the constant sheaf of each ordinary A-module. The latter states exactly the resulting derived tensor/stalk identification and expressly allows arbitrary coefficient rings and modules. This checks the essential quantifier: the test modules are not restricted to finite, constructible or flat modules.

For step 3 I opened lem-sfb-etale-derived-tensor-stalk in full. Its statement provides the canonical isomorphism for two arbitrary objects of the unbounded etale derived category, not merely constant sheaves. Hence it applies with the second object an arbitrary module sheaf in degree zero. The assumed ordinary-module test applies to that sheaf's A-module stalk; step 1 and the cited conservativity statement then give exactly the vanishing required by the definition. No new clause of the item is hidden in a new dependency.

For step 4 I opened prop-weil-pbc-inverse-image-modules-exact and lemma-openclosed-stalk-upperstar. The former identifies the constant rings, agrees with the abelian inverse image and states exactness. The latter is the natural stalk comparison for any scheme morphism, with no etale or flat hypothesis on that morphism. I spelled out its module-linearity and differential compatibility: naturality for scalar multiplication gives A-linearity, product compatibility gives the addition map, and naturality for each differential produces a complex isomorphism. Exactness lets this computation descend to the derived categories. The composite u followed by a geometric point is again a geometric point, with the same algebraically closed field, so the criterion on T applies. This proves preservation without introducing scheme-flatness or finite-type hypotheses.

I checked delivery-errors B through E: no new-node schema issues, no unsupported tag-only citations, no use of a dependency's proof in place of its statement, no replacement of the unit route, and no unstated ring, boundedness or geometric hypothesis. Each of the eleven citations has a verbatim quote in citations.json. I checked all proof steps for hidden comparisons and long-step issues; the largest is under 1000 characters. The non-elementary comparisons are the existing cited nodes, and the remaining operations on kernels, scalar maps and differentials are written out.

Small cases checked: the empty scheme (every module sheaf and derived object is zero and the stalk condition is vacuous); the zero ring (only zero modules); K=0; a=b (the exact same degree-zero testing argument); shifts; unbounded K; non-Noetherian A; and arbitrary scheme morphisms. None requires a correction. The proof distinguishes ordinary A-modules used for stalk tests from arbitrary A_T-module sheaves used in the definition.

## Unfinished work

None within the one-level stage-1 split. Existing dependency nodes retain their own independent status; no Lean code was written and no compiler, Lake or build command was run.
