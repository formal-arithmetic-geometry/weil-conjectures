# Q32 stage-1 report: lem-sf-automorphism-completion-unit-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-sf-automorphism-completion-unit-comparison.json`: statement node, split into eight proof steps; no Mathlib match for the whole statement.
- `citations.json`: eighteen literal statement excerpts, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the unaltered log produced by msearch.py. `write_split.py` is a sandbox-only preparation script, not a project file.

No new nodes and no new Mathlib leaves. The item statement, source, chapter, unit, creation record and blueprint ancestry are unchanged. Only split-owned fields were written. No Lean source, compiler, Lake, repository writes, direct git commands, launcher edits or agents were used.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag and for automorphism/completion found no declaration stating this item. The upstream integral-completion file was also read: `DerivedCategory.derivedCompletionCompIso` in `CategoryTheory/DerivedCategory/Complete/IntegralCompletion.lean` concerns constant coefficient module categories, principal non-zero-divisor ideals and a further completion. It neither states the actual completed-ring assertion here nor the comparison with these specified cochain units. It is not an attachment.

## WANTED

None. All documents used are present locally.

## Corrections and findings

The imported node was a sound statement with an empty proof. No statement dispute or change was necessary. Its completed coefficient category is essential: the argument does not identify it with the constant coefficient module category. Stacks 099M and 099N were read for context, but their constant coefficient conclusions are not used to prove this completed coefficient claim. Instead the argument works with the ringed Koszul reflector and with the concrete completed coefficient ring map already specified in the statement.

The main work is kept in the item: explicit finite scalar matrices identify the Koszul tower, a map on each product component identifies `1-t`, and the map on both fiber summands identifies the specified completion unit. The restrictions of the actual adjunction and the uniqueness calculation are then written out. There is no new node restating a clause, no proof hidden in a statement-only node, and no new node for a two-line elementary observation.

## Search results and reuse

There was no earlier split, report or search log in this sandbox. I read the inherited Q20 search records in the repository item, then ran and recorded Q32's own searches through the required msearch command. The current item records exactly the tool/query pairs in this sandbox's log. Two semantic phrasings were tried: scheme automorphism/adically complete sheaves, and the explicit product/Koszul mapping-fiber unit. A separate reflective-equivalence query found the abstract Hom bijection in `CategoryTheory.unitCompPartialBijective`; I read `Mathlib/CategoryTheory/Adjunction/Reflective.lean`, lines 105–155. The result supplies no concrete coefficient or unit comparison. The grep searches include CategoryTheory and a second, whole-Mathlib expression, followed by a focused check of the AdicCompletion candidates. I read `RingTheory/AdicCompletion/Algebra.lean`, lines 420–449, and `RingTheory/AdicCompletion/Functoriality.lean`, lines 163–185. These concern ordinary ring/module completions, not unbounded derived module sheaves. Both services returned real hits; none was treated as unavailable or as proof of a match.

The whole-blueprint searches for completion, automorphism and Koszul, the ancestor command, and whole-DAG keyword searches were inspected. The generic exact-functor, scalar-extension, module-adjunction, site-equivalence and reflector statements already exist. None states the whole item, so `blueprint.same_as` is empty. No new lemma needs a search, definition, or duplicate-tag audit.

## Not duplicates

No new nodes. The following existing nodes are used directly instead of creating copies: `lem-weil-proetale-isomorphism-inverse-image`, `lem-weil-sheaf-scalar-extension-ring-iso`, `lem-sf-exact-functor-derived-triangulated`, `lem-weil-pbc-ringed-topoi-module-adjunction`, `lem-weil-pbc-ringed-koszul-completion-reflector`, and the intrinsic-completion and tensor-complex definitions.

## Review by Q32

I read the item's source, `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product.md`, including both sentences, and the current DAG parent, whose statement spells out the product and fiber construction and whose split report assigns this item base Step 8. The unit record is a remark with no proof steps; the chapter, unit and GOAL were read, and neither route level was changed. The chapter's historical source list was not adopted as authorization to use SGA. This delivery uses no SGA source.

For the mathematical source I read Stacks `algebraization.tex`, label `lemma-derived-completion-koszul` (0A0E), including the finite free Koszul complexes in degrees minus r through zero, and its relationship to `lemma-derived-completion` (099B); `proetale.tex`, labels `lemma-naive-completion` (099M) and `lemma-pushforward-Noetherian-case` (099N), statement and proof; and `sites-modules.tex`, label `lemma-adjoint-pullback-pushforward-modules` (03D7), including its tensor/restriction adjunction computation. The intrinsic-completion definition specifies the actual mapping fiber used here, while the existing ringed reflector states the Hom bijection. There are no new nodes requiring additional sources. The representative calculation is my own argument following the blueprint's explicit convention, so `proof_origin.by` is agent.

In Step 1 I checked all four cited statements. The adic datum defines the completed ring as the actual inverse limit; the isomorphism-of-sites lemma explicitly gives the limit comparison and quotient-map naturality; the inverse-image definition defines the constant structure map by constants; and completed pullback defines its coefficient map by exactly these projections. Thus invertibility is proved only for an automorphism, and fixing the generator scalars is verified after every quotient projection. No equality between a completed ring sheaf and a constant ring sheaf is used.

In Step 2 the site-isomorphism statement supplies the formula on every site object and exactness on underlying abelian sheaves. The scalar-extension lemma states the actual action formula and normalized tensor isomorphism, not merely an abstract equivalence of module categories. I checked the module-adjunction statement is for arbitrary commutative ring sheaves and the tensor pullback in use. The inverse coefficient map from Step 1 makes the inverse site transport linear, which proves an actual module equivalence; uniqueness of the adjoint identifies its inverse with the specified module direct image. This avoids using the site-isomorphism lemma's constant-module clause for completed modules without an argument.

In Step 3 the exact-functor statement is on unbounded derived categories and explicitly says termwise application descends. Step 2 supplies its exactness hypothesis for both inverse functors. The module-adjunction statement fixes which ordinary adjunction is being descended. Consequently no derived-adjunction assertion is being extracted from an ordinary-adjunction definition alone: the exact inverse equivalence and its actual unit/counit are descended termwise.

In Step 4 I compared the intrinsic definition's degrees, transition directions and degree-zero inclusion with the finite exterior-basis matrices. The total-complex definition states the differential and its sign. Multiplication by every generator is fixed in Step 1, so the two chain maps and the transition equality have identical entries. Only finite sums are involved because the Koszul complex is bounded finite free. This is an elementary matrix computation from the cited definitions, not an uncited general derived tensor theorem.

In Step 5 I used the definition's specific product and mapping-fiber complex, not an unspecified cone. The product comparison is justified by the explicit inverse equivalence from Step 2 and the displayed universal Hom calculation. Its commutation with `1-t` is checked after each projection; its differential equation is written on both summands. It is an elementary application of the product universal property and the formula for this differential. No assertion about arbitrary inverse-image functors preserving products is being made.

In Step 6 the quoted formula in the intrinsic definition is exactly the unit chain map. The proof checks every projected component of its first summand and zero in its second summand. The preceding maps are natural on all cochain maps. I checked that the intrinsic definition interprets its construction after localization and that the exact-functor result supplies the same descent for the pullback. Thus the result is the specific unit square, for every representative, not just some isomorphism between the two completed objects.

In Step 7 preservation follows from invertibility in that square. The inverse automorphism satisfies the same hypotheses and the same scalar calculation, which proves inverse preservation without imposing a constructibility assumption. I read the reflector's naturality clause to justify closure under isomorphism, as well as the intrinsic definition's completeness predicate. The full subcategory contains both functor images, so the same unit and counit restrict; no new adjunction is assumed.

In Step 8 I checked the exact sentence in the reflector node: its composition-with-unit bijection applies to every complete target. Step 7 makes `G(L(HM))` such a target. The ordinary module adjunction has already descended in Step 3, and its naturality identifies precomposition with the unit on the two Hom sets. Injectivity and then the adjunction bijection give uniqueness. This uses the node's statement, not its proof or a definition of reflectivity standing in for the theorem.

I checked the B–E failure modes individually. There are no new nodes, so no extra hidden definitions, statement-only proofs, unverified Mathlib leaves, missing Stacks labels or duplicate nodes. Every step citation was opened and read; citations.json contains literal substrings of those statements. All non-elementary inputs are existing cited nodes; Steps 4–7 explicitly carry their elementary finite-matrix, product, chain-map and restriction computations. A dependency-closure check found no path from any cited input back to this item. The off-unit statement tools are declared in `split_report.tool_uses`, with their precise roles; these are generic tools, not replacement routes. The proof does not use the construction inside another node's proof. No proof step exceeds 2000 characters.

For small cases I checked the identity automorphism (all maps are identity on the displayed generators and projections), the zero object, an unbounded representative (each fixed total degree still has only finitely many Koszul summands), repeated or zero generators (only their scalar entries are used), the empty tuple for I=0 (Q_m is the rank-one degree-zero complex and the same product/fiber formula applies), and the unit ideal/zero coefficient sheaf (the unique zero-object maps are invertible). None requires an extra regular-sequence, non-zero-divisor, boundedness, constructibility or finiteness-of-the-scheme assumption. The original coefficient hypotheses and universe/small-site assumptions suffice; the ringed reflector and exact-functor inputs have no stricter hypothesis.

## Unfinished work

None in this one-level split. No new unsplit nodes are introduced. The eight steps supply all clauses of the item; the existing nodes remain independently responsible for their stated general tools.
