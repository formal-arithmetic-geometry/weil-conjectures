# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-unramified-radicial-representable.json`: split statement; unchanged statement and statement dependencies; five proof steps; no new nodes, no new Mathlib leaves.
- `citations.json`: a verbatim statement quotation for every step/node citation.

The sandbox initially contained no item or earlier report. I copied the current unsplit live item and retained its provenance, source, statement, and recorded Mathlib searches. No repair-note file for this item was found.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag and unramified/radicial/representable combinations found no declaration stating the item. The universally-injective declarations found under AlgebraicGeometry concern schemes; they do not supply algebraic-space schemehood. No Lean was written or compiled.

## Literature wanted

None.

## Findings and changes

Stacks `spaces-more-morphisms.tex`, Tag 05W6, `lemma-universally-injective-unramified`, states exactly the representability consequence under the item's condition (2). Its proof gives the route: open and surjective diagonal, monomorphism, locally-finite-type monomorphism implies separated locally quasi-finite, then schemehood after scheme base change. I implemented this route after first fixing the arbitrary scheme test. This is essential because the existing open-diagonal and locally-finite-type monomorphism nodes have scheme targets, not arbitrary algebraic-space targets. Using them directly for the original map would have been C4.

I read the current blueprint in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, particularly the unit `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, together with the DAG chapter and unit records and the inherited detailed provenance. This is a supporting input on the existing alteration/curve-moduli chain; it does not replace any unit step or alter a chapter. `tools/blueprint_refs.py ancestor` reports `None`, agreeing with the live item's inherited `blueprint.from.node`; I retained that lineage instead of inventing an imported ancestor. Whole-blueprint searches for `unramified` and `universally injective` yielded no equivalent statement. DAG searches by 05W6, 05W1, 040X, 0463, 0418, their labels, and related words found the existing nodes reused below.

No new statement, source error, or statement dispute was found. The item's old empty proof was the only mathematical gap repaired. No nodes were created for the elementary point-set diagonal argument or for clauses of this item.

The generic off-unit tools are explicitly declared in `split_report.tool_uses`: algebraic-space fibre products, open-subspace point calculus, and the separated locally quasi-finite schemehood theorem. Their uses are generic facts, and no lemma of this unit replaces them.

## Mathlib searches

The live item's five existing search records were retained unchanged. I additionally ran the authorized search command for the diagonal subclaim, with two semantic phrasings, Loogle, LeanSearch, and source grep; these actual calls are in `searches.jsonl`. All services answered. They found `AlgebraicGeometry.UniversallyInjective.iff_diagonal` and `AlgebraicGeometry.universallyInjective_eq_diagonal`. I read `Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean`, lines 34–79: its objects are explicitly `Scheme`, so this is not an algebraic-space match and cannot attach or finish this item. The needed forward implication is a two-line point-set calculation already, so I did not create a searched-but-unnecessary child node. No search that was not run has been added to a record.

## Not duplicates

No new nodes. In particular, the open-diagonal theorem, scheme-target monomorphism theorem and schemehood theorem were reused, not restated as children.

## Review by NW

I read Tag 05W6 in full, including all four equivalent conditions and its moreover clause, and compared the item hypothesis by hypothesis. The source requires a scheme base and algebraic spaces, with unramifiedness including local finite type and universal injectivity under arbitrary algebraic-space changes. These are precisely the item's assumptions. It asks only for representability, so separatedness and local quasi-finiteness appear as intermediate conclusions rather than strengthened hypotheses.

For step 1 I opened `def-trf-scheme-algebraic-space`, `lem-trf-space-fibre-products-etale-covers` and `lem-sfb-space-unramified-permanence`. Their statements respectively supply the actual representable sheaf of the test scheme, algebraicity of its fibre product with X over Y, and preservation of unramifiedness under every base change. I also checked the last fact in `spaces-morphisms.tex`, Tag 03ZJ, `lemma-base-change-unramified`. No pre-existing representability of the projection is used. Its local finite type is part of the stated unramified convention.

For step 2 the cited fibre-product statement gives fibre products in algebraic spaces and `def-a1-space-point-topology` supplies their functorial field-valued point classes. Associating compatible tuples of sections identifies the iterated base changes, so universal injectivity of the projection follows from the original quantifier. For the first projection p of the self-product, p is injective on point classes and p delta is the identity. Applying p to delta(p(z)) and z gives equal values and hence equal points. This is an elementary set-theoretic calculation, not an appeal to an uncited algebraic-space theorem. I checked it against the last paragraph of Tag 040X, `lemma-universally-injective`: the source uses exactly this argument for (2) implies (3). I kept it as a step rather than creating a node for the more general three-way equivalence.

For step 3 I read the entire statement of `lem-sfb-unramified-space-open-diagonal`: it applies to our now-schematic target T and says the diagonal is a representable open immersion, including every scheme test. This agrees with Tag 05W1(1), `lemma-diagonal-unramified-morphism`. I opened `lem-a1-space-point-open-calculus`; its final sentence says verbatim that an open subspace with full point image equals its target. This is exactly what the proof takes, and I checked the corresponding inclusion-preserving bijection in `spaces-properties.tex`, Tag 03BZ, `lemma-open-subspaces`. The remaining passage from invertible diagonal to injectivity on sections is written out as the compatible-pair argument, so there is no hidden use of a stronger Yoneda statement or a definition node as a theorem.

For step 4 I opened `lem-sfb-space-lft-monomorphism-separated-lqf` and `spaces-morphisms.tex`, Tag 0463, `lemma-monomorphism-loc-finite-type-loc-quasi-finite`. The DAG node is the scheme-target specialization and requires exactly chartwise local finite type and injectivity on every test-scheme section. Steps 1 and 3 establish these separately. Its conclusions are separatedness in the representable-closed-diagonal sense and chartwise local quasi-finiteness; neither requires quasi-compactness, Noetherianity or a field base.

For step 5 I opened `lem-a1-separated-locally-qf-space-representable` and its source Tag 03XX, `proposition-locally-quasi-finite-separated-over-scheme`. Its target must be a scheme, and it requires precisely the two properties obtained in step 4. The node supplies an actual scheme over T with an isomorphism of its representable sheaf to E, which gives exactly the definition of representability in the item. This is the scheme-target input of the general Tag 0418 theorem cited by 05W6, not a new restatement of this item's conclusion.

I checked B1–B9, C1–C8, D1–D5 and E1–E6 against the files: no unsplit child hides a proof, no new data or undefined object is introduced, every non-elementary input is a cited statement, and no dependency applies its proof rather than its statement. The complete quotation list in `citations.json` was extracted from the actual node statements. The only elementary step is the explicit compatible-tuple and injective-projection calculation. No step exceeds 2000 characters. The mathematical repair was to move to a scheme target before invoking the existing specialized results; the statement itself needed no correction.

Small cases checked: an empty source or an empty scheme test gives the empty representing scheme and an empty, hence surjective-to-empty, diagonal; the identity and open immersions satisfy the argument without forcing closedness; a non-flat closed immersion is allowed because no flatness is used. A positive-characteristic nontrivial purely inseparable field extension is universally injective but not unramified, so it does not incorrectly enter the open-diagonal step. Arbitrary non-quasi-compact test schemes are allowed by every cited theorem. There is no additional finite-type, separatedness or quasi-compactness hypothesis on T or Y.

## Unfinished work

None in the one-level split. Existing dependency nodes remain the project's responsibility; no claim is made that they are Lean-closed.
