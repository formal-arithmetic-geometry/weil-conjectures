# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-universal-injective-finite-test.json: item split into five proof steps; statement and statement dependencies retained.
- dag/nodes/sec-trace-formula/lem-trf-module-directed-colimit-fp.json: one new statement-only node, Stacks Tag 00HA; Mathlib verdict no match after two phrasings with LeanFinder, Loogle, grep and LeanSearch.
- citations.json: one verbatim statement quotation for each node used by each item proof step.

## Attachments

None. Searches in WeilConjectures/ of the supplied read-only source trees found neither the item's blueprint tag nor a project declaration proving the full finite-tensor-test criterion. Searches for the new node's tag, label and directed/filtered finite-presentation terminology also found no attachment. Master sorry declarations were not treated as finished proofs.

## WANTED

None. All mathematical sources used are in literature/stacks-project/algebra.tex.

## What was checked and corrected

The imported statement is correct. I read Tag 058K, theorem-universally-exact-criteria, including its six conditions and proof. Its first two conditions give the criterion for a cokernel short exact sequence; the item's equivalent formulation is injectivity of the first map. Rather than create another node carrying that same criterion, the delivered proof proves the map criterion directly by filtered colimits. This is below the unit level, and retains the inherited finite-test algebra input of the completion/flatification branch of lem-trf-local-term-locality. Neither the chapter nor the unit route is replaced.

I read Tag 00HA, lemma-module-colimit-fp, in full for the new node. Its index is a set of pairs of finite subsets of the module and finite sets of relations, ordered by inclusion with zero extension of relations. The empty pair supplies an index; the union of two pairs supplies a common upper bound. Its finite cokernel stages are finitely presented, and its canonical cocone is a colimit. The statement asks only for this existence, with a small nonempty directed partially ordered index, all linear maps and their compatibilities explicit. It contains no proof or extra specialization to universal injectivity. Its subsequent worker can obtain the construction from this precise source.

For tensor colimits I read Tag 00DD, lemma-tensor-products-commute-with-limits, including the identification of the colimit maps. For representative existence and eventual zero I read Tags 00D6 and 00D7, lemma-directed-colimit and lemma-zero-directed-limit. For the Noetherian clause I read Tag 00FP, lemma-Noetherian-finite-type-is-finite-presentation, especially (1). The earlier draft's Tag 0517 was only a section tag; the final proof cites the precise lemma Tag 00FP.

The initial sandbox draft packaged the substantive finite-test assertion into a new universal-exactness criterion. Self-review against D1/D2 identified that this did not provide a useful split. I removed that draft node and rewrote the item using the independent presentation foundation Tag 00HA and existing colimit tools. Searches already logged remain in searches.jsonl; the new node records only its own genuinely run searches. The inherited item search records are preserved, and the item adds genuinely run alternative searches with their actual results. Loogle's rejected unqualified identifier is recorded explicitly, not treated as evidence of absence by itself. No search service failure is disguised as a no-match result.

## Not duplicates

lem-trf-module-directed-colimit-fp vs lem-trf-valuation-finite-module-fp-reduction: the existing statement assumes a valuation-ring base, an essentially finite type local algebra and a finite module, and concludes surjective transitions with eventual stabilization of the closed fibre. The new statement is Tag 00HA for an arbitrary module over any commutative ring, with no finite-generation or valuation hypotheses; it does not assert fibre stabilization or surjective transitions. The existing node mentions 00HA in a proof source, but does not state its general assertion.

lem-trf-module-directed-colimit-fp vs lem-weil-pbc-site-flat-equational-criterion: the existing statement characterizes flat sheaves by local solutions to finite equations. It mentions Tag 00HA in a proof source but states no module colimit presentation.

lem-trf-module-directed-colimit-fp vs lem-weil-pbc-module-directed-colimit-finite-presentation: the existing statement concerns sheaves on a quasi-compact quasi-separated scheme. The new assertion is about algebraic modules, with their linear maps and colimit in the module category; extracting it from the scheme theorem requires the affine module/sheaf equivalence and preservation of finite presentation, rather than being an instance of its statement.

lem-trf-module-directed-colimit-fp vs lem-weil-pbc-module-filtered-colimit-finite-presentation: likewise the existing statement presents quasi-coherent sheaves, whereas the new node directly states the algebraic module presentation used here.

The whole-DAG searches used Tag 00HA, lemma-module-colimit-fp, and directed/filtered colimits with finite-presentation keywords. The blueprint search command returned zero matches for both 'module colimit finitely presented' and '00HA'. The new node's blueprint.from is the item's nearest imported ancestor, with the item prepended to the inherited via chain; same_as is empty.

## Review by Q128

I checked B1-B10 against the delivered node: its statement introduces R, Q, its small nonempty directed index and all cocone data; finite presentation and categorical colimit each cite the correct definition. It is statement-only and unsplit, with empty proof/proof_deps. TeX uses single backslashes in decoded strings. The source is the verified tag and label. No unsupported Mathlib leaf is claimed. Its searches were made by the required command in this item's sandbox, with the actual query text and log summaries retained.

For C1-C8 and D1-D5 I opened every cited node's statement, not merely its proof. Step 1 is just restricting the universal quantifier and uses no non-elementary fact. Step 2 uses precisely the new node's arbitrary-module presentation: R is commutative and Q is unrestricted, so its hypotheses match, and its small directed index is suitable for both later colimit tools. Step 3 uses the statement of lem-weil-pbc-tensor-commutes-with-colimits twice, with the same Q_i and fixed factors M and N; that statement supplies the canonical tensor cocones, not just an abstract isomorphic module. Step 4 uses both representative existence and eventual zero from lem-weil-pbc-filtered-colimit-modules-elementwise; its small filtered hypothesis follows from the nonempty directed poset in Step 2. The tensor definition states pure-tensor generation and composition of induced maps. I wrote the two required commutation identities on pure tensors explicitly, so no unproved transport or naturality comparison is hidden. Injectivity is invoked at the later finitely presented stage Q_j, not at the original stage and not for a possibly noninjective transition map. Step 5 uses the exact Noetherian finite-module theorem, plus the finite presentation and finite-generation definitions; the images of the standard basis explicitly prove the reverse finite-generation implication. Every uses entry has a verbatim quote in citations.json and the proof_deps list is exactly their union. Existing off-unit citations are Mathlib leaves or definitions, used as generic algebra tools, with no unit-step replacement. No new node restates the item, and no cycle is introduced by the presentation node's two definition dependencies.

For E1-E7 I checked zero modules, R the zero ring, identity maps, a noninjective map detected by Q=R, and an injective nonpure map (multiplication by 2 on the integers detected by the finitely presented module Z/2Z). The presentation lemma allows empty generators and relations, so the zero module does not cause an empty index. Directedness, smallness and commutativity are all available exactly where used. Finite presentation is not confused with finite generation over a non-Noetherian ring: their identification is used only in Step 5 under the Noetherian hypothesis. All proof steps are shorter than 2000 characters; the representative chase is one routine argument with each foundational input cited. No statement was weakened, no dispute was found, no SGA source was used, and no Lean, compiler, Lake or build tool was run.

## What could not be finished

The new Tag 00HA foundation is deliberately statement-only and unsplit, as required for a one-level stage-1 split. There is no remaining gap in the item's proof beyond its explicit cited nodes.
