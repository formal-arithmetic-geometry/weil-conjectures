# Stage-1 delivery: lem-trf-completed-maximal-localizations-detect-zero

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-completed-maximal-localizations-detect-zero.json`: statement retained; split into seven proof steps using existing nodes. The complete assertion is not a Mathlib leaf.
- `citations.json`: one entry for each step/node citation, quoting the cited statement verbatim.
- `searches.jsonl`: five actual msearch invocations, with the service answers inspected before recording the verdicts.
- `report.md`: this report.

No new nodes, no new Mathlib leaves, no Lean files, no unit or chapter edits.

## Attachments

None. I searched the project `lean/WeilConjectures/` by the exact blueprint id and by completed-localization/detection terminology. The nearby `AdicCompletion.completion_tensor_localMaps_injective` in `RingTheory/CompletionTensorLocalMapsInjective.lean` concerns injectivity of a completion comparison for a finite algebra, not arbitrary unbounded derived objects or the item's complete-local test-ring clauses. It does not attach this item.

## WANTED

None: the Stacks algebra, homology and derived-category sources used here are available locally.

## Findings and corrections

The item is true as stated, including the zero ring. I retained its statement and statement dependencies. Its inherited source place referred to an argument in another delivery's report, and singled out 00HN(6), which concerns bijectivity. I replaced that provenance with the actual proof inputs: 00HN(1)--(2), 00MC, 0316, 05GG, 05GI and the exact-functor argument 015F. I have not silently used a finite-generation assumption on cohomology or on the complex, and I do not assert that a single map R to a chosen completed maximal localization is faithfully flat.

I read the chapter and unit records, the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`, and the item's inherited blueprint provenance through the semidualizing-RHom-conservativity branch. This is a generic algebra input below the unit, not a replacement of a geometric step. Blueprint searches for `maximal localizations`, `completed maximal`, `completion` and `faithfully flat` found no blueprint node stating the whole item. Existing DAG nodes already state the smaller commutative-algebra and exact-functor facts; they are reused. `blueprint.same_as` is consequently empty. The inherited precise `blueprint.from.place` and `via` chain are preserved.

The five current msearch queries use the item id, and their actual answers and digests are retained. LeanFinder and LeanSearch returned local exactness criteria, module completion/tensor equivalences and flatness results; Loogle returned faithfully flat module definitions and tensor-zero reflection. The grep returned ordinary localization and adic-local-ring declarations. These explain portions of the proof, already represented by existing nodes, but no result states the whole derived detection assertion and all its test-ring properties. A second semantic phrasing was checked. The earlier item's searches are retained as history; the current searches are appended with their actual successful availability (including the formerly unavailable LeanSearch query, now successful).

## Not duplicates

No new nodes were created. In particular I did not create a maximal-localization detection node merely to quote 00HN: its annihilator proof is written out in step 6. I did not use `lem-weil-pbc-prime-localizations-jointly-injective`, whose statement is only about the ring and all primes, for detection of arbitrary modules at maximal ideals. I also did not use `lem-pc-flat-tensor-complex-cohom`, which assumes a bounded complex, for this unbounded item.

## Review by NB

I checked the split against delivery-errors B through E, with each cited node's statement open. The author of this review is the splitting worker, as required by the direct-delivery brief; the maintainer's review is independent.

For the item I read Stacks algebra.tex, `lemma-characterize-zero-local` (00HN), including the annihilator proof, and `lemma-completion-faithfully-flat` (00MC), including its Noetherian hypothesis. For completion properties I read `lemma-completion-Noetherian-Noetherian` (0316), `lemma-hathat-finitely-generated` (05GG), and `lemma-radical-completion` (05GI). I checked the Noetherian permanence lemma (00FN), the localization-flatness lemma (00HT), the proper-ideal/maximal-ideal argument in `lemma-Zariski-topology` (00E0), and the faithfully flat tensor-zero criterion in `lemma-ff` (00HP). I read derived.tex `lemma-right-derived-exact-functor` (015F), homology.tex `lemma-exact-functor` (010N), and the exact scalar-extension statements of the cited DAG nodes. There are no new nodes needing separate source audits, and no SGA source is used.

Step 1 uses `def-weil-pbc-localization-at-prime` precisely for locality and the extended maximal ideal, `lem-weil-pbc-localization-noetherian` for preservation of Noetherianity, and `lem-weil-pbc-localization-flat` for flatness. The maximal ideal is shown prime before applying these statements, and its complement is multiplicative. The local ring is nonzero because its maximal ideal is proper.

Step 2 uses `lem-weil-pbc-adic-completion-noetherian` for Noetherianity, the definition of Noetherianity to make the maximal ideal finitely generated, `lem-weil-pbc-adic-completion-mod-ideal` for completeness with respect to the extended ideal, and `lem-weil-pbc-local-completion-local-ring` for locality, identification of the maximal ideal and residue field. All these hypotheses hold for the ring A from step 1. The last residue field is nonzero, which proves B nonzero. Completeness has the actual ideal nB, not merely an unspecified topology.

Step 3 uses `lem-weil-pbc-local-completion-faithfully-flat` with the Noetherian local ring A just constructed. It then applies `lem-pc-module-flat-transitive` with the flat R-algebra A and the flat A-module B. That node is a Mathlib leaf stating precisely this change of base for a flat module; I inspected its `Module.Flat.trans` source in Flat/Stability.lean. The hypotheses do not require A to be faithfully flat over R.

Step 4 uses `lem-weil-pbc-flat-tensor-exact` for exactness of ordinary scalar extension, not just a definition of flatness. The factorization node gives the termwise derived functor; `lem-weil-pbc-exact-functor-derived-functor` identifies it as a total left derived functor; `lem-pur-derived-change-of-rings` specifies the same scalar-extension functor. This sheaf statement specializes to modules on the terminal site with its trivial topology: sheaves are just their value at the single object and all module/tensor operations are the ordinary ones. `lem-weil-pbc-exact-functor-complex-cohomology` gives the cohomology isomorphism for arbitrary complexes. Each cited statement has unbounded scope. I rejected the superficially closer bounded tensor/cohomology node because its hypothesis does not apply.

Step 5 first uses additivity of `lem-pur-derived-change-of-rings` for the forward implication. For the converse, step 4 gives vanishing of M tensor B. The two explicit pure-tensor formulas give the association/cancellation isomorphism (M tensor_R A) tensor_A B = M tensor_R B. Commuting the tensor factors allows exactly the order in `lem-sc-faithfully-flat-tensor-zero`: B is the faithfully flat A-module and N=M tensor_R A is arbitrary. No boundedness or finite generation is used here. This avoids invoking an uncited derived tensor transitivity theorem.

Step 6 is elementary from its two cited statements. I wrote both directions of the tensor/localization identification and checked the fraction relation after multiplying by the units from the denominators. The localization definition explicitly gives the criterion x/1=0 iff some element outside m kills x. If x is nonzero, its annihilator is proper, and `lem-weil-pbc-proper-ideal-contained-in-maximal` supplies a maximal ideal containing it. The resulting contradiction is the source's whole elementwise argument, not an appeal to the cited node's proof or a missing module-detection theorem.

Step 7 uses only `def-weil-abstract-derived-category`: vanishing cohomology means the map from the zero complex is a quasi-isomorphism and hence an isomorphism in the localization. The converse uses the cohomology functors already stated there. The zero-ring case is checked directly with the unital module identity x=1x=0x=0; the empty family of maximal ideals causes no exception.

For B1--B10, all new-node requirements are vacuous; the existing item preserves all imported fields and its statement. For C1 and C4, every non-elementary input is an existing node with exactly the quoted statement; `citations.json` quotes the statements without altering them. The only inline identifications are the explicit two-way fraction and tensor formulas. For D1--D5, nothing is moved into a restatement of the item's clauses; the proof steps contain the assembly and the detection argument. For E1--E7, I checked hypotheses at each application and tested R=0, a field (where m=0 and B=R), a non-domain such as k[e]/(e^2), and R=Z (where the individual map to Z_p need not detect all modules). Taking an arbitrary direct sum of shifted R-modules also confirms that no step depends on a finite degree range. All seven proof steps have fewer than 2000 characters, and none hides a non-elementary comparison lemma.

The off-unit non-leaf results are declared as generic tool uses in split_report. They are commutative algebra and exact derived functors, and no node of the geometric unit provides replacements. Definitions and existing Mathlib leaves are already permitted as tools.

## Unfinished work

None in this one-level stage-1 split. Existing dependencies keep their own status; this delivery does not claim their Lean proofs are finished. The mandatory remote dry run and push are performed after this report is written.
