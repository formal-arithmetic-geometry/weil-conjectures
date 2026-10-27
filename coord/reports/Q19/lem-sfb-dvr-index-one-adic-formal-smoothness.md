# Q19 stage-1 delivery: lem-sfb-dvr-index-one-adic-formal-smoothness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-index-one-adic-formal-smoothness.json`: existing statement, now split into three steps; not a Mathlib match.
- `citations.json`: seven verbatim quotation entries, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` was produced by the required msearch command.

There are zero new nodes and zero new Mathlib leaves. The item statement and statement dependencies are unchanged; its original searches and provenance are retained. No repository, launcher, Lean or unit file was written, no git command was run, and nothing was compiled.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for index-one, ramification-index-one, weakly unramified, DVR and formal smoothness found uses of this mathematical criterion in other docstrings, not a declaration proving this item with all its hypotheses. The general lifting and local-fibre facts are cited through their existing DAG nodes, rather than claimed as an exact Lean attachment.

## WANTED

None. All mathematical sources used are present under `literature/stacks-project/`.

## What was wrong or missing

The imported item was statement-only. Its source, Stacks 09E7, proves the implication by citing 07NQ and 0322, and the two corresponding general facts already exist in the DAG. There is no statement dispute: injectivity, locality, the equality of extended maximal ideals, and separability in the potentially transcendental sense are sufficient. No completeness, finite generation, algebraicity, excellence, or finite-presentation assumption has been inserted.

The inherited Mathlib search verdict claimed too broadly that the relevant field formal-smoothness statements require essential finite type. Reading the current `Smooth/Field.lean` shows that `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` (line 44) has no such assumption: it applies to a *separably generated* field extension. This still does not cover every separable extension in the item's finite-subextension sense. I corrected the verdict text while preserving all inherited queries and their result records, and added actual Q19 queries and their logged results. `Algebra.FormallySmooth.of_perfectField` (line 53) does require `EssFiniteType`. The residue-field criterion in `Unramified/LocalRing.lean` also assumes `EssFiniteType` and concludes formal unramifiedness, so it cannot be substituted for adic formal smoothness. `Smooth/AdicCompletion.lean:93` lifts a map from an already formally smooth algebra into a complete ring; it supplies no missing DVR criterion.

The current blueprint is the `latest` link, whose commit is ef6f9619fdbffa59e88528fb56483d76c70258c8. I read its ctf-stability unit and direct-images proof (3), together with the recorded chapter and unit. The historical Epp coefficient-DVR argument is no longer written in that proof. I retained the item's existing null blueprint ancestor and its historical provenance chain and made that limitation explicit in the split report. There is no claim that a current blueprint statement is identical to this supporting lemma. Searches through `blueprint_refs.py` for 09E7, index-one and weakly unramified returned no matching blueprint node. Broad formal-smoothness/adic searches yielded general tools rather than another statement of this DVR implication.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. I reused `lem-weil-pbc-pid-torsion-free-module-flat`, `lem-sfb-separable-field-square-zero-lifting` and `lem-weil-pbc-flat-formally-smooth-closed-fibre-adic`. In particular I did not create another 07NQ or 0322 node, a closed-fibre identification node, a torsion-freeness node, or a node restating the item's conclusion.

## Review by Q19

I read the actual source statement and proof of Stacks 09E7 (`more-algebra.tex`, `lemma-extension-dvrs-formally-smooth`), the equivalence in 07NQ (`proposition-fs-flat-fibre-fs`), and 0322 (`algebra.tex`, `proposition-characterize-separable-field-extensions`). The tag/label pairs were checked against `tags/tags`. For the additional flatness explanation I read 0AUW (`lemma-dedekind-torsion-free-flat`), which explicitly covers a DVR or a PID and states flatness iff torsion-freeness. I read the existing Mathlib leaf's source `Flat/TorsionFree.lean:93` as well. There are no new-node sources to review.

For step 1 I opened the *statements* of `def-sc-discrete-valuation-ring`, `def-weil-pbc-noetherian-ring` and `lem-weil-pbc-pid-torsion-free-module-flat`. The first supplies local domains and principal ideals; the second defines Noetherianity by finite generation of all ideals; the third accepts an arbitrary torsion-free module over a PID, with no finite-generation hypothesis. The step explicitly proves Noetherianity and torsion-freeness: if a nonzero scalar kills an element of S, injectivity makes its image nonzero and the domain property forces that element to vanish. Thus the flatness theorem is applied with exactly its hypotheses. No false assertion that every torsion-free module is free is used.

For step 2 I opened the *statements* of the closed-fibre criterion, the separable-field square-zero lifting theorem and the adic formal-smoothness definition. The first actually defines its closed fibre as the quotient S/m_R S; the equality of ideals in the item's hypothesis therefore gives precisely S/m_S. The induced k-algebra map sends [r] to [phi(r)], and locality makes it an embedding of residue fields. The quotient identification is [s] to [s], so it preserves this structure. Its maximal ideal is zero. The field-lifting node explicitly covers arbitrary separable extensions, neither only algebraic ones nor only separably generated ones, and supplies lifts for *every* square-zero test. That implies the adic lifting condition for the zero ideal directly. No completion or theorem about transporting derived objects is hidden in this identification.

For step 3 I again read the entire *statement* of the closed-fibre criterion: it assumes a local map of Noetherian local rings, flatness and formal smoothness of the quotient closed fibre, and concludes exactly maximal-ideal-adic formal smoothness of the upper ring. Locality is a hypothesis of the item, the Noetherian and flat conditions are proved in step 1, and the exact fibre/topology condition is proved in step 2. This is the source's 07NQ (2) to (3), not another result inferred from the proof of a cited node. The only non-leaf off-unit proof citation is this generic local-algebra tool; `split_report.tool_uses` explains why it is needed. The PID flatness result is already a Mathlib leaf, and the separable-field lifting node is in this unit. I traversed the dependencies of all three results and verified that none depends on this item.

As edge checks, the identity of any DVR gives its own residue field and satisfies every step. The examples k[t]_(t) to L[t]_(t), and k[[t]] to L[[t]], for separable L/k verify that the argument does not use completeness and does not assume finite residue degree. An arbitrary infinite separable residue extension is accepted by the field-lifting node's statement; I did not replace it by an assertion about separable algebraic or globally separably generated extensions. For t mapping to u^e with e > 1, the equality of ideals fails and the closed fibre is L[u]/(u^e), not L; the proof correctly cannot make its crucial identification. A purely inseparable nontrivial residue extension likewise cannot pass the separable lifting step. Fields themselves are excluded by the DVR definition, and no proof step attempts to choose a nonexistent nonzero uniformizer in a field.

Against delivery-errors B through E: the item remains self-contained and retains all three definition dependencies; sources have checked Stacks tags and labels; the seven citations are verbatim substrings of the cited statements; every non-elementary fact is one of those statements; all three steps are marked non-elementary; no new node is elementary, duplicated, a clause of the item or a disguised whole proof; no step exceeds 2000 characters (lengths 517, 921, 494); no source proof or mere tag is used as an uncited black box. The remaining quotient and domain calculations are written in the steps. Every used result has its hypotheses explicitly verified above. No statement correction or source error was required.

## Unfinished work

None in the stage-1 split. Required server dry run and direct delivery are performed after writing this report; their terminal result is reported to the dispatcher.
