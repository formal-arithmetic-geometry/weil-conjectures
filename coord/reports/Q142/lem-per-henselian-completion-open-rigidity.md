## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-completion-open-rigidity.json: reconstructed split, unchanged statement; no Mathlib match.
- citations.json: literal statement excerpts for all seven step/node citation occurrences.
- searches.jsonl: actual searches run by msearch.py, including the second semantic phrasing.
- report.md: worker report and self-review.

No new nodes, no new Mathlib leaves, no Lean files.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, the removed declaration name/module, henselian completion, Fujiwara and formal base change. No declaration states the complete item. The removed theorem attachment is historical evidence only. The pre-existing closed page-induction node is used as a tool, without changing its attachment.

## WANTED

None for this split. Read the local ILO PDF itself, physical PDF pages 379–380, printed pages 373–374. This report does not claim to have read Fujiwara's article or Bourbaki; their intermediate arguments belong to the already existing admitted lower interfaces. No source download or SGA use.

## What required repair

The released stage-1 repair note and coord/changes/20261024-Q112-strict-completion-inputs.md withdraw the old proof and explicitly admit the comparison inputs. I reconstructed a proof from their current statements, without resurrecting a historical dependency graph. The statement, source, statement dependencies, earlier recorded searches, blueprint provenance, lean_removed and lean_audit are retained. There is no statement dispute or added hypothesis.

ILO XX 4.4 displays the global comparison (*) after strictly local reduction. The admitted presentation and stalk interfaces explicitly state the general henselian-pair formulation required here, so the assembly needs neither an unproved general-to-strict-local transition nor an excellence assumption. They remain separate stage-1 obligations, not finished proofs. The arbitrary-torsion abelian version CTC is the relevant paragraph; I did not substitute the adjacent invertible-Z/nZ assertion.

## Existing interfaces and searches

Read the chapter and unit records and the latest blueprint ancestor proof, Step 3, to locate the preserved completion/purity subargument. Searched the whole DAG by the formal-base-change, henselian cohomology and admissible-modification concepts. Ran blueprint_refs ancestor, and searches for henselian completion, completion, rigidity, admissible and spectral sequence comparison. Existing nodes already supply every non-elementary input. No new node is proposed, so there are no new/existing same-tag duplicate pairs requiring a Not duplicates entry.

The item's new Mathlib searches were run through the mandated msearch.py command: LeanFinder twice, Loogle, grep and LeanSearch. All services answered. Read their returned signatures: localCohomology and its radical comparison are module local cohomology; AdicCompletion.map_exact, tensor comparison and flatness are algebraic completion facts; BDeRham/BDeRhamPlus are period rings; etale loci and StandardEtalePair lifting concern etale algebras; scheme open-restriction and pullback declarations concern scheme geometry. None compares the torsion etale cohomology groups in this item. Original search records remain untouched, and the new logged results are appended.

## Review by Q142

I checked the item against the CTC sketch in ILO XX 4.4, printed pp.373–374, including (*), (**), the paragraph beginning “Using the study”, and the dense henselian valued-field conclusion. The proof follows those reductions. I also read the current statements of every cited node and wrote literal excerpts in citations.json; no step uses a cited node's internal proof as extra output.

Step 1 uses def-weil-pbc-noetherian-ring only for its exact defining property, every ideal being finitely generated. This verifies the finite-generation hypothesis of lem-per-admissible-modification-cohomology-presentation. That node assumes precisely a henselian pair, its completion and a torsion abelian sheaf, and supplies the common topos, coefficient maps, first-quadrant spectral sequences, finite abutment filtrations and the identification of the abutment map with canonical cohomology pullback. I checked all those clauses, especially the last map identification. No separate assumption that the completion morphism is regular or excellent occurs; the presentation packages the completion ring and closed-fibre obligations in its own statement. This invocation does not use or assert noetherianity of the limit local rings.

Step 2 uses lem-per-admissible-modification-valuative-stalks, whose statement gives a conservative subfamily, compatible stalk identifications for all q, a dense inclusion of nontrivially valued fields with induced topology, henselian valuation rings, and a torsion coefficient sheaf. These are exactly the hypotheses of lem-per-dense-henselian-field-etale-comparison. The latter asserts canonical cohomology pullback isomorphisms for arbitrary torsion sheaves and all degrees, not merely an abstract Galois-group equivalence. The former explicitly identifies the stalk of our exchange map with those pullbacks. Conservativity, already supplied, then reflects these stalk isomorphisms to sheaf isomorphisms. The source for both interfaces is ILO p.374, read directly; no discretely valued, complete, constructible or prime-to-residue-characteristic hypothesis was introduced.

Step 3 applies a functor and its inverse to obtain E2 isomorphisms: no exactness or filtered-colimit preservation is claimed. I read lem-sp-page-induction and the current latest blueprint version in sec-abelian-varieties/sk-prop-av-pqf-finite, as well as the page recursion in Stacks homology.tex, Tags 011M/011N. The existing statement gives later-page and E-infinity isomorphisms. For this first-quadrant application stable pages exist because both differential endpoints leave the quadrant for r greater than max(p,q+1). This uses no uniform bound on all cohomology groups.

Step 4 cites the presentation again for compatible finite filtrations and the canonical filtered abutment map, then lem-sp-finite-filtration-induction for exactly the graded-isomorphism criterion. I read that node's statement and Stacks homology.tex Tag 0127, label lemma-characterize-strict, including its descending-induction diagram. The filtrations in each degree n have n+1 pieces, so the finite bounds required by the criterion hold. Naturality follows from the presentation's natural spectral sequences and exchange maps and the stalk interface's natural identifications; we retain the specified map throughout. The finite-filtration criterion is declared in split_report.tool_uses as a generic tool from another unit; the page-induction tool is already Lean-closed.

Small cases: I=0, or more generally nilpotent I, gives U and its pullback empty, with zero cohomology. The zero ring is included. A unit ideal can be henselian in the given idempotent-lifting sense only for the zero ring (take the finite algebra C and compare the idempotents 0 and 1 with C/I=0), so it introduces no nonzero-ring counterexample. If C is already complete, the canonical comparison is the identity. In degree n=0 the filtration has one graded piece, and the same criterion applies. The proof never restricts torsion to a fixed exponent or an invertible prime. The arbitrary nonconstructible torsion case is expressly covered by both lower comparison statements.

Against delivery-errors B–E: there are no new statement-only nodes or hollow definitions to audit; the cited definitions say exactly the notions used. All non-elementary comparisons have explicit existing nodes. No clause was moved into a new equivalent node. The proof has four steps, 2283 characters total, and no step longer than 2000 characters. No excluded direct-comparison node, SGA source or excellence-dependent substitute is cited. The only reused formerly excluded inputs are on Q112's explicit admitted list. The independent maintainer review must still assess the mathematics of these interface applications.

## Unfinished work

None within the one-level split. The existing unsplit lower interfaces remain their own items. Server dry-run and delivery results are recorded below after execution.

## Validation

The required deliver.py --no-push completed successfully: OK (not pushed), temporary delivery commit 15661520b6f, server preflight passed. This includes the server DAG and split checks and the literal citation gate. No local compiler, Lake or forbidden local preflight/check command was run. The final push is performed by the unmodified delivery tool.
