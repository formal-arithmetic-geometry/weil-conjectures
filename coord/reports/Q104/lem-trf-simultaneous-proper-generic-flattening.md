# Q104 stage-1 delivery: lem-trf-simultaneous-proper-generic-flattening

## Files written

- dag/nodes/sec-trace-formula/lem-trf-simultaneous-proper-generic-flattening.json: existing statement, now split into seven steps; Mathlib searches found no matching flattening theorem.
- citations.json: 21 verbatim statement excerpts, one for every step/node citation.
- report.md: this report. searches.jsonl records the five searches actually run in this attempt; prepare.py is sandbox-only preparation, not a delivery file.

## New nodes

None. In particular the general scheme flattening theorem already exists as lem-trf-flattening-by-admissible-blowup. Generic flatness, Noetherian topology, coproduct existence, and the blowup's isomorphism over its admissible open are also already nodes. The two short clopen restriction arguments are steps, not additional nodes. There are zero new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact item id and for generic flatness, flattening, flatification, and strict transforms. Existing generic-flatness declarations give an open restriction, not the flattening blowup. Compactification/EliminationOfIndeterminacy.lean and Blowup/AdmissibleBlowup.lean explicitly explain that their proofs bypass flattening and provide no such theorem. No declaration states the whole item.

## WANTED

None: the Stacks sources used are present locally.

## Changes and issues found

The original proof was empty. The statement cited def-weil-pbc-noetherian-ring for a Noetherian scheme, although that node defines only rings. I expanded the standard meaning of Noetherian scheme as locally Noetherian and quasi-compact, citing pqf-def-locnoeth and def-weil-pbc-quasi-compact-scheme. This is a definition/citation clarification, not a changed mathematical hypothesis; every conclusion is retained. I added the existing scheme-coproduct statement dependency because the statement includes the disjoint union. No statement dispute, counterexample to the item, or departure from the prescribed route was found.

I retained all prior search records, source references, provenance and blueprint via entries. Current searches are additionally recorded exactly as run. Two different semantic searches returned only flatness definitions and permanence properties; Loogle found no strictTransform declaration, and the Mathlib/AlgebraicGeometry grep found no strict-transform, flatification or flattening occurrence. These were successful searches, not unavailable services. The returned Flat definitions and permanence statements were read; none constructs a blowup.

## Blueprint and duplicate search

Read the chapter sec-trace-formula and unit sk-i-curve-zero records, the current main-20261015 ancestor lem-trf-local-term-locality, and the parent's existing split. The parent lem-trf-flatification-horizontal-curve-pair Step 1 requires exactly this simultaneous preparation, within its recorded semistable-alteration chain, before stable modification in ILO X Theorem 3.4 Step 2. No unit or chapter record is changed.

Searched all dag/nodes for 081R, 052A, 080D, generic flatness, and coproduct/strict-transform statements. tools/blueprint_refs.py searches for flattening, 081R, 052A, simultaneous, and disjoint union found no second blueprint statement of this item. The 081R elimination node assumes the family is an isomorphism over its open and concludes only an open immersion of the transform; it is not this simultaneous proper-family statement. The more general existing scheme flattening node is used, not duplicated. blueprint.same_as remains [].

## Not duplicates

No new nodes and hence no new/existing shared-tag pairs.

## Review by Q104

I read flat.tex, lemma-flat-after-blowing-up (081R), including its hypotheses and finite-presentation conclusion, and morphisms.tex, proposition-generic-flatness (052A). I read divisors.tex, definition-strict-transform (080D), as a scheme/ideal construction rather than topological closure. For the supporting steps I read properties.tex definition-noetherian (01OV), lemma-locally-Noetherian-quasi-separated (01OY), lemma-Noetherian-topology (01OZ); morphisms.tex lemma-finite-type-noetherian (01T6); topology.tex lemma-Noetherian-quasi-compact (04ZA); schemes.tex lemma-glue and lemma-glue-schemes (01JB/01JC), and the quasi-separatedness criterion. There are no new-node sources to review. I opened the statement of every cited DAG node and checked the exact hypotheses and conclusions below.

Step 1 uses the scheme-coproduct node for existence and the disjoint clopen cover. The proper-morphism definition includes finite type. The finite-type definition gives finite affine covers above each affine base open; combining two such covers proves finite type of the union, without assuming an unrecorded theorem on proper coproducts. This short argument is elementary.

Step 2 uses finite-type-over-Noetherian to make W Noetherian, locally-noetherian-quasi-separated for both W and S, and qcqs-morphism-permanence (1) to make W to S relatively quasi-separated. That last node explicitly supplies relative quasi-separatedness from the source's quasi-separatedness. S is quasi-compact by the clarified Noetherian hypothesis. This checks all the scheme-level compactness hypotheses, without silently assuming S is separated.

Step 3 uses generic-flat-finite-presentation with the integral base and finite-type g from Step 1. Its statement supplies both flatness and local finite presentation on a nonempty open, without requiring a nonempty source. The Noetherian closed-subset minimality node supplies a minimal member among the terms of every descending closed chain, forcing that chain to stabilize and hence giving the Noetherian topology; the compact-subsets node makes U quasi-compact. Both cited statements actually give these implications, so no implicit Noetherian-to-topological theorem is missing.

Step 4 invokes the existing general scheme flattening node only after checking each of its assumptions: S is qcqs; g is finite type and quasi-separated; U is quasi-compact; and the restriction is flat and locally finitely presented. Its statement gives the finite-type quasi-coherent ideal unit on U, the admissible blowup, flat finite presentation of W', and the schematic-closure identification. It does not merely define flattening. The blowup chosen here is common to both families.

Step 5 uses the scheme-coproduct node for the clopen decomposition. In this repair I also checked the kernel caveat in the current scheme-image statement: the literal kernel is quasi-coherent for a quasi-compact immersion. Step 3 makes every V intersected with an affine base open quasi-compact; the finite-type definition therefore gives quasi-compactness of V to S, and qcqs-morphism-permanence (3) gives it for the base-changed open immersion. These two newly explicit Step-5 citations state exactly those criteria. Pulling the two opens back gives a disjoint clopen cover of the fibre product, hence its coproduct by the same mapping property. The scheme-theoretic-image definition supplies the kernel ideal and closure convention; the strict-transform definition identifies the individual closures. Restriction to each clopen component is literally restriction of that same sheaf map and of its kernel, so the two closure ideals are the restrictions of the whole ideal. Thus the argument proves the coproduct identity scheme-theoretically, including nilpotents. It is not an appeal to the proof of a cited theorem and introduces no hidden comparison lemma.

Step 6 checks flatness and local finite presentation on identical local rings and affine neighbourhoods of clopen summands using their definitions. Relative quasi-compactness follows because the summand above an affine base open is a closed subset of the quasi-compact whole. The relative diagonal is the indicated base change of the whole diagonal; qcqs-morphism-permanence (3) explicitly preserves quasi-compactness under that base change. The quasi-separated definition then supplies relative quasi-separatedness. These are the three ingredients of finite presentation. No unsupported claim that arbitrary source restrictions preserve quasi-compactness is used: closedness of this restriction matters.

Step 7 uses admissible-blowup-over-open with the same ideal on V, not merely on U. The ideal is unit there by the definition of its vanishing locus, and V is quasi-compact by Step 3, so this is legitimate V-admissible data. The lemma supplies the isomorphism over V. On that open the closure-kernel map restricts to an identity and has zero kernel, giving the original families. No new non-elementary fact is hidden here.

Checked B1--B10: no new nodes, no unintroduced new objects, correct TeX and tags, honest logged searches, preserved blueprint ancestry, and no false Lean attachment. Checked C1--C8: all non-elementary inputs have cited nodes, all 21 excerpts are verbatim substrings, no proof-only constructions are borrowed, and generic tools outside the unit are declared in split_report.tool_uses for maintainer review. An explicit read-only graph traversal found no path back to the item from any nontrivial proof dependency. Checked D1--D5: no clauses relabelled as new nodes and no argument outsourced to a restatement; the coproduct and kernel calculations are written in the proof. Checked E1--E7: finite type, qcqs, integrality, and admissibility hypotheses match, and closures are scheme-theoretic.

Small cases: if one or both X_i are empty, the affine covers may be empty, g still has finite type, and the generic-flatness node still gives a nonempty open because S is integral and nonempty. Empty summands and their closures remain empty. If a family is entirely vertical, its strict transform may be empty; no surjectivity is claimed. If S is a field spectrum, the open is S and the unit ideal gives the identity blowup; proper finite-type schemes over a field are flat. Disconnected/reducible or nonreduced total spaces are allowed, and the componentwise kernel proof makes no integrality assumption on them. No excellence is required. Every proof step is under 1200 characters, so none meets the long-step threshold.

## Unfinished work

No missing part of this split. Existing unsplit dependencies retain their own future stage-1 tasks. No Lean was written and no compiler or build tool was run.

## Validation

The required deliver.py dry run and final delivery are run after this report; their tool output is the authoritative validation record.

## Repair of the landing return (2026-10-23)

The returned immutable head is 7fe71b567a3. Its retained sandbox contains the approved seven-step proof; the current repository item is still unsplit with an empty proof. I compared the retained item with that current node: its title, source, created metadata, chapter, unit and blueprint ancestry agree. The retained changes are the seven proof steps and their dependencies, the precise Noetherian-scheme definition citations, the preserved additional search records, and the split report. I retain those changes. The required delivery tool rebased the delivery onto its current server base and its initial dry run passed at 73db6eded7b.

I re-read all 20 distinct statement/proof dependency nodes in the current DAG, rather than relying on the older citation excerpts alone. Every cited statement remains available and unmerged; each of the 19 retained excerpts is still verbatim. In particular, generic-flat-finite-presentation still requires only finite type over an integral base; scheme flattening still has exactly the qcqs, finite-type, quasi-separated and generic-flat-presentation hypotheses checked in Steps 1--3. The proper and finite-type definitions, finite-type-over-Noetherian result, locally-Noetherian quasi-separatedness, topology statements, coproduct statement and admissible-blowup-over-open statement all supply the same inputs. All statement-only definitions are read for their actual data, not their proof. The complete current statement snapshots are recorded in sandbox-only rebase-audit.json.

This is a substantive proof repair as well as a rebase: Step 3 now writes the minimal-member argument that supplies the descending-chain hypothesis of the compact-subsets lemma. Step 5 now checks the quasi-compactness proviso of the current scheme-image definition before identifying the literal kernel, using the finite-type definition and the existing base-change permanence statement. Its citation quote now includes that proviso; the two additional step/node pairs make 21 citation entries. No new node or search question is introduced, so the logged searches are retained without repetition. I re-read Stacks 081R, 052A and 080D and the relevant Noetherian definitions; the source route and all item conclusions are unchanged.

I checked B--E again against the repaired steps: no new-node duplication or statement issue, no unsupported non-elementary input, no use of a cited proof instead of its statement, no implicit proper-coproduct theorem, no extra separatedness or excellence hypothesis, and no replacement of schematic closure by topological closure. Empty sources, entirely vertical sources, identity blowup over a field, and nonreduced total spaces still pass the arguments. The longest repaired step is below 1200 characters. The final dry run and push follow this report.
