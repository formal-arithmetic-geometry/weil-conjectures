# Stage-1 delivery: lem-trf-flat-module-presentation-after-boundary-blowup

## Files written

- dag/nodes/sec-trace-formula/lem-trf-flat-module-presentation-after-boundary-blowup.json: statement, split; no Mathlib match. Four proof steps assemble six existing nodes. Statement and statement dependencies retained exactly.
- citations.json: seven verbatim statement quotations, one for each step/dependency pair.
- report.md: this report. Searches are recorded by msearch.py in searches.jsonl.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and the finite-type/flat-module/presentation and strict-transform notions found no declaration proving every clause. The blowup source explicitly says its Nagata route does not formalize module flattening. Existing properness, Cartier-boundary and admissibility results alone do not attach this item.

## WANTED

None. All mathematical sources used are present in literature/.

## Problems found and decisions

The seeded node was an unsplit statement with no proof. Its statement is correct. No statement dispute, source correction, or route replacement was necessary. In particular, neither X nor X times_S T needs to be quasi-compact: Tag 081N is local and imposes no such hypothesis. The stronger quasi-compact-X hypothesis in the full flattening theorem 0815 belongs to the flattening argument, not to this final finite-presentation step.

The boundary ideal is arbitrary after its existence is established. I did not use lemma-nagata-conrad-dense-in-admissible-blowup: its statement assumes U dense in S, which the item does not assume. The existing det-nagata-boundary-divisor-cartier gives schematic density without that extra hypothesis. The source remark's phrase referring to the support as X minus U is an evident variable typo; the item already correctly uses S minus U.

The existing lemma lem-trf-module-strict-transform-flat-pullback concerns compatibility with flat changes of blowup squares; it is not the assertion that a relatively flat module has ordinary pullback as its strict transform. I instead use exactly clause (2) of lem-trf-module-admissible-blowup-calculus, which states the latter assertion and all its required permanence properties.

Existing item search records, including an invalid historical Loogle query, were preserved. Fresh actual leanfinder, loogle, grep, and leansearch runs are appended. A second semantic phrasing was also run. Search hits concern definitions, morphism finite presentation, and permanence; the module finite-type-implies-finite-presentation hit requires a Noetherian ring. None states the item under its hypotheses. I read the relevant Mathlib Quasicoherent.lean finite-presentation definitions and the returned types rather than treating these as matches.

## Unfinished work

None within the one-level stage-1 scope. Existing dependency nodes retain their own stage status. No Lean was written and no compiler, Lake, or build tool was invoked.

## Blueprint and duplicate searches

Read the chapter record sec-trace-formula and unit sk-i-curve-zero. The item is not the key node of that unit, so no unit record is changed. Its inherited ancestor and via chain lead through the semistable-alteration/flattening input of lem-trf-local-term-locality. The proof follows the seeded Stacks 0815/080Y/081N route without altering either chapter or unit.

Searched the entire DAG for the relevant tags, literature labels, finite-type flat modules, boundary ideals and strict transforms, and used blueprint_refs.py ancestor and search (flat finite type; boundary divisor; finite presentation). The existing dense-presentation, boundary-divisor and blowup-calculus nodes supply all non-elementary inputs. No new node is justified. The blueprint same_as remains [] because none states the full combined assertion with arbitrary boundary ideal and global finite presentation.

## Not duplicates

No new nodes. All six proof dependencies reuse existing statements; no elementary step, clause of the item, or special case of an existing statement was made into a new node.

## Review by Q01

I read Stacks flat.tex Tag 0815 (theorem-flatten-module), especially its final paragraph, Tag 080Y (remark-successive-blowups), third paragraph, and the complete statement of Tag 081N (lemma-flat-finite-type-finitely-presented-over-dense-open). I also read properties.tex Tag 01PH (lemma-quasi-coherent-finite-type-ideals), divisors.tex Tag 02OS (lemma-blowing-up-gives-effective-Cartier-divisor), Tag 07ZU (lemma-complement-effective-Cartier-divisor), and Tag 080F (lemma-strict-transform-flat), including their relevant proofs. There are no new nodes whose source needs separate review.

Step 1 cites lemma-nagata-qc-open-complement-ideal-exists for exactly existence of a finite-type quasi-coherent boundary ideal; S is qcqs and U is quasi-compact as that statement requires. It then cites det-nagata-boundary-divisor-cartier for admissibility and schematic density for ANY such ideal. Its statement explicitly gives those two conclusions, not merely topological density or existence of some other blowup. No density assumption on U in S is used.

Step 2 cites clause (2) of lem-trf-module-admissible-blowup-calculus. I checked its statement gives the canonical strict-transform/ordinary-pullback identification for a relatively flat module, flatness over T, quasi-coherence, finite type, agreement over U, and qcqs of T. The qcqs and quasi-compact-open hypotheses and the specified centre are all retained. This avoids confusing relative flatness of the module with flatness of X over S, which is not a hypothesis.

Step 3 cites lemma-nagata-admissible-blowup-over-open for its stated isomorphism of the inverse image of U with U. It cites clause (1) of lem-weil-pbc-qcqs-morphism-permanence to make the inclusion U_T into T quasi-compact, using quasi-compactness of its source and quasi-separatedness of T. The remaining finite-affine-cover argument is written out to obtain retrocompactness for every quasi-compact open, not merely affine opens. No intersection of affine opens is assumed affine.

Step 4 cites clause (3) of the same permanence statement for local finite presentation of q, with no quasi-compactness assumption on f. The isomorphism over U identifies precisely the restriction of the module on the full fibre product with the given finitely presented module. I checked every hypothesis of lem-trf-flat-finite-type-dense-presentation against Steps 1--3: local finite presentation of q, finite-type quasi-coherence and relative flatness of the module, retrocompact schematic density of U_T, and finite presentation on its inverse image. Its statement concludes finite presentation on ALL of Y, exactly the needed conclusion. All seven uses have verbatim quotations in citations.json.

For B1--B10, there are no new-node format, source, or Mathlib-leaf obligations to evade; the item retains its TeX, inherited provenance, statement and maintainer fields, and has recorded actual searches and blueprint references. For C1--C8, all non-elementary facts have explicit statement citations, all cited files were opened, and a read-only dependency traversal found no path from any of the six dependencies back to the item. The three off-unit Nagata statements are declared in split_report.tool_uses as generic tools; the qcqs permanence node is already a Mathlib leaf. For D1--D5, the proof assembles existing smaller ingredients and does not move any clause into a new node, cite a source in place of an argument, or depend on a proof-only construction. The four steps total 2165 characters, none exceeding 2000, and hide no new lemma.

For E1--E7 I checked hypotheses, objects, and boundary cases. In this self-review I corrected my preliminary tag number 0804 to the actual tag 02OS for lemma-blowing-up-gives-effective-Cartier-divisor, checking the local tag table. If U=S, its complement is empty and the blowup is an isomorphism; the conclusion reduces to the assumed finite presentation. If U is empty, a finite-type boundary ideal has full vanishing locus, hence is locally nilpotent; its blowup is empty, so all conclusions are vacuous. Empty S or X and the zero module also satisfy the argument. A disconnected S with U missing components causes no failure: the boundary blowup can remove those components. On a non-Noetherian base I use 081N, not the false claim that finite type alone implies finite presentation. The same specified ideal is used throughout, and no coefficient category, scheme strict transform, or support-only finite-presentation assertion is substituted for the module on X times_S T.
