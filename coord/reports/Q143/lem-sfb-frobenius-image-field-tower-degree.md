# Stage-1 report: lem-sfb-frobenius-image-field-tower-degree

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-image-field-tower-degree.json: statement node, now split into five steps; no whole-item Mathlib match. The existing mathematical statement is retained, with an explicit reference for its basis notion.
- citations.json: eight step/node entries, with verbatim quotations of the cited statements.
- No new nodes and no new Mathlib leaves. No unit record was changed: this auxiliary item is not the unit's key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for Frobenius with basis, finrank and degree. FieldTheory.frobenius_basis_compositum in FieldTheory/FrobeniusBasisCompositum.lean concerns the span of powers over an intermediate scalar field, explicitly does not assert independence, and does not state the tower formula. Read its statement and proof opening. It cannot attach this item. Other hits concern finite-field Galois operators, cohomology and Frobenius forms rather than this arbitrary-field tower.

## Literature

No WANTED sources. Read Stacks fields.tex, Tag 09G9 (fields-lemma-multiplicativity-degrees), its statement and entire basis proof; Tag 09FU (fields-lemma-field-maps-injective), its statement and inverse-element argument; varieties.tex, Tag 03SM (varieties-definition-absolute-frobenius), especially the following ring-Frobenius paragraph; and Tag 0CCG (varieties-remark-n-fold-relative-frobenius), its iteration formulas. Checked the tag/label correspondences in tags/tags. The sources provide the ring map, coefficient-expansion method and tower law; they do not state this exact imperfect-field basis refinement verbatim, so proof_origin is honestly agent.

## Changes and issues

At the original split there was no earlier item copy or report in the sandbox; this repair retains that original work, including its proof, citations and search log. The repository item was unsplit and had no Lean audit entry giving a completed declaration. No released repair note for this id was present. Read the chapter sec-six-functors-basics and the unit sk-thm-sf-ctf-stability; this item serves the algebraic refinement already specified by its inherited blueprint.from.place, through the smooth-curve relative-Frobenius degree node. The unit record historically has chapter sec-six-functors, whereas the item's chapter is sec-six-functors-basics; neither record was altered. blueprint_refs.py ancestor returns None for this inherited ancestry, so its null from.node and via chain are retained, with a specific existing place. Searches of the imported blueprint for Frobenius image, field tower, multiplicativity, ring Frobenius and basis found no blueprint statement of this lemma. same_as remains [].

No statement dispute, omitted hypothesis or weakened conclusion was found. Added def-weil-pbc-free-module to stmt_deps because the original statement used a basis without explicitly citing the definition. The statement's field, characteristic, extension and degree dependencies remain. No dependencies were removed. No Lean was written and no compiler, Lake or build command was run.

## Mathlib and duplicate searches

Ran the prescribed msearch.py commands, whose exact queries and result summaries are recorded in the item's mathlib_searches and the sandbox searches.jsonl. Used LeanSearch, Loogle, LeanFinder with two whole-item phrasings, and grep in FieldTheory. The preliminary injective-Frobenius search also found iterateFrobenius_inj and injective_frobenius; that part requires no new node because the elementary inverse-element argument is written in step 1.

Read Mathlib/FieldTheory/PurelyInseparable/Basic.lean:322: IsPurelyInseparable.finrank_eq_pow only asserts existence of some prime-power exponent. Read PerfectClosure.lean:376: Module.Basis.mapPowExpCharPowOfIsSeparable requires Algebra.IsSeparable and gives powers as a basis over the unchanged scalar field. Our Frobenius-image tower changes scalars and includes nontrivial purely inseparable extensions, so this is not a one-line specialization. The LeanSearch hits for semilinear iterateFrobenius describe the map, not the basis and degree formula. No service failure was recorded as mathematical absence.

Searched the whole DAG by tags 09G9 and keywords Frobenius, ring, basis, tower law, degree multiplicativity and basis transport. Reused def-weil-ring-frobenius, def-weil-pbc-free-module, def-weil-vector-space-dimension, def-pc-field-tower and lem-weil-pbc-field-degree-multiplicativity. The last is already a Mathlib leaf, including finiteness transitivity, so no new tower-law or basis-transport node is warranted. All cited dependencies are either definitions or Mathlib tools; no off-unit non-leaf theorem is used.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish.

## Review by Q143

I read the sources listed above with the item and the cited JSON statements open. For this item the critical point is that alpha_i has codomain its image L_i, rather than all of K: surjectivity onto the image requires no perfectness. The hypothesis p prime and characteristic p gives the ring endomorphism in def-weil-ring-frobenius. Step 1 takes precisely that ring-homomorphism assertion from its statement and writes the remaining injectivity and image-field argument. The zero-ring issue in that node is irrelevant here because def-weil-field explicitly requires 0 != 1. In particular the inverse used in step 1 exists.

Step 2 uses only exponent identities, with both containments in alpha_i(L_1)=L_{i+1} explicit. It also proves the descending inclusions needed before applying the tower law. Step 3 takes from def-weil-pbc-free-module the unique finite coefficient expansion and applies a ring homomorphism to a finite sum, with coefficients now in L_{i+1}. Step 4 lifts every relation coefficient using the already proved scalar-image equality, pulls the relation back by injectivity, and uses the same basis statement's uniqueness to force each coefficient to vanish. The statements of def-weil-vector-space-dimension and def-pc-field-tower then say exactly that the resulting finite basis has cardinality equal to the extension degree. None of these steps cites a node's proof. Steps 1--4 are short direct calculations from the cited statements, rather than hidden transport lemmas or new restatements of the item's clauses.

Step 5 invokes the exact statement of lem-weil-pbc-field-degree-multiplicativity: both adjacent extensions are finite, the induction supplies K/L_n and step 4 supplies L_n/L_{n+1}. That node explicitly gives finiteness of the composite as well as its degree, so there is no missing finiteness inference. The base case uses the singleton basis of K over K and the dimension definition. The induction claim, base and step are all stated. No step exceeds 2000 characters. The entire assembly proof is below 3000 characters.

For small cases I checked i=0 (identity map, original basis), n=0 (degree one), and d=1 (all tower degrees one, including finite/perfect fields). I also checked K=F_p(t): L_i=F_p(t^(p^i)), the usual basis 1,t,...,t^(p-1) maps to 1,t^(p^i),...,t^((p-1)p^i), and the degrees are p and p^n. This imperfect example tests the scalar fields and rules out an accidental use of surjectivity K -> K. In a nonzero field d=0 cannot occur, since K over L_1 contains 1. There are no new statements requiring further small-case checks.

Against delivery-errors B--E: the source tags and labels were checked; basis notation now has its definition; no new statement-only or leaf metadata is needed; every non-elementary use is the existing tower-law node; every quotation is copied verbatim; the proof performs the coefficient calculations rather than moving clauses to new nodes; the hypotheses on characteristic, nontriviality and finite degrees are checked where used. No mathematical correction was necessary beyond adding the missing notion reference. No second worker was used, as required by this direct-delivery brief.

## Repair of the promotion return (2026-10-23)

The return names delivered head 629038e061c and says that the reader approved the split but the landing refused the side-project completion because the live DAG still had an unsplit item. This is the only return point for this item. I compared the returned commit's node blobs with the current read clone without running a git command. The retained sandbox item was exactly the returned item's JSON; the current live item has the original unsplit statement-only node. The differences are precisely the split-owned statement reference, statement dependencies, proof, proof dependencies, proof origin, searches, status and split report. No changed maintainer metadata was copied back.

All eight statement/proof dependencies have identical blobs at the returned head and in the current DAG: def-weil-field, def-pc-field-characteristic, def-pc-field-extension, def-pc-field-tower, def-weil-pbc-free-module, def-weil-ring-frobenius, def-weil-vector-space-dimension and lem-weil-pbc-field-degree-multiplicativity. I reread every current statement nevertheless. The comparison is saved locally in repair-comparison.json. The delivery tool's first repair dry run fetched origin/sheaf-dag, built a fresh commit ed4fc39bcb1 and printed OK (not pushed), confirming that the retained split remains admissible over the current DAG.

I then adjusted step 1 to spell out how the zero-kernel argument proves injectivity for arbitrary x,y, and step 5 to cite explicitly both the dimension and degree definitions in the singleton-basis base case. The latter adds a verbatim step-5 quotation of def-pc-field-tower to citations.json; proof_deps already included it. No mathematical statement or route changes, new nodes, new Mathlib leaves or repeated searches were needed. The statements and search questions have not changed, and I read the retained searches.jsonl and the pertinent Mathlib candidates before preserving those searches. The final dry run and push use the official delivery command, which rebuilds on current origin/sheaf-dag and retains maintainer-owned fields.

For my repair review under the signature above: step 1 uses precisely the iterated ring-endomorphism assertion and the field's nonzero-unit axiom; step 2 computes the two image containments; steps 3 and 4 use unique basis expansions, with coefficients lifted through the proved scalar-image equality; step 4 reads degree as finite basis cardinality; step 5 uses both definitions for the base and the tower-law node's explicit finiteness and multiplication assertions for the induction. No citation takes a conclusion absent from the cited statement. I rechecked n=0, i=0, d=1 and the imperfect field F_p(t). Every step remains shorter than 2000 characters. The retained assembly remains shorter than 3000 characters. No SGA source, Lean write, compiler, Lake command, repository write or launcher edit was used.

## Unfinished work

None within stage 1. The final server dry run and direct delivery follow this report update.
