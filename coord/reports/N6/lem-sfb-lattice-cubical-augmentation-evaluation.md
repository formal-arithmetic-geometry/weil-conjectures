# Stage-1 delivery: lem-sfb-lattice-cubical-augmentation-evaluation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-lattice-cubical-augmentation-evaluation.json — statement, split; seven explicit proof steps. Mathlib verdict: no exact match.
- citations.json — verbatim statement quotations for every proof-step citation.
- searches.jsonl — actual msearch.py results, retained unchanged.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compiler invocations or repository writes.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and cubical, lattice contraction, Koszul evaluation and augmentation/evaluation notions. The Koszul top/dual evaluation results there concern scheme/ring Koszul models, not this internal lattice statement. Read the related parent docstring in lean/Sheaf/CategoryTheory/LatticeKoszulTriangulatedCupComparison.lean, steps 7–8: it explains the required sign formula but is not a finished attachment of this item.

## Literature and WANTED

Read the current blueprint main-20261015 direct-images proof, paragraph (3), named in the item. It supplies the ordinary open-direct-image route; it does not claim this entire structural calculation. Read Stacks more-algebra.tex, Tag 0623, definition-koszul-complex, for the underlying Koszul convention. The actual contracting homotopy is supplied by the existing integral-contraction node, whose full statement was read; no regular-sequence theorem or implicit projectivity claim is used.

WANTED: a published reference for this exact internal condensed-module cubical augmentation and signed evaluation calculation, for lem-sfb-lattice-cubical-augmentation-evaluation. The explicit proof is marked agent-written, rather than attributing its Hom signs or homotopy to a Stacks lemma that does not state them.

## What needed repair

The seeded item had no proof. Its statement and hypotheses are retained. In particular the contraction is only nonequivariant: the proof does not claim that h or s commutes with translation. K-flatness is proved by tensoring this contraction and detecting acyclicity after forgetting the action; this avoids assuming that arbitrary equivariant free terms are projective, or that sectionwise tensor computes internal tensor.

The blueprint ancestor tool prints None for this inherited chain. Retained its existing blueprint.from.node=null and via chain, filled same_as=[], and recorded the exact paragraph and parent steps in split_report.blueprint. No change to maintainer-owned ancestry metadata.

## Searches and reuse

Ran the prescribed leanfinder, loogle, grep and leansearch commands through msearch.py and read every hit. The second leanfinder phrasing separates the Hom differential and tensor-homotopy aspects. The HomComplex results are general differential identities, not the prescribed signed internal lattice evaluation; Rep.standardComplex and inhomogeneousCochains have different bar models and ordinary representations. Read the Mathlib HomComplex differential and representation-resolution source to verify this distinction. Retained the item's previous search records and added only actual newly logged queries. All services returned results; the cubical/Koszul-evaluation grep returned no hits.

Searched the whole DAG by cubical, K-flat, tensor acyclicity, internal tensor comparison, coproduct exactness and Hom evaluation notions. Ran blueprint_refs.py search for cubical, Koszul and homotopy, and ancestor for the item. Existing lem-pe-internal-section-tensor-comparison gives the exact arbitrary-small-site tensor dictionary needed here. Existing bounded-flat criteria were considered but are unnecessary, since the tensor contraction proves the stronger direct homotopy-equivalence assertion. No new lemma is created for a clause of this item or for elementary finite matrix/sign calculations.

## Not duplicates

No new nodes. The seven steps use existing integral contraction, Koszul, tensor and action infrastructure.

## Review by N6

I read the item source and the full statement of each cited node with the proof open. In step 1 the integral-contraction node supplies all four identities and explicitly permits nonequivariant h and s. An abelian-group homomorphism out of a free direct sum has finite support on each basis vector, so replacing each integral coefficient by its image in R constructs genuine internal maps by the coproduct property. This is an explicit construction; no unknown object or unsplit internalization lemma is substituted. The internal-module and action definitions specify exactly the linearity and equivariance used.

For step 2 I read lem-pe-internal-section-tensor-comparison: it is stated for any site in the coefficient universe, applies to our small coherent profinite site, identifies total tensor on local pure tensors and reflects acyclicity. It is declared as a generic off-unit tool in split_report.tool_uses. def-pc-tensor-complex-sheaves states precisely the total differential used. The restriction-calculus node explicitly says forgetting the action is exact and detects exactness, which is exactly its use here and in step 7. Expanding the homotopy gives the two cancelling coefficients (-1)^p and (-1)^(p+1); this proves the tensor augmentation is a homotopy equivalence for every underlying complex. Thus no finite support of sections of a sheafified coproduct, no convergence, no flatness of X, and no equivariant contraction is required. The proof that homotopic maps induce identical cohomology maps is included rather than assumed.

Step 3 uses only the actual signed Koszul differential in lem-sfb-discrete-lattice-koszul-resolution, and the sectionwise natural action definition. It does not take injective acyclicity or comparison for complexes from that node, which only states the derived comparison for modules. The operators commute with each other and with d_P by the equivariant complex hypothesis. Opposite deletion orders give the square-zero check. The coproduct universal property identifies equivariant maps by their values at the origin; generalized D-valued sections are covered by their finitely many clopen fibres, so equivariance is checked after all profinite base changes, rather than on global elements alone.

Step 4 checks both scaling recurrences explicitly, including the precomposition by the boundary on a basis cell. The finite width 0 through r justifies replacing the Hom product by a finite biproduct in each total degree even for unbounded complexes; bounded-below P in the item therefore satisfies all requirements. Step 5 checks the chain equation separately for cell size a, a+1, and every other size. Its only external input is the cited total-tensor convention, and both cancelling coefficients are written out. These steps carry the calculation themselves and do not hide a comparison lemma in a new node.

Step 6 proves translation equivariance, naturality in a map of complexes and commutation with restrictions by the formulas, citing the actual action definition. Step 7 uses the invariant inclusion clause of restriction-calculus, not its derived cup-product assertions. Invariant sections satisfy T^v x=x; degree zero has theta=1, while every positive cell maps to zero on both sides. This proves the stated equality of chain maps.

I tested r=0 (only one vertex, identity augmentation and unit evaluation), r=1 with b=0 and b=1 (theta_1,b=(-1)^(b+1) gives the required cancellation), top and bottom Koszul degrees, zero coefficient ring, nontrivial action and arbitrary unbounded X. There is no added characteristic, nonzero-ring or coefficient-flatness hypothesis. No statement dispute was found. All steps have fewer than 2000 characters and are explicit component calculations; the non-elementary integral contraction and internal tensor dictionary are cited nodes. Every proof citation has its unmodified source statement copied into citations.json, so the quotations can be checked verbatim.

I checked delivery-errors B–E: new-node conditions are vacuous; definitions are cited or spelled out; no doubled TeX escapes; no unsupported source attribution; every non-elementary input is a node whose statement supplies the fact; no use of another node's proof as its statement; no clause-only child, circular derivation or unproved transport claim. The current route and original statement are retained.

## Unfinished work

None in the stage-1 split. The existing cited dependencies remain their own items.


## Repair of return L, 2026-10-23

The return names head b596e2c13f3 and says that the mathematical reader approved it, but the side completion had not been promoted to the live DAG. I continued the retained delivered files rather than discarding or re-searching them. The required first action, the retained-version dry run, exited successfully with `OK (not pushed)` at 05ca96013a3. The delivery tool prepares its own worktree on the current DAG; I ran no git command in the read-only repository.

I compared the retained item with the current live node field by field. The live item is `unsplit`, has an empty proof and no reviewed record. Its statement, statement dependencies, source, created record, chapter, unit and full blueprint ancestry agree with the retained item. The only differences are the completed proof, its dependency list, agent proof-origin, actual logged searches, split status and split report. Thus the repair reapplies the reviewed argument to the live unsplit node, preserving the live mathematical statement and metadata. The split report now identifies the returned head, current comparison and repair date; this is a refreshed delivery for promotion, not an unchanged branch push.

I re-read the full current statement of every proof dependency, not only dependencies whose quotations might have changed: lem-sfb-integral-lattice-cubical-contraction, sk-def-sfb-module-objects, def-sfb-condensed-action-module, lem-pe-internal-section-tensor-comparison, def-pc-tensor-complex-sheaves, lem-sfb-condensed-derived-restriction-calculus and lem-sfb-discrete-lattice-koszul-resolution. All twelve retained quotation entries remain verbatim substrings of these current statements. Their hypotheses and supplied facts still justify exactly the uses described in Review by N6 above: integral contraction identities in step 1; arbitrary-small-site tensor comparison, total signs and exactness detection in step 2; the Koszul differential and natural action in steps 3–4; total tensor signs in step 5; generalized equivariance in step 6; and the actual invariant inclusion in step 7. No cited statement requires changing the argument or its dependency list.

I re-read the current direct-images paragraph (3), the chapter and unit records, and Stacks Tag 0623's definition-koszul-complex. I re-read all retained msearch results; neither the statement nor its search questions changed, so searches.jsonl and the existing search entries are retained. The current project-source searches supplied no complete declaration of this internal cubical augmentation/evaluation statement; the related triangulated lattice file still contains postponed proofs and is not an attachment. The seven proof steps have lengths below 2000 characters, and their matrix, homotopy and sign checks are explicit. The r=0 and zero-ring cases remain valid, and no translation-equivariance of the contraction is used. Rechecked delivery-errors B–E with these current statements: there are no new nodes, duplicated clauses, new hypotheses, hidden non-elementary inputs or altered source claims. A final dry run and push follow this report update.
