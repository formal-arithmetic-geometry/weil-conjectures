# Stage 1 report: lem-pe-internal-section-tensor-comparison

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-internal-section-tensor-comparison.json`: item split into eight proof steps; no new nodes.
- `citations.json`: verbatim statements for every dependency used by every proof step.
- `searches.jsonl`: Mathlib searches executed through `msearch.py`.

## Attachments

No exact sorry-free Lean declaration was found under `WeilConjectures/`; the item is split.

## WANTED

None. The relevant Stacks sources are present in `literature/stacks-project/`.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs.

## Review by Q155

I reread the imported item and its parent blueprint context in `sk-def-pe-derived-completion/_section.md`, then checked the existing module-object and section-module statements before writing the proof. The first step uses the internal-to-section-module equivalence and the sheafified objectwise tensor definition exactly for their stated claims: the forward functor keeps section groups, restrictions, and maps unchanged. For exactness, I checked that `lem-sfb-modobj-abelian` applies to the abelian sheaf tensor category, that the two internal-module forgetful lemmas provide finite limits and colimits, and that the section-module definition computes kernels sectionwise and cokernels by sheafification; the cited colimits/forgetful lemma supplies the target exactness. The tensor step uses only the displayed relative coequalizer, the sectionwise sheaf tensor definition, the section-module colimit description, and the closed tensor-Hom universal property. I explicitly checked that the pure-tensor normalization follows from the same coequalizer map. The unit/coherence step uses the regular-module clause of the equivalence and the induced associator, unitor, and symmetry constructions; equality on local pure tensors and coequalizer uniqueness supplies the coherence equations.

For complexes, I use the target small-colimit theorem and explicitly transfer each coproduct through the quasi-inverse using its Hom universal property. Colimits are sheafifications of sectionwise colimits; the proof does not assert that a section functor preserves them. Naturality on each summand and additivity give the direct-sum differential in `def-pc-tensor-complex-sheaves`, including its sign, also for unbounded complexes. I checked the edge cases of zero modules, the zero ring, degree-zero complexes, empty direct-sum degrees, and the identity ring object. Exactness gives the displayed cohomology comparison, so acyclicity is preserved and reflected. Finally, I compared the exact-tensor definition of flatness and the acyclic-total-tensor definition of K-flatness with the natural tensor comparison and the preceding acyclicity result; both properties are therefore preserved and reflected. I ran the required Mathlib searches with `msearch.py`; they found only ordinary module-flatness declarations and no internal sheaf-module equivalence, so the item remains a non-Mathlib statement. No source error or hypothesis change was found.

## What was wrong or incomplete in the imported node

The imported node had an empty proof and proof dependencies. I supplied the missing proof and citations while retaining its statement, statement dependencies, blueprint reference, and recorded search history while retaining both the upstream search records and the searches actually logged by `msearch.py` in the earlier sandbox attempt.

## What could not be finished

The final repaired split awaits the required server dry run and delivery.

## Continued review by Q155

The first required dry run passed at efc53ff6ee before edits. I compared the sandbox with the current shared item: its statement, source, statement dependencies and blueprint provenance agree, and the shared item remains unsplit. I retained the report, recorded searches and existing citation quotations. The full project-source searches by blueprint id and by internal/sectionwise equivalence terminology found no exact project declaration; existing tensor and K-flatness developments do not state all clauses of this comparison.

I read Stacks Tags 03DA and 03DB in sites-modules.tex for exactness and colimits, the bilinear universal-property discussion in Section 03EK and the immediately preceding 0GMW sheafification lemma, Definition 03ER for flatness, and Definition 06YN in sites-cohomology.tex for K-flatness. Tag 00YV concerns transport of algebraic structures, so the internal-to-sectionwise equivalence itself is taken from its existing DAG statement, not claimed to follow directly from that tag. The ambient tensor and internal-module structures were checked in the current main-20261015 blueprint and its module-category proof. No SGA source is used.

Step 1 uses the unchanged section groups and restriction maps in the equivalence statement and the displayed sheaf tensor construction. In step 2 I added the explicit citation of sk-def-sfb-sheaf-tensor for colimit preservation and additivity, checking the right-exact-tensor hypothesis of the internal-module abelian and forgetful lemmas. The target abelian and exact-forgetful claims occur explicitly in the two cited section-module nodes. Step 3 now spells out both directions of the balanced-map argument: the relative coequalizer conditions become sectionwise R-bilinearity, and the sheafification universal property identifies precisely these compatible maps. I added its existing definition node and removed the unused closed tensor-Hom and colimit citations from this step. This avoids silently treating sheaf sections as cokernel-preserving. I repaired a carriage return in the retained TeX arrow at the same time.

In step 4 I added def-sfb-modobj-symmetric-tensor, whose statement actually supplies the source symmetry: the relative-tensor definition alone gives only a monoidal structure. The step writes the associator, symmetry and unitor formulas on pure tensors and uses step 3's uniqueness for the diagrams. Step 5 removes lem-sfb-modobj-grothendieck: its Grothendieck hypothesis is unnecessary here. The target colimit statement and the given equivalence provide coproducts by the explicit Hom calculation in that step. Step 6 uses exactly the cited kernel/image cohomology formula. Step 7 compares the two exact-tensor tests through the exact equivalence. Step 8 now explicitly lifts every target test complex by the termwise quasi-inverse and uses its counit chain isomorphism, so both directions of K-flatness quantify over every required acyclic complex. No new node or statement change was needed. Every repaired step has fewer than 2000 characters.

The retained small-case checks remain valid: zero modules and the zero ring give zero tensors; the regular module comparison is the unit action; degree-zero complexes recover the module comparison; all direct-sum indices p+q=n are countable in the specified universe. I checked every new citation against the statement of its existing node and refreshed citations.json with verbatim quotations. The generic module-abelian, forgetful, sheaf-colimit and target tensor-closed lemmas are declared as tool uses in split_report; they supply no replacement of a parent unit step. This item is a tool extracted from the coefficient interpretation of the parent definition, whose current unit has no proof steps to rebind.
