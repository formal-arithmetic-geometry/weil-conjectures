# Stage 1 report

## Files written

- `dag/nodes/sec-abelian-varieties/pqf-def-coherent.json`: split definition; no new nodes.
- `citations.json`: empty, because definitions have no proof steps.

## Attachments

None. `AlgebraicGeometry.Scheme.Modules.isCoherent` in `WeilConjectures/AlgebraicGeometry/Modules/Coherent.lean:46` is not an attachment: it defines quasi-coherent plus finite presentation and its docstring explicitly says this is weaker than the Stacks coherent notion on general schemes.

## WANTED

WANTED: `literature/stacks-project/cohomology.tex`, Tag 01DW source text; the pinned Stacks checkout is absent from this machine.

## What was checked

I copied the item node and read its chapter/unit context, the imported statement, and the available Lean source. The statement is the Stacks three-clause definition: quasi-coherence on affine neighbourhoods, local finite type, and finite-type kernels of maps from finite free modules. The only project declaration with the relevant name has a different body, so it cannot be attached. Existing DAG definitions `def-pc-scheme` and `def-weil-sheaf-of-modules-category` supply the ambient scheme and module notions and are now the item's statement dependencies.

I searched the whole DAG and blueprint references for the definition and for Tag 01DW. No existing node states this definition or one of its clauses as an independent reusable theorem; creating clause nodes would restate parts of the item and violate the no-clause-duplication rule. Accordingly there are no new nodes and no proof steps. The blueprint fields were completed with `same_as: []` and the item remains the blueprint node itself.

## Review by F1

I checked the hypotheses and objects in the item against `def-pc-scheme` and `def-weil-sheaf-of-modules-category`; the item introduces the sheaf and its three properties, so no further statement dependency is needed. I read `Modules/Coherent.lean` in slopmaster2 and verified that `Scheme.Modules.isCoherent` is an abbreviation for `IsQuasicoherent ∧ IsFinitePresentation`, with the source comment warning that it differs from Stacks coherence away from locally Noetherian schemes. I therefore did not report an attachment. I ran both required phrasings of LeanFinder, Loogle, grep, and LeanSearch. LeanFinder returned only generic `SheafOfModules.IsFiniteType`/`IsFinitePresentation` predicates; Loogle and grep found no exact Stacks definition; LeanSearch was unavailable both times and is recorded as unavailable in the node. Small cases checked conceptually include the zero module, a finite free module, and a locally Noetherian affine scheme, where the three clauses have their usual meanings. Since this is a definition, there are no cited proof steps or citation quotes.

5. What remains: no Lean code is written at stage 1; the definition is ready for the next stage.

## Source error

The imported statement cited Tag 01DW, which is the Cohomology of Sheaves chapter landing page and does not define coherent modules. The statement is instead checked against Sheaves of Modules, Definition 17.12.1, Tag 01BV, with the finite-type clause from Tag 01B5; the node source and inline citation were corrected accordingly.

## Second reading by F1

- Item statement: checked the quasi-coherent, finite-type, and coherent clauses against Stacks Modules Definition 17.12.1 (Tag 01BV) and finite-type Definition Tag 01B5; hypotheses and the kernel condition agree.
- New nodes: none; B1-B7 and duplicate checks are vacuous.
- Proof steps: none; this is a definition node with no proof or citations.
- Lean attachment: checked `AlgebraicGeometry.Scheme.Modules.isCoherent` in `Modules/Coherent.lean:46`; it is the weaker quasi-coherent-plus-finite-presentation predicate and is not an exact attachment.
- Edge cases: checked the zero module, finite free modules, and affine schemes; all clauses have the expected truth conditions, including the empty scheme vacuously.
- Changed the Stacks source from incorrect Tag 01DW to Definition 17.12.1/Tag 01BV and Tag 01B5, and recorded the source error above.
