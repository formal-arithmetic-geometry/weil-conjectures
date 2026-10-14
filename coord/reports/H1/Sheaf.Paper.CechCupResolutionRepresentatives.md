## What changed

Replaced the placeholder proof of `AlgebraicGeometry.Scheme.Modules.cechCup_resolution_representatives`.
The proof imports `Sheaf.Paper.CechCupResolutionComparisonExists` and
`Sheaf.Paper.CechCupSignedAxisPairing`. It uses their existing flasque resolution comparison,
resolution class equations, and signed alpha/beta axis pairing. Two private proved lemmas establish
surjectivity of the class maps and that the paired cocycle is closed under the Leibniz identity.

The copied DAG node now records these two proof dependencies and the three corresponding proof steps.

## Proved and sorry left

`cechCup_resolution_representatives` is fully proved; no `sorry` remains in the delivered module.
The two private helper lemmas are also fully proved. Holes closed: 1; holes added: 0.
No new modules, nodes, definitions or assumptions were introduced.

Validation: the module compiles without warnings in 6.6 seconds. The sandbox passes the dry-run
preflight; the required independent second reading is left for the second reader.

## No longer needed

The direct proof imports `Sheaf.Paper.CechComparisonMapNaturality`,
`Sheaf.Paper.ModuleCupFlasqueAcyclicity`, and `Sheaf.Paper.ModuleCupGodementPairing` are removed.
These modules remain available transitively through the comparison construction; no global module
pruning is claimed. Their direct DAG proof dependencies `lem-sc-cech-comparison-map-naturality`,
`lem-sc-module-cup-flasque-acyclicity`, and `lem-sc-module-cup-godement-aw` are no longer needed by
this node because the existing comparison-existence theorem packages those constructions.

## Where the brief, the DAG or earlier work was wrong

The original plan expanded the Godement construction and comparison naturality directly. Existing
library declarations already package that construction and the signed Cech axis argument, so the
expanded dependencies were unnecessary. No statement was changed.

## Second reading by H1

1. Compared the delivered Lean module with the repository version. The theorem signature and all
   existing declarations are unchanged byte for byte; only the theorem proof and its private
   helpers were added, and the DAG proof/proof-dependency fields were updated accordingly. Verdict:
   pass.
2. Compiled the module with `lcompile.py` (including the sandbox import closure). It compiles
   without errors or warnings, contains no `sorry`, and introduces no forbidden declarations.
   The two private helper lemmas and the public theorem use only the expected imported results;
   the proof is kernel checked. Verdict: pass.
3. Checked the proof route and the two helper arguments against the imported declarations and
   searched the library for an existing declaration of the same result. The helpers are strictly
   intermediate (surjectivity of the class map and closure of the paired cocycle), are true at
   degrees zero as well as positive degrees, and are not duplicate library statements. Verdict:
   pass.
4. Checked pruning and imports. The direct imports removed in the first reading are not needed by
   this proof; the comparison-existence and signed-axis modules provide the required route. The
   unit route and public theorem statement remain unchanged. Verdict: pass.
5. Checked that the DAG proof, `proof_deps`, Lean proof, and report agree, and that no new node or
   split-off hole was introduced. Verdict: pass.

Changed only the proof and its recorded proof dependencies, and added this second-reading record;
no mathematical statement, definition, or public import was changed.

