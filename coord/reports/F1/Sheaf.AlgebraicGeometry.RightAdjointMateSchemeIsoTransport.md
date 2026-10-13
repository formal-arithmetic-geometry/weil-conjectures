## What changed

Added a real decomposition of the transport theorem into two named intermediate
statements, one proving ordinary base-change invertibility and one proving the
arrow-mate comparison. The main theorem now combines these two statements. The
intermediate proofs remain explicit named holes for parallel workers.

## Proved and sorry left

The main declaration `rightAdjoint_mate_scheme_iso_transport` is proved by applying
the two strictly simpler intermediate declarations. The following named holes remain:
`rightAdjoint_mate_scheme_iso_transport_base` (node
`lem-sc-right-adjoint-mate-scheme-iso-transport-base`) and
`rightAdjoint_mate_scheme_iso_transport_mate` (node
`lem-sc-right-adjoint-mate-scheme-iso-transport-mate`).

## No longer needed

Removed proof-only imports `Sheaf.AlgebraicGeometry.DerivedBaseChangePasting` and
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition` from the parent
module. They remain dependencies of the intermediate calculations, so no module
is pruned from the full import closure. The parent node now depends only on the
two decomposition nodes.

## Where the brief, the DAG or earlier work was wrong

The previous delivery recorded placeholder text in both new nodes’ `lean.statement`
fields. Replaced those placeholders with the actual Lean signatures. The dry run
now recognizes the closed parent declaration.

The original plan combines two substantial categorical calculations in one theorem.
This delivery exposes those calculations as independent, strictly smaller statements
so they can be proved in parallel.

## New nodes

`lem-sc-right-adjoint-mate-scheme-iso-transport-base` and
`lem-sc-right-adjoint-mate-scheme-iso-transport-mate` are new decomposition nodes.

## Earlier second reading (a previous round; superseded)

1. **Visibility and signatures.** Compared the delivered main module with the repository version. The target declaration signature is byte-for-byte unchanged; only proof imports and the proof body differ. The two decomposition declarations are new and are recorded by matching DAG nodes.

2. **Compilation and axioms.** Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds. The two intermediate declarations remain the explicitly named `sorry` holes listed above, with no `sorry` in definitions, and no forbidden declarations were added.

3. **Statements and decomposition.** The main theorem is proved by applying the two strictly smaller intermediate statements. I corrected the new node descriptions so the base node states only ordinary base-change invertibility and the mate node states only the arrow-mate comparison conditional on the supplied invertibility family. Their statements remain true and strictly simpler than the parent.

4. **Pruning and route.** Removed the main module's proof-only imports of `DerivedBaseChangePasting` and `RingedSpaceDerivedDirectImageComposition`; those dependencies remain in the two intermediate modules where their planned calculations belong. The unit route is retained through the parent theorem and both realized decomposition nodes.

5. **DAG agreement.** Updated both split node statements and proof steps to agree with the Lean conclusions and dependencies. No existing target statement or definition changed, and no Mathlib or upstream duplicate was introduced.

Changed: corrected the split-node metadata, shortened the main proof lines to remove style warnings, and pruned two unused proof-only imports from the parent module.

## Second reading by F1

1. Compared the delivered parent module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and proof-only imports changed. The two added intermediate declarations are recorded by matching DAG nodes.

2. Compiled all three sandbox modules with `lcompile.py`; compilation succeeds. The parent theorem has no `sorry`; the only remaining holes are the two explicitly named intermediate theorems. No forbidden declarations or hollow definitions were added.

3. Read both split statements and their proofs in the DAG. Each is a true conditional reduction strictly simpler than the parent: the base statement concludes only ordinary base-change invertibility, while the mate statement concludes only the conditional arrow isomorphism. Their signatures match the Lean declarations exactly, and no duplicate upstream declaration was found.

4. The parent proof now follows the decomposition route, retaining the unit through the parent and both realized split nodes. The two original proof-only imports removed from the parent are still imported by the intermediate modules where their calculations are intended; no further pruning is available.

5. Checked DAG proof, proof dependencies, and proof origin against the Lean proof. The parent depends only on the two split nodes, while each split node lists the dependencies used by its planned calculation. No target statement or definition changed.

Changed during second reading: corrected this report's pruning account to record removal of `DerivedBaseChangePasting` and `RingedSpaceDerivedDirectImageComposition` from the parent, and documented the checks above.
