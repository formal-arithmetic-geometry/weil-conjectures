## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_unitLift` in
`Sheaf.AlgebraicGeometry.AffineModuleTensorUnitLift` without changing its signature,
definitions, visibility, or existing docstring. Added the proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction`.

The two change-of-rings adjunctions construct the linear tensor-unit maps. Their section
formulas, together with `hP.2` and `hH.2`, identify the original pullback adjunct with the
composite of this linear map and the inverse-image unit. Semilinearity of that unit,
linearity of the constructed map, `ht`, and the ring adjunction triangle prove A-linearity.
`PresheafOfModules.homMk` retains the original additive maps and restrictions; the final
restriction-of-scalars equality follows by componentwise reflexivity.

Updated the node's proof, proof dependencies, and proof origin to this argument.
The unit `sk-thm-p1` and all of its realized statement and steps are unchanged.

Validation: the complete module compiles through `lcompile.py` with no errors or warnings.
`#print axioms` for the theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
All lines are at most 100 characters. A documented local heartbeat limit of 800000 accommodates
transported tensor adjunctions; the final local compile took 40.8 seconds, below the file limit.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_unitLift`
(node `lem-weil-pbc-affine-module-tensor-unit-lift`).

One of one original holes proved; zero holes added; no `sorry` remains in the delivered
module. This is a complete proof, not a decomposition. The axiom check also confirms
that it does not rest on imported sorries.

## No longer needed

No original imports were removed: both public imports are needed by the unchanged statement.
No module is claimed to leave the targets' import closure.

The direct proof no longer needs `lem-pc-module-inverse-image-adjunction`
(`Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback`): it uses only semilinearity
of the inverse-image unit from `def-pc-topological-inverse-image-module`
(`Sheaf.Topology.InverseImageModule`). The inverse-image adjunction remains a transitive
dependency of the unchanged public pullback-adjunction import, so this is direct proof
pruning, not removal from the library's import closure.

The former separate proof dependencies `def-pur-sheaf-tensor-product` and
`def-weil-presheaf-modules-sheafification` are supplied within the change-of-rings adjunction;
no independent tensor balancing or sheafification argument is needed here. Their definitions
remain needed by the statement and by imported adjunctions; their modules are not removed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The existing proof plan is valid, but its explicit balanced-tensor
calculation can be replaced by two applications of the already proved change-of-rings
adjunction. The plan did not list this available lemma. The pushout condition `hpush`, the
splitting identity `hb`, and the functor-map clauses `hP.1` and `hH.1` are unnecessary for this
objectwise conclusion; all hypotheses stay exactly as given. No changes or forced adaptations
of other modules are needed.

## Second reading by Y2

1. **Statements and interfaces.** Compared the delivered module and node with the repository
   versions. The theorem signature, definitions, visibility, docstring, public imports, and unit
   statement are unchanged; only a proof-only import and proof metadata were added.
2. **Proof validity.** Compiled the module with `lcompile.py`; it has no errors or warnings,
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The theorem's axioms
   are limited to `propext`, `Classical.choice`, and `Quot.sound`.
3. **Statements and dependencies.** The change-of-rings adjunction used in the proof is an
   existing proved declaration and is not a restatement of this target. The revised DAG proof,
   dependencies, and origin match the imports and declarations used by the Lean proof; the
   removed direct dependencies are genuinely unused by the new route.
4. **Pruning.** The proof uses the shortest available route through the two existing
   change-of-rings adjunctions and inverse-image semilinearity. No public import can be removed,
   and no target-closure module is incorrectly claimed as pruned.
5. **Unit route.** The `sk-thm-p1` unit and all realized statement and proof steps are preserved;
   the direct proof still establishes the same objectwise algebra-linear lift.

Changed only the proof-only import, theorem proof, and matching DAG proof metadata. No statement,
definition, unit, or split-off theorem was changed or added.
