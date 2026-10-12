## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.AffineModuleTensorCounitFactor` by a complete Lean reduction.
The existing signature and visibility are unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.AffineModuleTensorCounitLinear` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction`.

The new lemma isolates B-linearity of the pullback counit transported through κ.
It does not mention H or γ. The main proof applies the existing change-of-rings
adjunction along ε to this B-linear map, transports through the stated object
identifications, and checks the factor equation sectionwise using hH.
It proves epimorphy by injectivity of the same Hom equivalence: equality after γ
implies equality on every tensor-unit generator and hence equality of the maps.
The helper's section formula uniquely determines its witness; no arbitrary data
is selected from an unproved mere-existence statement.

The item node's proof, proof_deps and proof_origin now record this route.
The theorem-local heartbeat allowance has an explanatory comment; the module's
existing options and public imports are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_counitFactor`
(node `lem-weil-pbc-affine-module-tensor-counit-factor`).
There are no sorries left in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_counitLinear`
(node `lem-weil-pbc-affine-module-tensor-counit-linear`), in its own new module.
Its entire proof is `by sorry`; its docstring and node carry the evaluation argument.
Thus this delivery is a decomposition (one hole closed, one added), not a
sorry-free proof of the whole original result. The factorization glue and the
entire epimorphism argument are implemented in Lean.

The new statement was checked on identity morphisms, empty schemes/opens,
zero rings and modules, and split maps b, ε. It imposes neither affineness nor
quasi-coherence. The equality t ε = e supplies precisely the balanced tensor
relation, and b ε = 1 supplies O_U-linearity after restriction.

## No longer needed

No imports removed; no nodes or modules globally pruned.
Removed from the parent node's direct `proof_deps`: `def-pur-sheaf-tensor-product`,
`lem-pc-module-pullback-adjunction`, and
`def-weil-presheaf-modules-sheafification`. They now occur through the
counit-linearity lemma or the public statement imports and remain needed
transitively; none of their modules is globally pruned.
The parent's third proof step no longer needs a local-surjectivity argument:
its epimorphism assertion follows directly from the already proved
change-of-rings Hom equivalence. The unit's realized statements and steps are kept.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The B-linearity assertion in the original first proof
step was not itself given by a stated theorem among its dependencies; it is now
isolated as a strictly smaller lemma. The original epimorphism step can be
replaced by the Hom-equivalence argument, avoiding a separate sheaf-local
surjectivity theorem.

`tools/blueprint_refs.py ancestor` prints None for this item because its
`created.item` is a module name. The new node retains the item's recorded
blueprint ancestor `thm-weil-pbc-finite-etale-lifting` and extends its recorded
via chain. Blueprint search found no existing counit-linearity node.
LeanSearch returned Internal Server Error; this is recorded as unavailable,
not as absence. LeanFinder and Mathlib grep found no exact match. Stacks 01SB,
the construction of h and its elucidation, was read against the supplied plan.

## New nodes

`lem-weil-pbc-affine-module-tensor-counit-linear` states only that the composite
of κ and the canonical pullback counit is B-linear for the action through ε.
Its module is `Sheaf.AlgebraicGeometry.AffineModuleTensorCounitLinear`.
The node includes the full setting, the unit compatibility formula, a
three-step natural-language proof and the actual three search records.
No existing definition or statement was changed; there are no change records
or forced adaptations.


## Second reading by E1

1. **Interface: PASS.** Compared the existing module with the repository by
   `diff` and checked the theorem signature byte for byte. The only Lean changes
   are two plain proof imports, a documented local heartbeat option, and the
   proof body. The existing docstring, signature, public imports, definitions,
   and visibility are unchanged. No change record or forced adaptation is needed.
2. **Proof: PASS as a decomposition.** Both delivered modules compile together
   through `lcompile.py --all` without warnings. A scratch copy with `#print axioms`
   for both declarations reports only `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`. The sole new sorry is the named counit-linearity theorem;
   there are no definitions with holes or forbidden declarations. The main
   proof constructs the factor map through the existing change-of-rings Hom
   equivalence and proves epimorphy by its injectivity. No arbitrary witness
   is installed as definition data; the helper's section formula determines its
   morphism uniquely by sheaf-module extensionality.
3. **Split statement: PASS.** Read the full helper signature, docstring, and
   matching node. It removes H, gamma, their identifications and compatibility,
   and asserts only B-linearity of the fixed counit composite. It is strictly
   part of the argument, not a restatement of the original conjunction.
   Tensor evaluation is balanced because t epsilon=e, and its restriction is
   O_U-linear because b epsilon=1. The canonical unit compatibility fixes its
   agreement with the supplied kappa. Locally, at a point of U, inverse-image
   sections come from neighborhoods of its image; the pullback module is
   generated by their unit images over O_U. Thus agreement on those images
   extends to all sections. Identity maps reduce to ordinary evaluation;
   zero modules, zero rings, and empty schemes introduce no exceptions.
   Independently searched LeanFinder for inverse-image counit/scalar-action
   compatibility, Loogle for `SheafOfModules.pullbackPushforwardAdjunction`,
   Mathlib grep for counit/change-of-rings/restriction combinations, and the
   project sources for inverse-image and tensor counits. The generic Mathlib
   adjunctions and the project's TopologicalPullback theorem supply ingredients,
   but none states the required B-linearity under the given kappa compatibility.
   Closing this remaining sheaf/tensor comparison is not a few-minute repair.
   Read the source's construction and elucidation online:
   [Stacks 01SB](https://stacks.math.columbia.edu/tag/01SB).
4. **Route and pruning: PASS.** The factorization uses the existing proved
   change-of-rings adjunction, and epimorphy uses no extra split theorem.
   Both public imports are needed to state the signatures, and both added
   plain imports are used in the proof. Checked the old four direct dependencies:
   the change-of-rings adjunction stays direct; the other three are explicitly
   listed above as removed direct dependencies, still required transitively.
   Read `dag/units/sk-thm-p1.json`: this below-unit helper is not a realized
   statement or step, and this reduction changes none of the unit's routes.
5. **Nodes: PASS.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`, matching the actual Hom-equivalence proof. The new node's
   verbatim Lean statement, source, proof steps, dependency union, searches,
   creation record, blueprint ancestry, chapter, unit, and Lean attachment
   agree with the new module and meet the stage-3 field requirements.

Second-reading changes: made the removed direct proof dependencies explicit
in `## No longer needed` and added this review. No Lean proof or statement
needed repair. One original hole closed and one smaller hole added: net zero
holes, a decomposition, with no globally pruned modules.
