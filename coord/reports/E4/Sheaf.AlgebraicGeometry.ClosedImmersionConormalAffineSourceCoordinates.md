## What changed

Completed the earlier sandbox reduction in
`Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineSourceCoordinates`.
The statement and public imports are unchanged. The proof imports
`ClosedImmersionConormalAffineTensorCoordinates`, `ModulePullbackAffineSections`,
and `AffineConormalSections` as proof-only dependencies.

On the affine inverse-image opens, obtain the tensor-coordinate equivalence e,
then the bijective affine pullback comparison c for the quasi-coherent conormal.
Convert c to an additive equivalence d and take (e.trans d).symm. The two
pure-tensor formulas compute the inverse on generators. Expanding the
pushforward isomorphisms and applying the presheaf composition law identifies
the transported successive units with the direct restriction. The final
arrow equality follows from the thin category of opens.

The new tensor-coordinate module contains only the remaining chart-ring and
tensor algebra argument. It is strictly a part of the original argument: it
involves neither the sections of the second pullback nor the f-unit or its
pushforward/equality transport. Added its complete DAG node and updated the
original node's proof, proof_deps and proof_origin to match the Lean proof.
No existing signatures, definitions or visibility changed; no forced adaptations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_source_coordinates`
(node `lem-weil-pbc-closed-immersion-conormal-affine-source-coordinates`).
Its module now has no sorry.

Added one strictly lower hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_tensor_coordinates`
(node `lem-weil-pbc-closed-immersion-conormal-affine-tensor-coordinates`).
Its proof is exactly `:= by sorry` in its own new module. Its docstring gives
the source, the complete algebra argument and the generator normalization.

This is a decomposition: one upper hole closed, one lower hole added, net
zero holes closed. The combination into the original theorem is fully proved
and compiled. Existing imported declarations may still depend on sorry;
they were not changed in this delivery.

Both delivered modules compiled together through lcompile.py. The source
coordinate theorem retained exactly its original signature. Checked the
remaining lemma on J=0, J=A, zero chart rings, identity base change, and
nonflat base change: in particular it compares the source tensor modules,
not the target conormal, so flatness is not required. The unit sk-thm-p1
and all of its realized statements and steps are unchanged.

## No longer needed

None globally. No original import was removed. The original node no longer
needs `lem-pc-ideal-sheaf-comap-affine-extension` or
`lem-weil-pbc-tensor-over-quotient-ring` as direct proof dependencies:
they are now dependencies of the lower tensor-coordinate node, and remain
needed transitively. The other four original proof dependencies remain
needed directly. No module or unit step is claimed pruned.

The earlier scratchpad algebra experiment is not included in the delivery:
it is not needed for the completed combination proof.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had a compiling reduction in the sandbox but no report
or DAG node for its remaining theorem, and no completed dry run. Added those
missing delivery records and updated the main theorem's proof docstring.

The Stacks source checkout named by the nodes is absent on this machine.
Read the cited primary-source pages directly:
[Tag 0473](https://stacks.math.columbia.edu/tag/0473),
[Tag 01R3](https://stacks.math.columbia.edu/tag/01R3), and
[Tag 01JU](https://stacks.math.columbia.edu/tag/01JU).
The tensor argument expands the algebra implicit in these affine reductions.
LeanSearch returned Internal Server Error; recorded this as unavailable, not
as an absence result. LeanFinder, Loogle, source grep and blueprint searches
found algebra ingredients but no duplicate normalized scheme tensor-coordinate
statement. No mathematical error in the brief or unit route was found.

## New nodes

`lem-weil-pbc-closed-immersion-conormal-affine-tensor-coordinates`:
identifies B tensor_A J/J² with the tensor of the first conormal's affine
sections over C=Γ(Z',V') with D=Γ(Z,V). Its generator formula contains only
the i'-unit. The proof plan retains the original cartesian kernel/ideal
calculation, normalized affine conormal coordinates, quotient scalar
cancellation and annihilation argument. Its one named sorry is isolated in
`Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineTensorCoordinates`.
No change record is needed, since no existing interface changed.

## Second reading by E4

1. **Statements and signatures.** I compared both delivered Lean modules with the
repository versions. The existing source-coordinate theorem has the identical
signature and conclusion. The new tensor-coordinate theorem is a proper
intermediate statement: it constructs only the tensor equivalence before the
second pullback section comparison, with the same closed-immersion, cartesian
square, affine-open, and ideal-section hypotheses. No target statement or
definition changed.

2. **Compilation and trust.** I compiled both modules together with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all ...`; both compiled cleanly.
The only remaining `sorry` is the named theorem
`closedImmersion_conormal_affine_tensor_coordinates`, and it is documented and
has the matching DAG node. The completed source-coordinate theorem has no
`sorry`. The delivered files contain no axiom, unsafe, opaque, extern, or
implemented-by declaration.

3. **Truth and strength of the split.** The new theorem is strictly smaller than
the original: its equivalence ends at
`Γ((tensorPullback i').obj i'.ker.toModules,V') ⊗ Γ(Z',V') Γ(Z,V)` and its
formula uses only the first adjunction unit. It does not mention the second
pullback's sections, its unit, pushforward composition, or equality transport.
Its docstring checks the edge cases `J = 0`, `J = A`, zero chart rings,
identity base change, and nonflat base change. The cited Stacks statements
0473, 01R3(2), and 01JU(1) support the affine conormal and cartesian ideal
calculations. Searches recorded in the node found no duplicate declaration.

4. **Proof route and pruning.** The source-coordinate proof uses the new
tensor-coordinate theorem, the existing affine conormal and affine pullback
section comparison, then computes the restriction composition by the presheaf
composition law and thinness of opens. The unit route is retained; no unit step
is bypassed. The node's `proof`, `proof_deps`, and `proof_origin` match this
route. The removed direct dependencies are still used transitively by the new
lower node, so no module is incorrectly claimed pruned.

5. **Changes made.** I found no statement, import, visibility, or mathematical
error requiring repair. I added this second-reading record only; the Lean files
and node statements remain unchanged after the checks above.
