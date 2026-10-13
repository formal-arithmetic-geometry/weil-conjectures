## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.picard_fixed_model_residue_cycle_comparison`
with a complete Lean reduction, preserving its signature and all public imports.
Added `PicardDescendedFibreCoefficientTrivial`, whose theorem is proved from the existing
field rank-one theorem and module adjunction. The universal structure unit excludes an
empty source fibre; descent then makes the fibre coefficient trivial.
Added `PicardResidueCyclesGeometricNaturality`, isolating comparison on source cycles
modulo boundaries. The main module proves the remaining algebra: zero incoming residue
differential makes the surjective comparison injective; zero outgoing differential
identifies the full source term with its cycles; tensoring the inverse basis supplies
alpha; the evaluated chain-map equation puts every representative image into target cycles.
Updated the parent node's proof route and recorded both new declarations as nodes.
Explicit composition equations and subtype extensionality avoid unfolding equivalence
structures in the compatibility check. The compiler wall-time limit remains 60 seconds.
No existing statement, definition, signature, or visibility changed. No forced adaptations.
The main file compiled without warnings in 50.6 seconds; its signature comparison reports
no statement changes. The delivery dry check validates the complete three-module set.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_fixed_model_residue_cycle_comparison`
(node `lem-sc-picard-fixed-model-residue-cycle-comparison`). Its proof contains no sorry.
Also proved the new theorem
`AlgebraicGeometry.Scheme.picard_descended_fibre_coefficient_trivial`
(node `lem-sc-picard-descended-fibre-coefficient-trivial`), with no sorry in its module.

One new hole remains:
`AlgebraicGeometry.Scheme.picard_residue_cycles_geometric_naturality`
(node `lem-sc-picard-residue-cycles-geometric-naturality`), whose entire proof is `by sorry`.
This is a decomposition: one upper hole closed and one lower hole added, net zero holes.
The lower theorem is not a renaming: it has no coordinate basis or source minimality;
it compares a source cycle kernel with fibre cohomology, retaining boundaries and giving
surjectivity and their exact kernel description. The main proof supplies the bijectivity,
full-term extension, tensor coordinates, and target-cycle membership.

## No longer needed

Removed the main module's direct proof imports:
`Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial`,
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.
The first remains used by the proved coefficient lemma; the other two remain proof-plan
imports of the geometric comparison. Accordingly none of the old proof-dependency modules
is claimed pruned from the transitive target closure. No node or module is wholly pruned.
The main proof needs source minimality only in degrees zero and one; it does not use
higher-degree vanishing to perform the algebraic assembly. No complements, projections,
product comparisons, or particular chain representatives are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped before trying a formal reduction. The geometric comparison
can be stated without source coordinates or minimality: its source cycle map is a
surjection with precisely the boundaries as kernel. This interface supports a real Lean
proof of the original assertion and leaves a separate geometric task.
The supplied DAG dependencies do not themselves state the whole natural cycle-to-fibre
comparison, so it is explicitly named rather than inferred from their prose proofs.
The unit `sk-prop-av-cube` and its statement and steps are unchanged.
Edge cases checked: an empty source fibre contradicts the structure-unit hypothesis;
n=0 removes only the target naturality assertions; m=0 is handled by the same additive
equivalences. The new geometric statement allows nonzero source boundaries and maps them
to zero, rather than incorrectly asserting injectivity without minimality.
LeanSearch was unavailable (HTTP Internal Server Error); Loogle, LeanFinder and source
searches were performed. Source passages read: Stacks 0BF2, 0BDP, 0B91 and 01XK.
The inherited rank-one dependency cites 0BF0, but that tag states closedness of the
descent locus. The new coefficient lemma cites 0BF2/0BDP for the fibrewise descent
argument and uses the existing proved field rank-one declaration.

## New nodes

`lem-sc-picard-descended-fibre-coefficient-trivial` records the proved coefficient lemma
in `Sheaf.AlgebraicGeometry.PicardDescendedFibreCoefficientTrivial`. It isolates the
nonempty-fibre/rank-one argument and uses no derived models or target family.

`lem-sc-picard-residue-cycles-geometric-naturality` records the remaining geometric
comparison in `Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality`.
It compares cycles modulo boundaries, with the common source-fibre trivialization
pulled back to every target. Its complete proof in words and inherited geometric
dependencies are in its docstring and node.

## Second reading by A4

1. **Statements and interfaces.** Compared the delivered parent module byte-for-byte
   with the repository version apart from proof/import changes; the existing target
   signature is unchanged. The two added declarations have signatures matching their
   DAG nodes and introduce no altered existing interface.
2. **Compilation and proof hygiene.** Compiled all three modules with `lcompile.py --all`
   and compiled the parent independently. There are no errors, forbidden declarations,
   or `sorry` in definitions; the only remaining `sorry` is the named geometric
   comparison theorem and its matching node.
3. **New statements.** Checked the coefficient lemma's nonempty-fibre and rank-one
   argument, including the empty-fibre contradiction, and checked that the geometric
   lemma retains incoming boundaries and states surjectivity plus the exact kernel.
   Both are strictly simpler than the parent and are not duplicate library declarations.
4. **Route and pruning.** The parent proof uses the coefficient and geometric nodes,
   then performs the source differential algebra and target-cycle calculation. Removed
   imports are proof-only and no unit step is bypassed; the unit realization is unchanged.
5. **Nodes and dependencies.** Verified that each node's declaration, proof route,
   proof dependencies, source, and split status agree with the Lean files. No stale
   proof dependency was claimed as pruned.

I changed only the parent proof/imports, added the two split-off modules and nodes, and
recorded this second reading. The dry-run delivery check passes.
