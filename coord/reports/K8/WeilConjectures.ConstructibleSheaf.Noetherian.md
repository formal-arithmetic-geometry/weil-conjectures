## What changed

Rebased the retained K8 proof of
`AlgebraicGeometry.Etale.exists_finset_mono_pi_lift` onto the current
`WeilConjectures.ConstructibleSheaf.Noetherian` source. The theorem is filled
with the finite irreducible lisse stratification argument of blueprint
`lem-weil-pbc-constructible-noetherian-finite-selection` (proof paragraph).

For each stratum, take the image of its generic point and the canonical
residue-field algebraic-closure stalk there. These source stalks are finite
because the coefficient ring is finite. Choose one detecting index for each
nonzero element of these finitely many finite stalks. Their finite image is
`L₀`. Product projections prove injectivity at every tested stalk.
Naturality of `upperStarCompSheafFiberIso` transports monicity to the geometric
generic stalk on each stratum. The generic-stalk criterion already proved in
this file makes the restricted map monomorphic. Lift each canonical geometric
point through a stratum containing its image, transport monicity back by the
same natural isomorphism, and cancel on stalks. Geometric-stalk extensionality
then proves monicity of the original product map.

The current source already contains the required private import
`WeilConjectures.AlgebraicGeometry.IrreducibleStratificationRefinement` and its
newer proof of `Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible`;
both were preserved while applying this proof. The current private helper
`mono_map_iff_of_natIso` was also preserved. Every existing declaration
signature, attribute, docstring, and public import is preserved. No definitions
or other modules change.

Validation: the complete module compiled on the project server. The final
delivery runs the clean compile, signature checks, and axiom probe.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Etale.exists_finset_mono_pi_lift`
(blueprint `lem-weil-pbc-constructible-noetherian-finite-selection`).

Holes added: zero. Holes left in the item: zero. Split-off statements: zero.
The finite dependent sum and its image handle empty schemes, zero source
stalks, and empty index sets without a nonemptiness assumption. No hypothesis
on any target sheaf is used beyond being a module sheaf.

## No longer needed

Imports removed: none. Nodes or modules pruned: none.
The proof directly performs the generic-stalk testing argument with the
module-valued stratification and generic-stalk criterion already in this file.
It needs no import of the older abelian-sheaf modules
`WeilConjectures.AlgebraicGeometry.ConstructibleFiniteStalkTests` or
`WeilConjectures.AlgebraicGeometry.ConstructibleFiniteSelection` and no
forgetful-sheaf comparison. Their existing consumers still need them, so no
global withdrawal is proposed.

## Where the brief, the DAG or earlier work was wrong

The returned packet was based on an older source revision. Since then the
current source acquired the private refinement import, a completed
`exists_stratification_isIrreducible` proof, and the private natural-isomorphism
helper. This repair takes that source as the base and changes only the finite
selection theorem proof; the current import-direction check remains valid.

No node currently has `lean.module` equal to the assigned source module.
The blueprint finite-selection node is attached to the older abelian theorem
`AlgebraicGeometry.Scheme.exists_mono_biproduct_of_constructible_stalk_detection`
in `WeilConjectures.AlgebraicGeometry.ConstructibleFiniteSelection`; the
stratification and generic-kernel nodes similarly have older abelian
attachments. This delivery proves their module-valued counterparts already
present in the assigned source file. It follows the blueprint's finite lisse
partition route and leaves the attachments and the older theorems intact.
The unit record `sk-prop-sf-cbc` has no realized statement or proof-step node
that this proof bypasses. No new nodes or route changes are required.

Searches run: LeanFinder for finite subfamilies detecting nonzero geometric
stalk elements, Loogle for `Mono` and `Pi.lift`, and ripgrep through the source
library, Sheaf modules, and Mathlib. The older finite-testing proofs provided
the natural-isomorphism and cancellation pattern; no Mathlib theorem directly
states the assigned constructible-module selection result.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
