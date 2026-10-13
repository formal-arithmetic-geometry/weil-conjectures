## What changed

Completed and checked the earlier sandbox candidate in
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineReconstructionObjectwise`.
The existing public theorem's signature and docstring are unchanged.
The existing proved private helpers `Scheme.Modules.product_qc` and
`Scheme.Modules.multiplication_range` in the ideal-section dependency compute
quasi-coherence and the affine multiplication range (accessed by proof-only `import all`).
Two proved private helpers transport the module cokernel through tilde and construct
a single-level quotient isomorphism with its projection equation. The theorem assembles these isomorphisms,
proves transition naturality by cancelling the quotient projections, and lifts the
isomorphism to the full subcategory. The choice of each comparison is uniquely determined
by its projection equation; no data is chosen from an unproved existence theorem.

Used a proof-only `import all` of the existing ideal-section module and added
proof-only imports for the affine ideal-sheaf comparison, module cokernels and
the linear first-isomorphism construction. Tensor-section and cokernel/image
calculations are reused through the ideal-section module without direct imports. Updated the existing node's proof, proof_deps and proof_origin to record
these calculations. No public interface, definition or statement was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.coherentFormalModules_affine_reconstruction_objectwise`
(node `lem-weil-pbc-coherent-formal-modules-affine-reconstruction-objectwise`).
There are no sorries left in the delivered module and no added holes or new modules.
The delivered private helpers `affineIdealPower_tilde_cokernel` and
`affineFormalQuotient_projection_iso` are proved; the other two helpers are reused
from the existing dependency rather than duplicated.
The theorem is proved from existing dependencies, not decomposed into new holed statements.
The existing quotient-functor membership theorem remains a dependency in its own module;
this delivery does not claim to close holes in dependencies.

Validation: the candidate compiled cleanly through lcompile.py, and after replacing the
local cokernel/kernel quasi-coherence argument by the existing image theorem, it compiled
cleanly again. The delivery dry run also performs the declaration and axiom probes.
The first-isomorphism and cokernel arguments include zero modules, the unit ideal and the
zero ideal; the positive exponent is n+1, including the first level n=0.

## No longer needed

Removed the redundant direct import `Sheaf.AlgebraicGeometry.CoherentFormalModule`;
it remains publicly available through `CoherentFormalModulesAffineQuotient`, and its
node and constructions remain necessary.
Removed the provisional direct import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel` from the earlier sandbox
candidate: quasi-coherence of the image is supplied by
`quasiCoherent_cokernel_image`. This does not prune that module from the whole closure,
because other necessary modules still use it.
No original proof-dependency node is bypassed. No unit statement or unit proof step is
pruned. The second reading also removed the candidate's direct imports of
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections` and
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`: the existing ideal-section
helpers already perform those calculations. Their nodes are still dependencies of
the argument; their modules remain reached through the ideal-section module.
All remaining imports are used by the statements or the proof. No whole module
is claimed pruned from the target import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had a complete candidate but no report or node-route update and no
successful delivery dry run. Its two scratch-file public helper variants are not delivered;
the actual delivery keeps proved private helpers in the item module, so it adds no nodes.
The original one-step DAG plan omitted the generic tensor-section and cokernel/image
statements needed for its multiplication calculation; the updated route names them.
Searches found the Mathlib first-isomorphism construction but no ready-made ideal-power
tilde comparison. No mathematical error or unusable signature was found.

## Second reading by D3

1. Compared the sole delivered module with the repository using `diff` and checked
   the existing public theorem signature byte for byte. Verdict: unchanged signature,
   docstring, visibility and public imports; no definition or interface changes and
   no forced adaptations or change records required.
2. Compiled the original candidate and the repaired candidate through `lcompile.py`.
   Verdict: both compile without errors or warnings. The delivered source has no
   `sorry`, axiom, unsafe declaration, opaque declaration, extern, implemented_by or
   kernel-check bypass, and adds no definitions. Explicit scratch-copy `#print axioms`
   and the delivery tool's full declaration probe check the axiom dependencies.
   The two local helpers use only `propext`, `Classical.choice` and `Quot.sound`.
   The public theorem additionally uses `sorryAx` through the existing
   `coherentFormalModules_affine_quotient_coherent` dependency, which is still open.
   Isomorphisms are constructed from quotient equivalences and cokernel universal
   properties; the choice of comparisons is fixed by their projection equations.
3. No statements are split off and no holes or nodes are added. Read the two proved
   private helpers: exactness supplies the module cokernel, the adjunction transports
   it to sheaves, and the first isomorphism theorem yields the projection-compatible
   comparison. The zero module, zero ideal, unit ideal and first level n=0 require
   no nonzero assumption; the helper is used at the positive exponent n+1.
   Verdict: true, appropriately strong, and no forbidden arbitrary witness selection.
4. Searched Lean sources with quotient/tilde and multiplication-range terminology,
   and ran an independent Mathlib grep search for ideal products and the surjective
   first isomorphism theorem. Found the candidate's two copied helper proofs already
   in the ideal-section dependency. Replaced those copies by existing proved helpers,
   using the landed `CoherentFormalModuleAffineOpenSectionsAdic` module's `import all`
   pattern; removed the two now-unnecessary direct imports. The remaining cokernel
   transport and level comparison are not supplied by the searched declarations.
   Read `dag/units/sk-thm-p1.json`, including its `realized` fields: this auxiliary
   node is not itself a unit statement or step, and the route and all original
   proof-dependency nodes stay. Verdict: shortened below the unit level; no bypass.
5. Compared the existing node with the sandbox node and checked that `proof_deps`
   equals the union of its steps' `uses`. Updated the first step to say the two helper
   calculations are reused, rather than locally proved. The node records the actual
   range calculation, cokernel transport, first-isomorphism step and naturality
   assembly; `proof_origin` cites Lemma 087W. The unit record is unchanged. Read the
   source at https://stacks.math.columbia.edu/tag/087W (the literature checkout is not
   on this machine). Verdict: Lean and DAG agree; no new-node requirements apply.

Changed: removed duplicate `product_qc` and `multiplication_range` proofs, reused
existing helpers by a proof-only `import all`, removed redundant direct tensor/image
imports, and corrected the report and node proof description. The existing public
proof, cokernel transport and single-level comparison are otherwise unchanged.
