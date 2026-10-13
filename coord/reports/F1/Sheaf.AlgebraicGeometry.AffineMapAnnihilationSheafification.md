## What changed

Proved `AlgebraicGeometry.affine_map_annihilation_sheafification` with its signature and
existing public imports unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover`,
`Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison` (with `import all`),
and `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`.

Two fully proved private helpers supply the linear
identification of global sections of an associated module on an affine scheme, and
annihilation detection using the singleton top affine cover. The main proof constructs
kernel/cokernel isomorphisms via exactness and transports the annihilator inequalities
through global-section linear equivalences. Updated the item's DAG proof and direct
proof dependencies to match this route. No definitions or existing signatures changed.

The module compiled cleanly with lcompile.py. Import-direction checks permit the new
Sheaf detection and source-library section-comparison imports. The argument includes
exponent zero, zero modules, the unit or zero ideal, and the empty affine scheme: the
linear equivalences and singleton-cover proof do not require nonzero objects or points.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.affine_map_annihilation_sheafification`
(lem-weil-pbc-affine-map-annihilation-sheafification).
No sorry remains in the delivered module; no holes added or split off.
Both new private helpers are fully proved. Kernel preservation is reused from the
existing private theorem in AffineDerivedTildeHomologyComparison via `import all`. Dependency closure axiom status is
checked by the delivery probe; this report does not claim unrelated imported results
are proved.

## No longer needed

No original public import was removed: the existing two public imports are preserved.
The repair removes the duplicate private `AlgebraicGeometry.tilde_preservesKernel`
and its direct proof import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`; this module remains
a transitive dependency of the imported existing kernel-preservation theorem.
The direct DAG dependency `lem-weil-pbc-quasi-coherent-module-kernel` is replaced by
`new-affine-derived-tilde-homology-comparison`, whose module provides that theorem.
The earlier repair removed the redundant added proof imports
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` and
`Mathlib.Algebra.Category.ModuleCat.Kernels`; their declarations are already available
through the retained imports. This removes import edges, not modules from the target closure.
The main proof no longer directly needs these planned nodes/modules:

- lem-weil-pbc-module-pullback-ideal-power-product-image /
  Sheaf.AlgebraicGeometry.ModulePullbackIdealPowerProductImage;
- lem-weil-pbc-ideal-times-quasi-coherent-affine-sections /
  Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections;
- lem-weil-pbc-quasi-coherent-module-cokernel-image /
  Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage.

The last two remain transitive dependencies of the affine annihilation-detection theorem;
this delivery prunes their direct edges only, and does not claim they leave the targets'
closure. The pullback-product comparison is bypassed entirely by detection on X itself.
No node realizing the unit's own statement or proof steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The planned ideal-product pullback comparison
is unnecessary for an isomorphism of affine schemes. The main missing glue can be proved
from existing functor comparisons and section equivalences, without new stated nodes.
The cited Stacks source files are absent on this machine; the corresponding public
Stacks pages for Tags 01IB, 01I7 and 0889 were consulted instead.


Repair of the returned delivery: the duplicate-statement check correctly found that
`AlgebraicGeometry.tilde_preservesKernel` was already proved in
`Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`. The earlier review
incorrectly treated private visibility as preventing reuse: `import all` exposes the
existing helper to this proof. Removed the duplicate declaration completely, imported
the existing module with `import all`, and retained the application of the existing
helper in the main theorem. No other module, signature or visibility changed.
The previous second reading described the superseded delivery and has been removed
so that the independent reader can review the repaired version.

## Second reading by F1

1. Compared the only delivered Lean module with the repository version using diff,
   and independently compared the existing theorem signature byte for byte. PASS:
   the signature, existing docstring, public imports and visibility are unchanged.
   The new section equivalence explicitly composes existing isomorphisms; it chooses
   no arbitrary witness from an unproved existence theorem. No change record is needed.
2. Compiled the delivered module locally with lcompile.py: clean, 8.7 seconds.
   Compiled a fresh scratch copy with #print axioms for the main theorem, both new
   private helpers, and the imported private tilde_preservesKernel. PASS: all four
   depend only on propext, Classical.choice and Quot.sound, with no sorryAx.
   There are no sorry, forbidden declarations, or hollow definitions in the module.
3. No statements were split off and no holes were added. PASS. Read both new helpers:
   the section equivalence is over the correct global-section ring, and the zero
   detection helper transports the annihilator along a linear equivalence and uses
   exactly the singleton top affine cover. Checked t = 0, zero modules, zero/unit
   ideals and the empty affine scheme; neither helper excludes these cases.
   Local rg confirmed that the kernel-preservation proof is reused rather than
   duplicated. An independent Loogle query confirmed LinearEquiv.annihilator_eq.
4. Read the proof from its conclusion through the kernel/cokernel comparisons and
   the imported affine-cover detection theorem. PASS: the main hole is closed from
   existing proved results, without a renamed restatement or new lower holes.
   Searched Mathlib and upstream section/tilde comparison declarations; no shorter
   complete bridge was found. Removing each of the three added proof imports in
   separate scratch copies fails respectively on the affine detection theorem,
   kernel preservation/restriction limits, and sectionsRestrictFromSpecLinearEquiv.
   These imports are necessary and proof-only. The report accounts for all four
   removed old proof_deps, including quasi-coherent module kernel. Checked
   dag/units/sk-thm-p1.json realized: none of the removed dependencies realizes
   the unit statement or a step, so its route is preserved. Pruning here removes
   direct dependencies; no whole-module closure reduction is claimed.
5. Compared the delivered node with its repository version. PASS: only proof,
   proof_deps and proof_origin change. The dependencies are exactly the union of
   the proof steps' uses; their records identify the reused Lean declarations or
   Mathlib matches. The three steps accurately describe the implemented exactness,
   section equivalence and annihilator detection argument. There are no new nodes.

Second-reading changes: corrected stale attribution of import removal in this report,
and added this independent review and fresh axiom evidence. No Lean or node repair
was necessary. One existing hole closed; zero holes added; this is a proof, not a
decomposition. The required delivery dry run and delivery follow this review.
