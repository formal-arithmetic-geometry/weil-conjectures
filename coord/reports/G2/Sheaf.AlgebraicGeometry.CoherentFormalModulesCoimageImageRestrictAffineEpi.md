## What changed

Completed `AlgebraicGeometry.coherentFormalModules_coimageImage_isEpi_restrict_affine`
without changing its signature or public imports. Two proved private helpers construct
the affine equivalence from the existing spectrum equivalence and prove preservation
of cokernels by restriction from ambient cokernel closure. On the affine open,
Mathlib transfers abelianness from finite modules over the Noetherian completion.
Kernel and cokernel preservation then transport the comparison isomorphism; inclusion
and evaluation give the required component epimorphism. The node records this route.

Added proof imports of `CoherentFormalModulesIsoEquivalence`,
`CoherentFormalModulesRestrictionKernels`, `Mathlib.Algebra.Category.FGModuleCat.Abelian`,
and `Mathlib.CategoryTheory.Abelian.Transfer`. The first two modules landed during
this session through P4; the saved attempt's duplicate sandbox modules were removed
from the delivery, and the proof now uses the landed signatures.

Single-file compilation through `lcompile.py` is clean. The original kernel and
cokernel instances remain arbitrary. The affine category's abelian structure is
local proof data, not a global instance. Zero arrows, the empty affine open, and
zero/unit ideals follow the same equivalence and universal-property argument.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.coherentFormalModules_coimageImage_isEpi_restrict_affine`
(node `lem-weil-pbc-coherent-formal-coimage-image-affine-epi`).
No `sorry` remains in the item's module. No holes or new modules are added.
This is a proof from existing project statements, not an axiom-free closure:
`AlgebraicGeometry.coherentFormalModules_iso_equivalence` is now proved from existing
project dependencies, while
`AlgebraicGeometry.coherentFormalModules_restriction_preservesKernel` remains an existing
open dependency. Their existing nodes are
`lem-weil-pbc-coherent-formal-modules-iso-equivalence` and
`lem-weil-pbc-coherent-formal-modules-restriction-kernels`.

## No longer needed

Removed the following direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`

The direct stabilized-kernel construction dependency
`lem-weil-pbc-coherent-formal-module-kernel` is replaced by open-kernel preservation.
It remains a transitive dependency of that existing statement; no claim is made
that it or the other removed modules leave the targets' import closure.
The direct affine-section calculation and sectionwise first-isomorphism glue are
unnecessary here: Mathlib's categorical comparison transport supplies them.
The attempted import of `CoherentFormalModulesFiniteProducts` is also unnecessary;
finite products transfer from the finite-module category along the affine equivalence.
The saved attempt's `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian` import
is unnecessary because Noetherianity of an open subscheme is inferred directly.
No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The saved attempt was incomplete: it had unregistered duplicate helper modules and
its scheme-isomorphism helper did not compile. P4's newly landed nodes now provide
both required interfaces, so those duplicate files are not delivered.
The original plan was mathematically valid but did not expose open-kernel
preservation as a usable dependency. The existing restriction-limits theorem
cannot be imported here, since it imports global formal abelianness, which depends
on this item. The separate preservation-of-kernels theorem avoids that cycle.
There is no statement dispute or forced adaptation. The unit record `sk-thm-p1`
is unchanged; this categorical argument changes only the node-level glue.


## Second reading by G2

1. PASS: Compared the sole delivered Lean module with the repository version and
   mechanically checked the existing theorem signature byte for byte. The three
   public imports and all public declarations are unchanged. No definitions,
   additional hypotheses, or weakened conclusions were introduced; no change
   record is required. Scratchpad modules are not delivered.
2. PASS: Independently compiled the module with lcompile.py without warnings or
   errors. It contains no sorry or prohibited declaration. A scratch copy with
   #print axioms for the theorem and both private helpers reports exactly propext,
   Classical.choice, Quot.sound, and sorryAx from existing dependencies. There is
   no new data definition or arbitrary witness exposed downstream: equivalences
   are used locally within proposition proofs to transport categorical properties.
3. PASS: No statement or hole was split off and no new module or node is delivered.
   The two private helpers are fully proved components of the recorded argument.
   Checked the affine ideal round trip, full-subcategory reflection of cokernels,
   and applicability to zero arrows, empty affine opens, and zero/unit ideals;
   these use no extra nonemptiness or proper-ideal assumption.
4. PASS: Searched the library by comparison transport and checked the parallel
   monomorphism proof, plus an independent Lean Finder query on kernel/cokernel
   preservation. Mathlib's PreservesCoimageImageComparison.iso is already the route
   used here; no shorter usable public result was found. Every added proof import
   supplies a required equivalence, preservation result, completion Noetherianity,
   cokernel closure, or abelian transfer/finite-module instance. All four removed
   direct imports are reported above. The sole removed old proof_deps entry is
   lem-weil-pbc-coherent-formal-module-kernel, also reported above. It remains
   transitive; no whole-closure pruning is claimed. Read sk-thm-p1's realized
   statement and steps: this changes only lower categorical glue and bypasses
   no unit-level realization.
5. PASS: Compared the old and delivered node. Only proof, proof_deps, and
   proof_origin change. The dependency union agrees with the four Lean argument
   steps, including formal restriction objects supplied transitively by kernel
   preservation. The node's statement and Lean record remain unchanged.

Second-reading changes: corrected the report's stale assertion that the
scheme-isomorphism equivalence itself still has a hole; it now has a proof,
although its dependencies and this theorem's axiom closure remain open. Added
this review and the independent search/axiom evidence. No Lean or DAG repair was
needed. Closed 1 of 1 original holes; added 0 holes, with 0 statements split off.
