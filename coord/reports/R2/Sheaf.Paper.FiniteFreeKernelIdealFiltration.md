## What changed

Proved `AlgebraicGeometry.finite_free_kernel_ideal_filtration` without changing its
signature, universes, visibility, or existing docstring. The proof uses
`Finite.induction_empty_option`, transports along free-module isomorphisms, proves
the empty-coordinate case directly, and appends one short exact sequence at each
successor stage. The finite chain is constructed explicitly with an `if` on its
index; no module data is chosen from an unproved existence statement.

Added two fully proved helper modules and their nodes:

- `Sheaf.Paper.FiniteFreeKernelCoordinateStep`: constructs the coordinate inclusion,
  retraction and projection as coproduct maps, proves the kernel universal property,
  and transports the epimorphic image factorization to an ideal module.
- `Sheaf.Paper.QuasiCoherentSubmoduleIdeal`: constructs ideal sheaf data from the
  affine section ranges of an inclusion into the structure sheaf. Denominator
  lifting proves localization compatibility. A kernel lift gives the comparison
  map, and affine section bijectivity proves it is an isomorphism.

Updated the item's node proof and dependency list to match this induction. Its
statement and statement dependencies are unchanged. The unit record has no
realized statement or steps attached to this item; the geometric coordinate
filtration route of Tag 01XF is preserved.

All three modules compile together, without warnings. Direct axiom checks of the
filtration theorem and coordinate step list exactly `propext`, `Classical.choice`,
and `Quot.sound`, so their transitive dependencies contain no `sorryAx` either.
The delivery tool performs its axiom probe on each module as well.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finite_free_kernel_ideal_filtration`
(node `lem-pqf-finite-free-kernel-ideal-filtration`).

Also fully proved:
`AlgebraicGeometry.finite_free_kernel_coordinate_step`
(node `lem-pqf-finite-free-kernel-coordinate-step`) and
`AlgebraicGeometry.quasiCoherent_submodule_ideal`
(node `lem-pqf-quasi-coherent-submodule-ideal`).

No `sorry` remains in the item or either new module. Holes closed: 1; holes added: 0.
This is a proof, not a decomposition into new proof obligations.

Edge cases checked in the argument: an empty index type gives a zero-length chain;
removing the distinguished coordinate from `Option PEmpty` gives a zero left
kernel; the zero map gives the unit ideal as its coordinate image; the zero
submodule gives zero ideal data. No step uses `Epi p`, affineness of X,
quasi-compactness, finite generation of the kernels, or cohomology vanishing.

## No longer needed

Removed the item's proof imports of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` and
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`, replacing them with
`Sheaf.Paper.FiniteFreeKernelCoordinateStep` and `Mathlib.Data.Fintype.Option`.
Kernel closure remains used in the coordinate helper, so it is not pruned from the
transitive proof closure.

The complete three-module proof does not use
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` or its node
`lem-weil-pbc-quasi-coherent-module-cokernel-image`. The local-image and affine
cokernel formulas of that theorem are unnecessary: the abelian image is a kernel
of a cokernel, so the smaller source-library closure theorems suffice. Its entire
proof-only import branch is unnecessary for this item; other callers may still
need it. All public imports of the assigned module are retained for its statement.
For completeness, the old direct proof dependencies
`lem-weil-pbc-quasi-coherent-module-kernel` and `pqf-def-coherent` now occur in
the helper nodes instead of the filtration node; both remain used transitively.
`def-weil-sheaf-of-modules-category` remains a direct dependency. Thus the only
old dependency no longer used anywhere in this argument is
`lem-weil-pbc-quasi-coherent-module-cokernel-image`.

Second reading also removed the redundant public import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` from
`Sheaf.Paper.QuasiCoherentSubmoduleIdeal`: its signature already sees
quasi-coherence through the ideal-module import, and its proof needs none of that
module's extra results. No other planned geometric step or unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's direct-image paragraph
suggested constructing inverse section maps on an affine basis and gluing them.
A shorter implementation constructs one global comparison by the kernel universal
property, after proving the necessary vanishing locally, and checks that comparison
on the affine basis. This avoids a separate gluing construction of morphisms.

The source file `literature/stacks-project/coherent.tex` is not present on this
machine. The cited coordinate paragraph of Tag 01XF was read at
https://stacks.math.columbia.edu/tag/01XF; the node proof origins label the Lean
implementations as agent-written explications of that argument. LeanSearch was
attempted for both helpers and returned Internal Server Error; no mathematical
absence verdict was inferred from that failure. LeanFinder/Loogle, local source
searches and blueprint/DAG searches found no duplicate of either helper.

## New nodes

`lem-pqf-finite-free-kernel-coordinate-step`, in
`dag/nodes/sec-abelian-varieties/lem-pqf-finite-free-kernel-coordinate-step.json`,
records the fully proved single-coordinate kernel short exact sequence. It uses
quasi-coherent kernel and cokernel closure, together with the ideal-recognition
helper; its four proof steps describe the actual coproduct and kernel constructions.

`lem-pqf-quasi-coherent-submodule-ideal`, in
`dag/nodes/sec-abelian-varieties/lem-pqf-quasi-coherent-submodule-ideal.json`, records
the fully proved recognition of a quasi-coherent submodule of the structure sheaf.
Its three steps describe the range-ideal construction, localization compatibility,
global kernel lift, and affine-basis isomorphism check. Both new nodes carry the
item's chapter/unit, ancestor and via chain, source, three search kinds, and Lean
signature records. There are no interface changes or change records.

## Second reading by R2

1. Compared every delivered module with the repository. Only the filtration module
   exists there; its declaration signature, universes, visibility and existing
   docstring are byte for byte unchanged. The helpers are new modules, with one
   new theorem each. No definition or existing interface changed, and no change
   record is required. The existing node changes only proof, proof_deps and
   proof_origin. Verdict: pass.
2. Compiled all three modules locally in import order, without errors or warnings.
   Scanned all three for sorry, axiom, unsafe, opaque, implemented_by, extern and
   sorryAx: none occurs. In a scratch copy, printed the axioms of all three public
   theorems: each lists exactly propext, Classical.choice and Quot.sound. The
   chain and ideal data are explicit constructions; the existential helper
   theorems are fully proved. Verdict: pass.
3. No statement is left split off with sorry. Read both new helper statements and
   their proofs: the coordinate result is one induction step, and ideal recognition
   is the comparison needed for its quotient, not a renamed filtration theorem.
   Checked empty coordinates, zero map, zero submodule, identity inclusion and
   the empty scheme; none requires an unstated hypothesis. The localization
   argument also handles f=0, where the basic open is empty. Independent LeanFinder
   search for a monomorphism from a quasi-coherent sheaf into O_X returned ideal-data
   constructors only; Loogle found the kernel universal-property lemma already
   used; Mathlib grep and local searches with image/structure/subobject/ideal
   variants found no duplicate geometric theorem. Verdict: pass.
4. Read the argument downward from the filtration theorem, and compared the
   coordinate step with Stacks Tag 01XF. Finite-type induction uses the source
   library's free functor and Mathlib's kernel/image/exactness transport results.
   Ideal recognition reuses denominator lifting, affine range and affine-basis
   isomorphism results. No shorter existing geometric theorem was found. The
   FreeGenerator import supplies Hom.app_presheaf_map, and LocallyFreeAffine
   supplies the affine-basis criterion. Proof-only imports are plain imports.
   Removed one redundant public import in the new ideal helper and recompiled.
   The No longer needed section now accounts explicitly for every old proof
   dependency. The unit's realized statement and step arrays are empty; the
   coordinate route and the enclosing unit are preserved. Verdict: pass.
5. Compared node signatures with the Lean statements, and checked proof steps,
   their uses unions, proof_deps and proof_origin against the implementation.
   New nodes have the required source, searches, creation, ancestor/via,
   chapter/unit and Lean records. The ideal node describes the actual range
   construction and global kernel lift; the coordinate node records cokernel
   then kernel closure for the image, rather than the unused image theorem.
   Verdict: pass.

Changes by the second reader: removed the redundant public quasi-coherence import
from the new ideal helper; completed the old-dependency accounting above; appended
this review. No proof or statement repair was needed. The delivery closes one
original hole, adds zero holes and leaves zero split-off obligations.
