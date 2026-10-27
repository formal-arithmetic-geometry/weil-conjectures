## What changed

Proved `AlgebraicGeometry.RingedSpace.exists_generatedIdeal_tensor` with its statement
unchanged. Constructed multiplication using the sectionwise tensor lift and module
sheafification adjunction; proved uniqueness by tensor extensionality. Proved the
local finite-sum characterization, the ideal axioms, containment of the original
map, and minimality. Four proved private helpers give local-to-global membership
for mono ranges, local lifting along epis, the image-range criterion, and local
lifting from the tensor presheaf.

Updated the existing node's proof, proof dependencies, and proof origin to match
the direct adjunction and covering-sieve argument. No definitions, public
signatures, or public imports changed. No new modules or nodes.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.RingedSpace.exists_generatedIdeal_tensor`
(node `lem-weil-pbc-ringed-space-generated-ideal-tensor`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.

## No longer needed

Removed private imports:
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`.
- `Mathlib.Topology.Sheaves.Sheafify`.

The proof no longer uses `lem-pc-sites-sheaf-tensor-bilinear-universal`: the
statement's tensor object is directly a sheafification, so its adjunction and
ordinary `TensorProduct.lift` supply existence and uniqueness without comparing
it to the monoidal tensor. Nor does it use
`lem-weil-pbc-stalk-sheafification-space` or `def-weil-pbc-module-stalk`:
Mathlib's local surjectivity of the sheafification unit gives the needed
neighbourhood lifts directly. Removed these three node dependencies from the
proof route. This is pruning of this item's dependencies only; no upstream
module or declaration is withdrawn. The unit route stays unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement. The planned passage through stalks and
a separate tensor comparison is unnecessary for the actual tensor definition.
The local-image step requires more than just the cokernel map being epic and
annihilating multiplication: the proof explicitly uses local lifting along the
epic image factor and local-to-global membership for the image mono. The latter
follows by evaluation preserving kernels of mono exact sequences and by sheaf
separatedness; it also handles the empty open.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
