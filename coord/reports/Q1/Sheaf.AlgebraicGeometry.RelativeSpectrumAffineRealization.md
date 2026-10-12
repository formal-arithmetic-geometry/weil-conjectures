## What changed

Proved `AlgebraicGeometry.exists_affine_structure_algebra` with its statement unchanged.
The spectral pieces and their transition maps form an equifibered relative gluing datum,
using the already proved quasi-coherent algebra affine-inclusion theorem. Mathlib glues
this datum; its range/preimage equality proves affineness.

Added `Sheaf.AlgebraicGeometry.RelativeSpectrumStructureAlgebra`, containing the fully
proved theorem `AlgebraicGeometry.structure_algebra_iso_of_affine_spectral_charts`.
It constructs the comparison on affine sections, extends it by the basis theorem,
checks algebra compatibility, and inverts the resulting isomorphism. The new module
uses only Mathlib and the existing algebra-sheaf definition. Both new proof imports
in the item are ordinary imports. Existing public imports and signatures are unchanged.
Updated the item's proof dependencies and added the helper's node.

## Proved and sorry left

- `AlgebraicGeometry.exists_affine_structure_algebra`: proved; the item's sole sorry is removed.
- `AlgebraicGeometry.structure_algebra_iso_of_affine_spectral_charts`: proved in full.
- No sorry remains in either delivered module; none is split off or added elsewhere.

Both modules compile locally without warnings. The construction permits an empty base,
empty affine opens and zero section rings. The helper does not assume quasi-coherence:
its cartesian spectral charts supply exactly the local isomorphisms needed.
Existing dependencies of the affine-inclusion theorem remain the responsibility of their nodes.

## No longer needed

Pruned `lem-weil-pbc-morphism-into-affine-scheme` from this item's proof dependencies.
The argument uses the explicit canonical affine charts and never needs the general
bijection for morphisms into an affine scheme or its final uniqueness argument.
Its Mathlib module `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` is not added as a
separate proof import; affine-chart infrastructure may still import it transitively.

No original import is removed. The affine spectrum, affine-inclusion, relative-gluing
and affine-morphism dependencies remain. The sheaf-morphism-on-basis dependency is
retained through the new, fully proved helper. No unit statement or unit proof step
is bypassed, and no other Sheaf or WeilConjectures module is claimed to be globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The affine-inclusion theorem is already proved and
fits the construction. In this compiler, instance inference does not recover the gluing
datum from its functor projection; the proof supplies the existing Mathlib instances
explicitly. The local clone has no literature checkout, so the cited Stacks proofs
were read at the official pages for Tags 01LP, 01LV and 01LX. LeanSearch returned an
Internal Server Error; semantic search and source searches were still available.

## New nodes

`lem-weil-pbc-relative-spectrum-structure-algebra` records the compatible-chart algebra
comparison, the section-isomorphism part of the original plan. It is fully proved in
`Sheaf.AlgebraicGeometry.RelativeSpectrumStructureAlgebra`; it introduces no unfinished
work. Its source is the first paragraph of the proof of Stacks Tag 01LV, with the
basis extension theorem and the spectrum sections isomorphism as proof dependencies.
No change record is needed: no existing definition or statement was changed.

## Second reading by Q1

1. Statements and definitions: PASS. I diffed the existing module against the
repository version: its notation, docstring and theorem signature are byte-for-byte
unchanged; only the proof and two ordinary proof imports were added. There is no
existing definition change and no change record is required. The new helper assumes
precisely a cartesian chart over each affine open and compatibility under affine
inclusions, and concludes an isomorphism in Under S.sheaf.

2. Proof and axioms: PASS for this delivery's holes. Both modules compiled cleanly
with lcompile.py. Neither contains sorry, an axiom, unsafe, opaque, extern,
implemented_by or a kernel-check bypass. A scratch probe of both declarations gave
only propext, Classical.choice and Quot.sound for the new helper. The existing
exists_affine_structure_algebra additionally has sorryAx through the still-open
quasiCoherent_affine_section_baseChange dependency; its local hole is closed, but
it is not yet an axiom-clean target proof. No hole is added or split off here.

3. New statement: PASS. I read the whole chart-comparison proof and the official
Stacks pages Tags 01LP, 01LV (first proof paragraph), and 01LX (1), (3). The helper
isolates only the section comparison after charts are supplied, not the original
existence theorem. Base change makes k_U an open immersion; the pullback image
formula identifies its range with f-inverse(U), making its sections map invertible.
The restriction calculation uses hres with the correct opposite-category direction.
GammaSpecIso naturality supplies the ring-map compatibility. Basis extension and
basis isomorphism detection yield b, and the explicit appLE calculation checks the
O_S-structure equation before forming the Under isomorphism and inverting it.
The empty base, empty affine open and zero-ring chart all satisfy these same
calculations, with no nonemptiness or nonzero-ring assumption. I searched the library
and Mathlib for structure_algebra, spectral_charts, relativeSpec, relative_spec and
basis extension, and ran LeanFinder with a different cartesian-chart query through
msearch.py. Results give the constituent absolute-spectrum and basis lemmas, not a
packaged comparison or a duplicate existence result. There are no unfinished
split-off statements.

4. Route, imports and pruning: PASS after import cleanup. The outer proof uses the
existing affine-inclusion theorem to construct F, t and the equifibered datum, then
Mathlib relative gluing for the affine inverse images and the cartesian charts.
I read the relative-gluing range and pullback declarations, the pullback image
formula, isoSpec_inv_appTop, and the basis extension/isomorphism declarations.
This is the planned gluing and basis-comparison route. sk-thm-p1.json realized lists
neither this item nor the pruned morphism-into-affine theorem as a unit realization;
no unit statement or step is bypassed. Of the old proof_deps, only
lem-weil-pbc-morphism-into-affine-scheme is genuinely unused. The old direct
lem-weil-pbc-sheaf-morphism-on-basis dependency moves into the new helper, so it is
still used transitively and is not pruned. I removed the helper's unnecessary public
Pullbacks import (proof infrastructure already comes through PullbackCarrier) and
redundant public AffineScheme import (already public through CommAlgebraSheaf's
Modules.Sheaf import). The remaining new imports are proof-only ordinary imports.

5. Nodes: PASS. The existing node differs only in proof, proof_deps and proof_origin;
its steps match the actual Lean construction and their uses have union proof_deps.
The new node's signature matches the Lean verbatim, its proof follows the four
sections of the helper, and its chapter, unit, source, creator and blueprint origin
are present. Its recorded searches have logged queries. No change to the unit record
was needed.

Second-reading changes: removed two unnecessary public imports from the new helper;
added this review and the explicit upstream sorryAx qualification. No mathematical
proof or statement was changed. Holes closed: exists_affine_structure_algebra (one
of one original holes); holes added: none. The fully proved new helper is an
additional declaration, not a decomposition into lower holes.
