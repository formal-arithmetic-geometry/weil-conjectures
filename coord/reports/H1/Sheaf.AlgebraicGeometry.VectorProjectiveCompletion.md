## What changed

Proved `AlgebraicGeometry.VectorProjectiveCompletion.exists_projective_completion` with its
original statement. The proof constructs a presentation from the existing projective-bundle
realization of O plus F; constructs the dehomogenization by explicit mutually inverse ring
maps; constructs and normalizes every projective frame chart; then glues the open immersion
on the locally directed cover by inverse images of affine base opens. It proves the precise
image, uniqueness, frame compatibility, Noetherianity, finite type, separatedness, compactification
and rank-zero clauses. No affine intersection is assumed affine.

Moved the seven existing definitions, with names, signatures and bodies unchanged, to
`VectorProjectiveCompletionData`; the original module publicly imports it. This permits the
local construction modules to import the definitions without a cycle. The change record is
`coord/changes/H1-vector-projective-completion-data.md`. The initial consumer scan found no
Lean importers. During delivery, `FiniteRingBundleSectionOrientation` landed with an import
of this module; it needs no edit and is recorded in the change record. Unfinished DAG
parents and the unit route retain the original theorem.
No adopted source-library file or target statement was edited.

The generic dehomogenization proof treats a graded algebra abstractly instead of unfolding
its concrete symmetric-algebra quotient. This avoids the elaboration blowup encountered in
the first concrete formulation. It is an algebraic abstraction, not a split to evade the
single-file time limit. All new statements are proved in this delivery.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.VectorProjectiveCompletion.exists_projective_completion`.

Added zero holes. No `sorry` remains in any delivered module. The following new results are
proved, rather than deferred decompositions:

- `SymmetricAlgebra.exists_dehomogenization`.
- `AlgebraicGeometry.VectorProjectiveCompletion.exists_projectivePresentation`.
- `AlgebraicGeometry.VectorProjectiveCompletion.exists_affineDehomogenization`.
- `AlgebraicGeometry.VectorProjectiveCompletion.exists_frameModel`.

Existing project dependencies may still contain their own named holes, including the
projective-bundle realization and relative projective-space interfaces; those remain their
existing items. No such hole is duplicated or hidden in a definition. There are no new axioms,
no arbitrary existence-witness definitions, and no target changes.

## No longer needed

No existing module or declaration is withdrawn. Closure-level pruning is not claimed.
The following original proof imports are removed from the item:

- `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`: absolute Proj map composition,
  identity and basic-open formulas suffice for the local frame proof.
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`: used privately in the new frame module.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`: used privately in the presentation
  module to compare symmetric degree with powers of the degree-one image.
- `Mathlib.AlgebraicGeometry.Gluing`: the global proof uses the Mathlib locally directed
  open-cover API through `Mathlib.AlgebraicGeometry.Cover.Directed`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`: used privately in the new
  presentation module, whose realization supplies properness and rank-zero isomorphy.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`: the rank argument
  uses the restriction/free-sum API and `Modules.LocallyFreeRank` instead.

The original public imports are preserved through the data module. The new public imports
are for actual signatures; proof dependencies are private imports.

The original node's direct proof dependencies and maintainer-approved `tool_uses` list no
longer need these eleven wrapper nodes, so all eleven entries are removed from `tool_uses`:

- `lem-weil-pbc-quasi-coherent-symmetric-algebra`: the presentation theorem reuses the existing
  projective-bundle realization; its required symmetric section data remain used transitively.
- `lem-weil-pbc-symmetric-algebra-graded`: used in the presentation theorem, not separately in
  the global gluing proof.
- `lemma-nagata-relative-proj-exists`: actual relative-Proj construction and restriction cocone
  equations supply the maps; it remains represented by the existing relative-Proj interface.
- `lem-weil-pbc-symmetric-algebra-free-module-polynomial`: Mathlib's basis polynomial equivalence
  directly constructs the local coordinates; the node is retained as the corresponding local
  algebra dependency of the frame result.
- `prop-nagata-relative-proj-functoriality`: the local modules use the existing Proj API directly;
  the main theorem consumes their proved compatibility statements.
- `lem-weil-pbc-scheme-morphism-gluing`: Mathlib's locally directed cover gluing and hom_ext
  directly supply gluing and uniqueness.
- `lem-weil-pbc-finite-type-over-noetherian`: Mathlib gives locally Noetherian plus compactness
  for the proper projection.
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`: Mathlib gives local Noetherianity of an
  open immersion and Noetherian topology of the embedded source.
- `lem-weil-pbc-qc-open-immersion-finite-type`: compactness of the Noetherian source and the
  Mathlib morphism-property instances supply quasi-compactness and local finite type.
- `lem-sfb-finite-type-composition-base-change`: Mathlib composition instances suffice.
- `lem-weil-pbc-proper-fp-permanence`: Mathlib separatedness of an open immersion, properness
  implying separatedness, and composition suffice; no new diagonal argument is required.

Other original direct dependencies now occur inside the new local nodes or the unchanged
statement interface: `def-amb-finite-locally-free-module`,
`def-nagata-homogeneous-localization-degree-zero`, `def-nagata-relative-projective-space`,
`def-weil-proper-morphism`, and `lem-pur-projective-bundle-tautological-geometry`.
These are not assertions that those nodes are globally unused.

## Where the brief, the DAG or earlier work was wrong

The planned dehomogenization on a free affine frame alone is insufficient for the theorem's
quantification over every affine open. The proof constructs the equivalence for an arbitrary
section module M. A frame is used only for the separate projective-space comparison.

The rank-zero conclusion for the completion is already supplied by the existing
projective-bundle realization, so the completion's Proj need not be reconstructed for d=0.
The vector-bundle rank-zero isomorphism is proved from its existing trivialization maps.

An initial single LocalModels remainder was temporary working scaffolding. It has been
replaced by proved independent local results and is not part of this delivery. No remaining
statement is the original theorem under a new name.

All six delivery modules compiled together in import order through `lcompile.py --all`.
The main theorem compiled in 11.6 seconds; the longest supporting module, the frame model,
compiled in 29.1 seconds. The delivery command additionally performs its preflight checks.

## New nodes

`def-amb-vector-projective-presentation-data` attaches the seven exact moved definitions to
`VectorProjectiveCompletionData`; it changes their module ownership, not their semantics.

`lem-amb-symmetric-algebra-dehomogenization` attaches the fully proved general algebra theorem
`SymmetricAlgebra.exists_dehomogenization`; it requires no freeness or Noetherian hypothesis.

`lem-amb-vector-projective-presentation` attaches the fully proved construction and properness
of the presentation of O plus F, including the rank-zero structural isomorphism.

`lem-amb-vector-projective-dehomogenization` attaches the fully proved affine equivalences,
normalizations and restriction compatibility as scheme maps.

`lem-amb-vector-projective-frame-model` attaches the fully proved polynomial and projective
frame comparisons, including the structural map and standard-open equations.

All nodes are in `dag/nodes/sec-smooth-purity/`, with the original chapter/unit, source,
proof in words, dependency records and Mathlib search records. The original node's proof,
proof dependencies and Lean attachment follow the implementation. The change record is
`coord/changes/H1-vector-projective-completion-data.md`.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
