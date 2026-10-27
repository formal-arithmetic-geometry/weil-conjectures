## What changed

Filled `AlgebraicGeometry.PurityVectorBundle.lineZeroGeometry` in
`lean/Sheaf/Paper/LineZeroGeometry.lean`, preserving its signature and every public import.
Reused `VectorProjectiveCompletion.exists_projective_completion` and transported its
compactification through `V.phi`, retaining the specified normalized chart equations.
Local frames give smoothness of relative dimension one. A proved private helper
identifies the closed image of a section with its source;
the source-library finite-locally-free Cartier criterion gives the Cartier property
both before and after arbitrary base change. Flat stalk localization, the kernel-stalk
formula, and the Noetherian
one-equation dimension theorem give the displayed stalk dimensions. The final pullback
isomorphism is constructed explicitly from the frame, affine-space base change,
`AffineSpace.SpecIso`, and `MvPolynomial.uniqueAlgEquiv`; its two morphism equations
are proved, including evaluation at zero.

Added private proof imports for `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion`,
`WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier`, and
`Mathlib.Algebra.MvPolynomial.Equiv`, and `Mathlib.RingTheory.Flat.Localization`. Updated the item's existing node in `proof`,
`proof_deps`, `proof_origin`, and removal of obsolete `tool_uses` only. No other module,
statement, definition, universe, or attribute changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.PurityVectorBundle.lineZeroGeometry`
(node `lem-pur-line-zero-geometry`). Original holes: 1; closed: 1; remaining in this
module: 0; added elsewhere: 0; split off: 0. This is a proof from existing declarations,
with no new holes. The Cartier argument uses the already-proved
`AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat`
(node `lem-pc-cartier-criterion`) rather than the still-unproved smooth-curve-section
wrapper. No claim is made that all transitive proof dependencies are already proved.

The theorem statement was compared byte-for-byte with the original and is unchanged.
The constructed polynomial chart works for every coefficient ring, including the zero
ring, nonreduced rings, and arbitrary nonflat or non-Noetherian base changes. No point
is chosen on an empty base; all pointwise assertions quantify over supplied points.

## No longer needed

Removed these private imports from this module:

- `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`
- `WeilConjectures.Compactification.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`
- `Mathlib.RingTheory.Localization.Submodule`
- `Mathlib.AlgebraicGeometry.Pullbacks`

Removed the following direct proof dependencies from this node:

- `lem-weil-pbc-symmetric-algebra-free-module-polynomial`
- `lem-weil-pbc-affine-morphism-relative-spec`
- `lem-weil-pbc-affine-morphism-permanence`
- `lem-weil-pbc-lft-pointwise-criterion`
- `def-weil-finite-type-morphism`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-weil-pbc-smooth-restrict-open-subschemes`
- `lem-weil-pbc-smooth-local-on-source`
- `lem-pur-projective-bundle-tautological-geometry`
- `lemma-nagata-relative-affine-space-open-immersion`
- `lem-weil-pbc-scheme-morphism-gluing`
- `pqf-def-locnoeth`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-closed-immersion-base-change`
- `lem-weil-pbc-fibre-product-affine-spectra`

Projective chart construction and gluing are already supplied by the existing complete
projective-completion theorem, so this item does not redo those steps. Finite-type
properties come from that same theorem; smoothness uses target locality of the
fixed-relative-dimension chart definition. The same Cartier criterion also gives the
arbitrary-base-change assertion without a separate closed-immersion base-change proof.
The direct symmetric-algebra polynomial calculation is replaced by the existing frame
specification and the explicit one-variable polynomial equivalence.

Removed the obsolete approved tool entries
`lem-weil-pbc-affine-morphism-relative-spec` and
`lemma-nagata-relative-affine-space-open-immersion`; retained
`sbc-lem-affine-space-smooth` in its original order. These removals concern direct
uses by this item. Dependencies internal to the reused projective-completion theorem
remain needed; no upstream declaration or module is withdrawn. No whole-library
module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original nine-step plan duplicated existing
proved projective-completion and frame APIs. The DAG now records the shorter actual
argument and the already-proved finite-locally-free Cartier criterion. The latter is
used only for its geometric invertible-ideal conclusion; no cohomological purity
theorem or prescribed unit realization is bypassed. Its use is recorded in proof
dependencies;
no new maintainer tool approval was inserted. Target locality is used for fixed
relative dimension, rather than the old source-local lemma about smoothness alone.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
