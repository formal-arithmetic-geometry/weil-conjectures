## What changed

Proved `AlgebraicGeometry.exists_affine_neighbourhood_quasiCompact_open_of_fiber_open`
in `Sheaf.AlgebraicGeometry.FibreOpenAffineReduction`, with the original signature and
public imports unchanged. The proof uses only Mathlib. Two proved private helpers give a
compact open neighbourhood of a compact subset inside a prescribed scheme open, and
preservation of geometric reducedness under precomposition by an open immersion.

The fibre is Noetherian locally and compact, so its prescribed open T is compact. Lift T
along the fibre embedding to an ambient open, intersect with the inverse image of an
affine base neighbourhood, and take a finite affine subcover of the compact image of T.
Pull this compact ambient open back to the localized family. The open image in Y is
exactly the chosen ambient open, which proves the requested equality in the lattice of
fibre opens. Flatness, local finite presentation, quasi-compactness, quasi-separatedness
and geometric reducedness follow from base change, composition and open restriction.
The empty-open case is included without a nonemptiness assumption.

Updated the item's own DAG proof, proof dependencies and proof origin to describe this
construction. No shared interface or other existing module changed.

Validation: the final module compiled through `lcompile.py` in 3.8 seconds, with no
errors or warnings. The delivery preflight supplies the declaration axiom check.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.exists_affine_neighbourhood_quasiCompact_open_of_fiber_open`
(node `lem-trf-fibre-open-affine-reduction`). Added 0 holes; 0 remain in the delivered
module. Both private helper theorems have complete proofs. No split-off statements.

## No longer needed

Removed redundant proof imports `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Properties`, `Mathlib.AlgebraicGeometry.Pullbacks`, and
`Mathlib.AlgebraicGeometry.PullbackCarrier`; the unchanged public imports already
provide their declarations. The only explicit proof import needed is
`Mathlib.AlgebraicGeometry.Noetherian`.

The direct proof does not need the separate DAG dependencies
`lem-weil-pbc-lfp-affine-opens-finite-presentation` and
`lem-weil-pbc-quasi-separated-affine-cover-criterion`. Composition with the open
immersion gives local finite presentation, and the quasi-separated-space property
restricts along its open embedding. Removed these from this node's proof dependencies.
No existing source declaration or library module is withdrawn, and no unit route is
bypassed. No Sheaf proof-dependency modules were imported.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The stated plan is valid. Its explicit residue-field
identification after localization is unnecessary in Lean: construct the compact open
inside h⁻¹(S₀) in Y first, then pull it back to the localization. The open-image formula
proves the exact fibre-open equality without transporting between localized fibres.
The Mathlib fibrewise characterization of geometric reducedness also avoids separate
residue-field comparison arguments. Source read: Stacks `more-morphisms.tex`, Tag 055W,
first paragraph of the proof of `lemma-fibre-geometrically-connected-reduced`; the
current blueprint unit `sk-i-curve-zero` and its realized route were also checked.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
