## What changed

Proved `AlgebraicGeometry.locallyOfFinitePresentation_iff_of_fppf_source_family`
in the assigned module, preserving its statement, universes and public imports.
The reverse implication chooses one covering member and one preimage per point
of `X`. The coproduct of this family has index type `X`, so it exists in
`Scheme.{u}` even for an original index type `I : Type v`. Its induced map is
flat and locally of finite presentation by `IsZariskiLocalAtSource.sigmaDesc`,
and surjective because each point has its chosen preimage in its component.
Coproduct extensionality identifies its composite with the coproduct map of
the composites, which is locally of finite presentation by the same locality
lemma. The existing proved source-library theorem
`LocallyOfFinitePresentation.of_comp_of_flat_of_surjective` finishes the proof.
The forward implication is composition.

Added one private proof import,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
and retained the private import `Mathlib.AlgebraicGeometry.Limits` for
coproducts. Updated the item's DAG proof, proof dependencies and origin;
removed both obsolete top-level tool-use entries. Added a node attaching the
existing singleton descent theorem, without adding a Lean declaration.
No other existing module, definition, statement, public import or node changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.locallyOfFinitePresentation_iff_of_fppf_source_family`
(node `lem-trf-lfp-fppf-source-locality`).

Zero holes left in the item; zero holes added; zero split off.
The new attachment node names a theorem already proved in the adopted source.
This is a proof, not a decomposition into new unproved statements.

The final module compiled cleanly through `lcompile.py` in 2.2 seconds.
Delivery compilation and its axiom probe provide the final mechanical check.
No nonemptiness, smallness of `I`, quasi-compactness, separation or Noetherian
hypothesis was added. The empty `X` case uses an empty coproduct. If `I` is
empty, joint surjectivity already forces this case. Repeated selected members
cause no problem: each selected point still has its own component preimage.

## No longer needed

Removed these private imports:

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`

The following old proof dependencies are not used by the item's assembly:

- `lem-weil-pbc-affine-opens-basis`
- `lem-trf-fppf-covering-base-change`
- `lem-pc-fppf-affine-refinement`
- `lem-a1-locally-ringed-space-affine-adjunction`
- `lem-weil-pbc-flat-morphism-affine-criterion`
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`
- `lem-trf-finite-affine-composite-presentation`
- `def-weil-pbc-finite-type-algebra`
- `lem-a1-finite-affine-family-fppf-algebra`
- `lem-trf-finite-presentation-fppf-source-algebra`

In particular, the proof does not import the unproved modules
`Sheaf.AlgebraicGeometry.FiniteAffineCompositePresentation` and
`Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineFamilyFppfAlgebra`, or the
refinement module. The proved singleton source-descent theorem already carries
the required affine reduction and algebra argument; the family-to-singleton
step only needs a coproduct. These are removals from this item's dependencies,
not withdrawals of nodes or modules that may have other consumers.
Removed old tool-use approvals `lem-pc-fppf-affine-refinement` and
`lem-a1-finite-affine-family-fppf-algebra` because neither is used here.

## Where the brief, the DAG or earlier work was wrong

The old searches correctly identified the source-library singleton theorem,
but did not exploit the short family reduction through coproducts. The only
universe subtlety is that `I : Type v` need not be `u`-small. Selecting one
member for each point of `X` resolves it without changing the statement.
The original docstring retains the valid expanded affine argument; the Lean
proof uses the existing singleton theorem for that part, and the DAG now
records the actual assembly. No mathematical statement was corrected.
The item does not realize the statement or a proof step in its unit's
`realized` field, and this generic scheme-theoretic simplification does not
change the unit or chapter route.

## New nodes

`lem-trf-lfp-flat-surjective-source-descent` attaches the existing proved
`AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective`
in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
Source: Stacks 02KL, locally finite presentation case; the complete adopted
Lean proof at lines 62-152 was read. Its hypotheses are exactly flatness,
surjectivity and local finite presentation of the source map, together with
local finite presentation of the composite. It has no quasi-compactness
hypothesis and handles empty schemes. It is an existing theorem attachment,
not a new unproved lemma or a renamed copy of the family statement.
LeanSearch, LeanFinder/Loogle and grep searches were run, and an exact scan of
DAG declaration attachments found no node for this singleton theorem.
Blueprint searches for `02KL` and `finite presentation source` found no
matching source-descent node. The `02KL` blueprint hit concerns different
fpqc/base-change properties. No new Lean module or change record is needed.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
