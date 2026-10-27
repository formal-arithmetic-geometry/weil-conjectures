## What changed

Proved `AlgebraicGeometry.isQuasiAffineHom_iff_exists_relativeSpec_embedding` with its
signature unchanged, following the current four-step DAG plan. Quasi-affineness of all
affine-base inverse images supplies quasi-compactness and quasi-separatedness via the
Mathlib affine-local criteria. The existing `qcqs_relative_affinization_map` supplies
the algebra, relative spectrum and canonical charts. Composing each chart with
`Scheme.Spec.mapIso U.topIso.op` transports ambient-open sections to global sections
of the open subscheme; the chart equation then applies
`isOpenImmersion_and_quasiCompact_of_canonical_affine_charts`. The converse uses the
existing quasi-affine composition instance for a quasi-compact open immersion followed
by an affine morphism.

Added private proof imports of `Sheaf.AlgebraicGeometry.QcqsRelativeAffinizationMap`
and `Sheaf.AlgebraicGeometry.CanonicalAffineChartsQcOpenImmersion`. Public imports,
existing docstrings and all declaration signatures are unchanged. No node changes
are needed: the Lean argument implements the current node proof and dependencies.
The source read was Stacks `morphisms.tex`, lemma-characterize-quasi-affine (Tag 01SM).
Mathlib searches through LeanFinder, Loogle and grep found absolute quasi-affine
permanence results but no replacement for the relative construction.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.isQuasiAffineHom_iff_exists_relativeSpec_embedding`
(node `lem-trf-quasi-affine-relative-spec-embedding`).

Zero holes remain in the item; zero holes added; zero lemmas split off.
The proof uses the already stated lemmas `AlgebraicGeometry.qcqs_relative_affinization_map`
(node `lem-trf-qcqs-relative-affinization-map`) and
`AlgebraicGeometry.isOpenImmersion_and_quasiCompact_of_canonical_affine_charts`
(node `lem-trf-canonical-affine-charts-qc-open-immersion`), whose existing proofs contain
`sorry`. They remain needed as the stage-3 plan specifies; this delivery does not claim
that the item has no transitive sorry dependencies.

## No longer needed

Removed redundant direct private imports:

- `Mathlib.AlgebraicGeometry.QuasiAffine`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`
- `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Gluing`
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
- `WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`
- `WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps`

The relevant APIs are available through the statement imports and the two declared
proof dependencies. No DAG dependency or module is withdrawn or claimed globally
pruned: the canonical relative-affinization and chart criteria encapsulate the original
local-map/gluing argument, so those lower dependencies remain needed there.
All current item proof dependencies are retained, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The existing declaration docstring describes the
expanded six-step argument, while the current DAG packages it into four steps using
the two existing statement modules. The proof follows that current DAG without
changing any statement. The `Opens.toSpecΓ` versus `Scheme.toSpecΓ` distinction requires
the explicit canonical `topIso` transport above.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
