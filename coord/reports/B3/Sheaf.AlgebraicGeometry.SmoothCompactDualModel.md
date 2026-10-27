## What changed

Proved `AlgebraicGeometry.Etale.exists_smooth_compact_dual_model` from two proper
intermediate statements. The public theorem has its original signature. Construct
`N = RHom(L[0], omega_f)` and `C = Rf_! N` explicitly. Smooth charts prove that the
dualizing complex is invertible and bounded constructible of finite Tor amplitude;
compact-support finiteness proves bounded constructibility of C. Internal adjunction
and compact exchange construct the open and test isomorphisms. A proved generic
naturality calculation transports compact-adjunction exchange to the record's
canonical ordinary exchange equation.

The new module `SmoothLisseRelativeDual` is proved without holes. It uses finite-lisse
flatness, the explicit sheaf dual, the degree-zero dualizable complex, the coefficient
dual/tensor isomorphism, finite-Tor tensor stability, and canonical relative biduality.
The relative dual and bidual map are explicit constructions with an equality API.

The record uses definitionally equal generic abbreviations for derived inverse image
and the degree-zero complex. `FiniteLisseFieldDual` infers the definitionally equal
result type of its unchanged comparison construction. Both changes avoid costly
concrete instance comparisons. The original consumer `SmoothGenericDirectImage`
is included unchanged for verification. The change record is
`coord/changes/B3-smooth-compact-dual-local-elaboration.md`.

The resumed packet initially failed the import-cycle check. The higher
`CohomologicalSmoothness` module now reaches this item through smooth base change,
projective-line trace, affine-line Kunneth, stability, and Deligne finiteness. Replaced
that import with the existing lower chart reduction and a strictly smaller finite-field
affine-line exchange statement. Chartwise invertibility is proved directly from the
shifted rank-one description. No adopted source-library file changes.

Validation: the final six-module packet compiles without errors or warnings through
`lcompile.py --all`, including the unchanged consumer. The main module took 60.5 s in
that batch; its separate profiled compile took 51.4 s. Profiling options were removed.

## Proved and sorry left

Original holes: 1. Closed:
`AlgebraicGeometry.Etale.exists_smooth_compact_dual_model`
(node `lem-asd-smooth-compact-dual-model`).

Also proved the new theorem `AlgebraicGeometry.Etale.finiteLisseRelativeDual`
(node `lem-asd-finite-lisse-relative-dual`), without any added hole.
The existing `FiniteLisseFieldDual` repair has zero original and zero remaining holes.

Added holes, each the whole proof of a public theorem in its own module:

- `AlgebraicGeometry.Etale.compactInternalAdjunctionExchange`
  (node `lem-asd-compact-internal-exchange`): the canonical mate compatibility for
  arbitrary complexes; no smoothness or coefficient-dual finiteness is asserted.
- `AlgebraicGeometry.Etale.compactModelAffineLineExchange`
  (node `lem-asd-compact-model-affine-line-exchange`): only affine-line projections
  over affine bases, with finite field coefficients. The existing source chart
  reduction handles all other smooth morphisms in the model's proof.

The item has zero holes; the packet has two. This is a decomposition of the original
hole, not a complete proof independent of new holes. All complex and isomorphism data
are explicit. Inverting an explicit map uses only its invertibility; there is no choice
of an arbitrary compact model from an unproved existence statement.

## No longer needed

The global dualizing complex avoids the planned clopen decomposition by relative
dimension and recombination of compact images. Smooth charts and a finite subcover
suffice to obtain common bounds.

This proof does not import `Sheaf.SmoothPurity.InternalAdjunctionEvaluation`,
`Sheaf.AlgebraicGeometry.CompactProjectionExchange`,
`Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange`,
`Sheaf.AlgebraicGeometry.SmoothTensorDuality`, or
`Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`. Existing source theorems supply
compact-image finiteness, smooth duality, and tensor-Hom adjunction. The compact mate
identity uses the coefficient-last projection convention. The main module omits the
unused `LowerShriekProjectionExchange` proof import; that theorem is an ingredient of
the separate compatibility obligation. The new compact-adjunction module imports
`UpperShriekCanonicalMaps` instead of the unnecessary higher `SmoothDuality` module.

Removed `CohomologicalSmoothness` from the retained packet to break the cycle. Its
shifted rank-one invertibility argument is proved locally; its full smooth-exchange
import is replaced by the lower etale/affine-line chart reduction. The higher source
smooth base-change theorem remains in the library with its existing proof.

The item no longer lists these original proof dependencies:
`lem-fin-compact-bounded-and-base-change`,
`sbc-lem-smooth-relative-dimension-locally-constant`,
`lemma-weil-pbc-geometric-stalk-conservative`,
`lem-asd-internal-adjunction-evaluation`, `thm-cbc-finite-torsion`,
`lem-weil-pbc-adjunction-of-natural-bijection`, `def-weil-pbc-derived-categories`,
`def-pur-derived-internal-hom`, `prop-asd-smooth-base-change`,
`lem-pod-separated-finite-type-base-change`,
`lemma-nagata-compactification-base-change`, and
`lem-asd-compact-projection-exchange`. Compact-exchange and compactification base change
are supplied directly by source APIs; the new compatibility node records its actual
projection-exchange ingredient. The finite-coefficient `prop-asd-internal-adjunction` is retained; the much broader
`lem-sf-tensor-hom` is not used. Likewise, the oriented geometric
`thm-sf-dual-perfect` and the pro-etale coefficient-specific `lem-sf-tensor-ctf` are
replaced by records of the actual proved categorical and ordinary-etale source inputs.
Statement dependencies are unchanged. No whole module
is withdrawn; declarations used elsewhere remain available.

## Where the brief, the DAG or earlier work was wrong

The original finite clopen decomposition and coefficient-first evaluation expansion
were unnecessary. The retained attempt had not accounted for the current smooth
base-change import cycle and still left relative finite-lisse duality unproved.
The lower chart theorem permits an acyclic reduction to the affine-line case. That
case is strictly smaller than constructing a compact dual, its finiteness, all open
and test isomorphisms, and their compatibility.

Preflight also detected DAG cycles through the broader `lem-sf-tensor-hom` and
`thm-sf-dual-perfect` nodes. Those nodes assert more than the source APIs used here,
and their planned proofs return through smooth generic direct image. The packet now
uses finite-coefficient internal adjunction and records the already-proved abstract
relative-bidual and ordinary-etale finite-ring tensor lemmas separately. There is no
cycle in the resulting dependency closure. Search records now include LeanSearch,
Loogle/LeanFinder and Mathlib grep; the unsupported `sorry_free` source-record field
and redundant existing-source `file` field were removed. No Lean proof changed in
this metadata repair.

The public comparison and record field aliases are definitionally equal to their
original constructions. No target statement or mathematical hypothesis changes.

## New nodes

`lem-asd-finite-lisse-relative-dual`: proved finite-lisse relative-dual finiteness,
dualizability and canonical biduality, in `SmoothLisseRelativeDual`.

`lem-asd-compact-internal-exchange`: the remaining Cartesian compact-adjunction mate
identity in `CompactInternalAdjunctionExchange`.

`lem-asd-compact-model-affine-line-exchange`: the remaining affine-line model case of
canonical exceptional exchange, in `CompactModelAffineLineExchange`. Its source is the
current blueprint's projective-line/affine-line argument. The existing complete source
implementation cannot be imported here because it reaches the parent item.

`lem-asd-finite-coefficient-compact-image`: records the existing proved source theorem
`boundedConstructible_rightDerivedLowerShriek_and_isIso` at generic finite
coefficients. It adds neither a Lean declaration nor a hole.

`lem-asd-source-invertible-relative-bidual`: records the already-proved categorical
`isDualizable_ihom_obj` and `isIso_toIhomIhom_of_isDualizable`, with no geometric
orientation or four-coefficient hypotheses. It adds no Lean file or hole.

`lem-asd-source-finite-etale-tensor-ctf`: records the already-proved generic finite-ring
ordinary-etale `constructibleFiniteTor_tensor`. It adds no Lean file or hole.

All remaining holes have complete natural-language proofs and source references in
their docstrings and nodes. The unit route is retained. Change record:
`coord/changes/B3-smooth-compact-dual-local-elaboration.md`.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
