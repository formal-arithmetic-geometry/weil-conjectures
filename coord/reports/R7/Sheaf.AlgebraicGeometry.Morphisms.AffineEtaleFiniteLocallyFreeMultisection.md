## What changed

Proved `AlgebraicGeometry.exists_affine_etale_finiteLocallyFree_multisection` in
`Sheaf.AlgebraicGeometry.Morphisms.AffineEtaleFiniteLocallyFreeMultisection`, preserving its
signature, public imports and existing docstrings. Three proved private helpers identify the
intrinsic fibre Cohen–Macaulay locus, select a closed Cohen–Macaulay fibre point, and construct
the canonical fibre comparison with both projection equations.

The proof follows Stacks 055W: apply the existing closed-point slice, apply the existing
02LK elementary étale finite-piece theorem, refine by an affine-cover member, apply the
existing persistence theorem, and combine finite + flat + locally finitely presented.
Mathlib's cartesian residue-field fibre square supplies the final geometric-property checks.
The node's six proof steps, proof dependencies and proof origin now record this Lean argument.
No existing shared module or public interface is changed.

Validation: `lcompile.py` compiled the delivered module without errors or warnings in 5.1 s,
well within the 60 s per-file limit.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_affine_etale_finiteLocallyFree_multisection`
(node `lem-trf-affine-etale-finite-free-multisection`).

Added 0 holes, split off 0 statements, and left 0 textual `sorry`s in the delivery.
The proof uses the existing stated theorems
`flat_lfp_cm_locus_fibre_dense` and
`AlgebraicGeometry.exists_flat_locallyQuasiFinite_slice_of_closed_fibre_depth_eq_ringKrullDim`;
their pre-existing proofs remain work for their own items. This is a proof from the declared
DAG inputs, not a claim that the entire transitive import closure is now sorry-free.

## No longer needed

Removed private imports:

- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: Mathlib's cartesian fibre square
  directly gives the required canonical comparison, including both projection equations.
- `WeilConjectures.AlgebraicGeometry.RestrictedFibreLocallyNoetherian`: use the Mathlib
  locally-finite-type-over-a-field and Noetherian stalk instances directly.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: already available through the retained
  statement imports; no separate proof import is needed.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: its needed API is already available through
  retained imports.
- `Mathlib.RingTheory.Localization.Submodule`: no explicit localization argument is needed.

Removed direct proof dependencies:

- `lem-sbc-restricted-fibre-locally-noetherian` (also removed its obsolete top-level
  `tool_uses` entry): the generic Mathlib instance suffices without a restriction to the
  whole base open.
- `lem-weil-pbc-affine-open-stalk-localization` and
  `lem-weil-pbc-localization-noetherian`: Noetherian fibre stalks follow directly from the
  Mathlib scheme API recorded in `pqf-def-locnoeth`.
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`: the existing implication from local
  finite presentation to local finite type supplies the hypothesis of 02LK directly.

These are dependencies this proof does not need separately; no source-library declaration
is removed, and no assertion is made that these modules are globally unreachable.
The unit route and all six geometric steps are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The DAG expanded several facts already provided by Mathlib
into explicit affine-chart arguments; the Lean proof uses that API directly. The original
single `sorry` concealed substantial but elementary glue: transporting the fibre point,
selecting a closed point in the open locus, refining the finite piece affinely, and checking
the canonical fibre projections. All this glue is now proved.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
