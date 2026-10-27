## What changed

The main theorem `AlgebraicGeometry.Scheme.RationalStratumPullback.rational_stratum_pullback_models`
now explicitly assembles its normalized Stratum and all Chart records. Its statement
is unchanged. The proof uses the supplied Along comparison and completion-normalized
counits; it does not replace the chosen realization or completed pullback.

The proof obtains the two ambient compositors, proves the immersion single comparison
is invertible, and constructs Stratum. It composes Stratum.comparison with the derived
to ordinary single comparison on the finite locally free restriction. This identifies
the actual pulled-back realized K with an ordinary module in degree zero; the standard
derived t-structure transfers both bounds. On each arbitrary chart it assembles both
compositions and a FreeModel with the explicit balanced forward and inverse formulas.
The finite-free property is proved using the original free sheaf's generating sections.

All sixteen existing data declarations were relocated verbatim to
`Sheaf.Paper.RationalStratumPullbackData`, publicly reexported by the original module.
This permits four separate supporting theorem modules without an import cycle. The
old names, signatures, definition bodies, visibility and public prerequisites remain
available. No source-library module was changed. The complete relocation and consumer
inventory are in `coord/changes/U1-rational-stratum-pullback-data.md`.

## Proved and sorry left

Original holes closed by a complete assembly proof:

- `AlgebraicGeometry.Scheme.RationalStratumPullback.rational_stratum_pullback_models`
  (`lem-per-rational-stratum-pullback-models`).

Four strictly smaller holes are split off, each the complete proof of one public
theorem in its own module, with a source, proof in words and DAG node:

- `AlgebraicGeometry.Scheme.RationalStratumPullback.rational_ambient_pull_models`
  (`lem-per-rational-ambient-pull-models`): a universal normalized counit for one
  arbitrary ambient morphism, without any stratum, chart or degree bound.
- `AlgebraicGeometry.Scheme.RationalStratumPullback.rational_ambient_pull_composition`
  (`lem-per-rational-ambient-pull-composition`): composition of supplied normalized
  pullbacks, without the realization object, local freeness or degree bounds.
- `AlgebraicGeometry.Scheme.RationalStratumPullback.rational_pull_single_computation`
  (`lem-per-rational-pull-single-computation`): computation on a single sheaf when
  its coefficient map is invertible or the sheaf is finite locally free; no chart
  or stratum comparison is asserted.
- `AlgebraicGeometry.Scheme.RationalStratumPullback.rational_balanced_free_pullback`
  (`lem-per-rational-balanced-free-pullback`): an ordinary finite-free isomorphism
  and its balanced section equations; no derived assertion or counit computation.

This is a decomposition: one original hole closed, four holes added, net three more
holes in the changed files. It is not a net proof of the target closure. There are
zero holes in definitions and zero holes left in the main module. No axiom, unsafe
code, external implementation or arbitrary witness-based definition is introduced.

Validation: the final server `lcompile.py --all` run compiled all six modules
successfully, including the complete main assembly and its finite-free helper.
All sixteen relocated declarations and the main theorem signature were checked
byte for byte against the shared source. Import-direction checks passed.

## No longer needed

The proof avoids a second chartwise cohomology-vanishing descent: the locally free
single computation already supplies the global degree-zero isomorphism. Its proof
still uses local trivializations and sheaf separatedness, documented in that new node.
No blueprint unit statement or unit proof step is bypassed.

Removed original private imports from the data module / main theorem:

- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` (used only by the new
  ambient composition obligation).
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent` (used only by the new
  ambient counit obligation).
- `Sheaf.CategoryTheory.RingedSiteModules` (no direct use).
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` (already available through
  the preserved public prerequisites).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` (already available
  through the preserved public prerequisites).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and
  `Mathlib.AlgebraicGeometry.OpenImmersion` (the existing immersion API supplies the
  coefficient-isomorphism theorem; no factorization is needed in this assembly).
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale` and
  `Mathlib.AlgebraicGeometry.Sites.Fpqc` (base-changed chart objects are constructed by
  the existing ProEt base-change functor; no covering descent is redone here).

Original direct proof dependencies moved below new obligations:
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-weil-pbc-ringed-topoi-derived-pullback`,
`lem-per-continuous-coefficient-slice-normalization`,
`def-pc-flat-sheaf-modules`, `def-pc-kflat-complex`,
`def-pur-sheaf-tensor-product`. They remain needed by the respective new nodes.

Original direct proof edges no longer used:
`def-weil-closed-immersion`, `def-weil-open-immersion`,
`lem-weil-pbc-weakly-etale-composition-base-change`,
`lem-galois-fpqc-covering-base-change`, `def-weil-pbc-proetale-site`,
`def-weil-sheaf-of-modules-category` and
`lem-per-continuous-rational-derived-realization` as an existence theorem. The given
Along carries the realization comparison; the existing continuous rational data and
site/module definitions remain statement prerequisites, not new proof obligations.
The four old top-level tool-use approvals are removed from the item because they are
not its direct proof edges; no new top-level approvals are added.

The supporting theorem modules import only the public data their statements need.
Their proof plans cite the generic source theorems in the DAG, without unnecessarily
importing those unfinished proofs into their Lean import closure.

No existing Lean module is withdrawn. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The main conclusion needs universal and unit-normalized ambient comparison records,
not merely unspecified isomorphisms. The generic stated derived-pullback theorem does
not directly provide them for the exact `ContinuousRational.modulePull` presentation:
identity scalar factors and cochain counits must be transported. Likewise composition
interfaces restricted to noetherian bases or invertible coefficient maps do not cover
the arbitrary chart morphisms used here. The new obligations isolate precisely these
transport steps instead of assuming any chart realization equivalence or flatness of
the structural coefficient map.

The original proof's separate descent of the final cohomological bounds can be folded
into the finite locally free single computation. This shortens the assembly while
preserving the local-free/K-flat argument and the canonical stratum/chart maps.

## New nodes

`def-per-rational-stratum-pullback-data` owns the sixteen existing relocated data
declarations. It introduces no alternative definition and has no proof obligation.

`lem-per-rational-ambient-pull-models` isolates the normalized ambient counit and its
K-flat computation, following Stacks 06YY and the identity-scalar normalization API.

`lem-per-rational-ambient-pull-composition` isolates the two successive tensor factors,
actual unit formula, termwise comparison and universal derived descent of Stacks 0D6D.

`lem-per-rational-pull-single-computation` isolates exact coefficient restriction and
finite locally free K-flat single computation. Its local argument includes rank zero
and the empty covering.

`lem-per-rational-balanced-free-pullback` isolates only the ordinary finite-free tensor
calculation, with both section formulas and no derived computation clause.

The ownership change record is `coord/changes/U1-rational-stratum-pullback-data.md`.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
