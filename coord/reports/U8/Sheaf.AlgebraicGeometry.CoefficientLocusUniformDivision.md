## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.HilbertCoefficient.coefficient_locus_uniform_division` by a complete
Lean reduction. It chooses the existing essential-prefix stabilization bounds, proves
nonvanishing of the finite test product and membership of its principal open, proves the
matrix-entry alternatives, derives exact orders from a lower bound and a nonzero vertex
coefficient, and combines restricted and full division over both residue and extension fields.
The existing theorem signature is unchanged, including all geometric hypotheses.

Extracted the eight existing concrete definitions/instance verbatim into
`Sheaf.AlgebraicGeometry.CoefficientDivisionData`, publicly reexported by the item, to allow
acyclic imports of the proof lemmas. See change record
`coord/changes/coefficient-division-data-extraction.md`.

Proved the new theorem `coefficient_order_locus_bound` directly: extend a centered ring map
to the affine stalk, construct the ideals of series of order at least p, and map maximal-ideal
powers into those ideals. This needs only affineness and the constant-coefficient identity;
no Taylor uniqueness, smoothness, etaleness, or differential comparison is required.
Private proved helpers handle W-zero coefficients, restricted coefficients, matrix entries,
finite-test membership, the principal-open equivalence, and preservation of order by an
injective field map.

Remote compilation checked all six modules. The clean final compile and delivery preflight
are the validation of the submitted versions. No other existing Lean module is changed;
there are zero current direct Lean importers of the item. Both DAG parents remain attached.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.HilbertCoefficient.coefficient_locus_uniform_division`
(node `lem-trf-coefficient-locus-uniform-division`). This is a decomposition, not a complete
sorry-free proof: three strictly smaller algebraic statements are added with holes.

New theorem proved without `sorry`:
`AlgebraicGeometry.HilbertCoefficient.coefficient_order_locus_bound`
(node `lem-trf-coefficient-order-locus-bound`). The seven private helpers in the item
are also proved without holes.

Every remaining hole in the delivery (three added, none in the item or the data module):

- `AlgebraicGeometry.HilbertCoefficient.coefficient_first_exponent_determinants`
  (`lem-trf-coefficient-first-exponent-determinants`): triangularity and the
  first-dividing-vertex reindexing for restricted matrices in arbitrary degrees.
- `AlgebraicGeometry.HilbertCoefficient.coefficient_restricted_finite_tests`
  (`lem-trf-coefficient-restricted-finite-tests`): the square-matrix criterion,
  supplied finite-test equivalence, late-prefix transport, and scalar extension.
- `AlgebraicGeometry.HilbertCoefficient.coefficient_restricted_to_full`
  (`lem-trf-coefficient-restricted-to-full`): enumerate the finite subtype indices
  and variable complement and apply the existing extra-variables comparison.

Each has its own module, source, full natural-language proof and DAG node. The original
module has 0 of its original 1 holes remaining; 3 lower holes were added. The theorem
`exists_finiteDivisionTest` used by the proof remains an existing dependency with its
pre-existing hole, not a hole added by this packet. The net new-hole count of this
reduction is +2 before considering the removal of now-unused proof dependencies.

## No longer needed

Removed the item's proof import of
`Sheaf.AlgebraicGeometry.DiagonalTaylorFaithfulFlatness` and its dependency edge
`lem-trf-diagonal-taylor-faithful-flatness`. The lower order estimate is proved using
localization and a centered ring map; faithful flatness and a canonical Taylor map
are unnecessary for this theorem.

Removed the planned dependency `lem-trf-etale-coordinate-derivations-jacobian`
(module `Sheaf.AlgebraicGeometry.EtaleCoordinateDerivations`). Every restricted
matrix entry uses an order-zero Taylor coefficient, so no differentiation or factorial
comparison is needed. The corresponding geometric hypotheses remain in the unchanged
public statement and are retained without use by the argument.

Removed the unused public import `Mathlib.LinearAlgebra.Determinant`. Matrix determinants
needed by statements are already available from RegularHilbertCoefficientDatum.
Moved the supported-division and regular-datum public imports into the data module;
FiniteType and Trunc remain public imports of the item. This preserves their reexports.

The original direct proof import of
`Sheaf.RingTheory.HomogeneousDivisionExtraVariables` is replaced by the new comparison
module: the existing node `lem-trf-homogeneous-division-extra-variables` remains a declared
proof dependency of that subargument and is not pruned. The determinant invertibility
node `lem-weil-endomorphism-invertible-iff-det-nonzero` remains a dependency of the finite-test
subargument. `lem-trf-initial-diagram-stabilization` remains used directly.
No existing module is withdrawn, and no unit-level route changes.

## Where the brief, the DAG or earlier work was wrong

The original plan's first step proves a derivative/factorial comparison that the actual
statement does not need: the finite restricted forms use only W-zero coefficients.
The geometric Taylor-order lower estimate likewise follows for every centered global
ring map on an affine scheme. The proof therefore prunes the two stronger Taylor-calculus
nodes without changing any conclusion or hypothesis of the item.

The available stabilization and extra-variables statements do not directly supply the
chosen square-matrix indexing, the dependent prefix subtype transports, or the finite
essential/complement variable enumerations required by this module. The three new
algebraic statements isolate these gaps; they are not copies of the upper theorem.

Read BM 1997 online, Lemma 7.7 pp.263--264, Theorem 8.1 pp.273--275, Lemma 9.12 p.281,
and completion of Theorem 9.6 p.282, alongside the inherited ILO route reference and
latest blueprint ancestor. Searches included the whole imported blueprint and existing
DAG modules as well as logged LeanSearch, LeanFinder, Loogle and Mathlib grep queries.
No exact reusable statement for the three transports/matrix constructions was found.

Checked the mathematical edge cases in each statement: empty vertices, empty essential
variables, zero-degree vertices, empty positive-degree matrix indices, late prefixes,
zero series, and field embeddings into another universe. The lower bound is vacuous
in degree zero and allows infinite order. The finite-test scalar extension uses inverse
matrices, so it needs no universe-sized stabilization assumption over the extension.
The full-variable comparison uses only W-zero coefficients and no unasserted order bound.

## New nodes

`def-trf-coefficient-division-data` records the existing eight concrete definitions/instance
in their extracted module, with identical names, signatures and bodies. It introduces
no new mathematical notion or postponed data. The extraction is recorded at
`coord/changes/coefficient-division-data-extraction.md`.

`lem-trf-coefficient-first-exponent-determinants` isolates the all-degree triangular
matrix calculation at the center; it has no geometry, open set, bounds or uniform-order
conclusion.

`lem-trf-coefficient-restricted-finite-tests` isolates the finite-dimensional algebra
from the given finite-test predicates and nonzero bounded determinants, including
late-prefix identification and arbitrary coefficient extension.

`lem-trf-coefficient-order-locus-bound` is proved by affine stalk localization and
maximal-ideal powers. It provides only the lower bound, not order equality or division.

`lem-trf-coefficient-restricted-to-full` isolates the finite-variable and prefix
reindexing for the existing extra-variables theorem; its series are arbitrary except
for their supplied W-zero coefficients, and it has no open-locus assertion.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
