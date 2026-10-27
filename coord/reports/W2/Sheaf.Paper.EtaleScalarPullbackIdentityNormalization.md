## What changed

Proved `AlgebraicGeometry.Etale.etaleScalarPullbackIdentityNormalization` in
`Sheaf.Paper.EtaleScalarPullbackIdentityNormalization`, preserving its complete signature.
The geometric conjuncts are specializations of the already proved source-library
`leftDerivedUpperStarComp_id_right_hom_app`.

For the scalar conjunct, use `Sheaf.Paper.ScalarPullbackComposition` as a private proof
import. Transport the geometric unit equations along the canonical comparison with exact
derived inverse image. At two identity scheme maps, scalar composition and naturality
show that the transported scalar comparison satisfies the unit equation: cancel its
invertible component and the geometric compositor, then use faithfulness of a functor
isomorphic to the identity. Cancel the transport isomorphism to obtain the original
scalar equation. All three categorical helpers are private and completely proved.
No coefficient flatness, boundedness, or other hypothesis is added.

The assigned node's proof, proof dependencies and proof origin now describe this argument.
Removed obsolete top-level tool approvals; the new scalar-composition dependency is used
as a general coherence tool, with no change to the purity unit's statement or route.
Neither the Lean import graph nor the DAG has a path from scalar composition back to this
item. The change record is
`coord/changes/W2-etale-scalar-identity-import-pruning.md`.

Validation: `lcompile.py` accepted both the item and the unchanged sole direct importer,
`Sheaf.Paper.EtaleDirectImageScalarComposition`, with exit code zero and no Lean warnings.
The service reported totals of 54.2 s and 72.3 s respectively (including setup); both
passed its separate 60-second Lean-runtime acceptance check. The unchanged consumer
copy was removed from the sandbox after verification.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.etaleScalarPullbackIdentityNormalization`
(node `lem-pur-etale-scalar-pullback-identity-normalization`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No new statement with `sorry`, definition, instance, or axiom is added.

## No longer needed

Removed these seven direct imports, because neither the statement nor the new proof needs
their declarations:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact` (public).
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` (public).
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` (public).
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` (private).
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` (private).
- `Sheaf.Paper.ScalarPullbackRepresentativeData` (private).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` (private).

The following original direct proof dependencies are unnecessary in this module's proof:
`lem-pc-kflat-resolution`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`prop-weil-pbc-inverse-image-modules-exact`,
`def-pur-scalar-pullback-representative-data`, `def-pur-sheaf-tensor-product`,
`lem-sfb-ringed-derived-monoidal-comparisons`, and `lem-pur-derived-change-of-rings`.
The first, second, third and sixth obsolete top-level `tool_uses` entries were removed.
The statement dependencies are unchanged. Some of these results remain reachable through
other imports, including scalar composition; no global module withdrawal or claim that
they are unused everywhere is made.

## Where the brief, the DAG or earlier work was wrong

The original representative-level plan is mathematically valid but unnecessarily repeats
existing coherence. The geometric equations are already proved in the adopted source tree,
and the scalar equation follows from the already proved scalar-composition theorem.
The theorem's original docstring retains that valid alternative representative argument;
the actual shorter route is recorded in the node and this report.

At session start the item and several dependencies were in quarantine, with the listed
false-tail import-closure reason. The quarantine row and archive were inspected before
copying. The shared tree restored those files during this session; work then continued
from the restored current sources. No archive or Lean attachment is deleted, no empty
module is substituted, and no quarantined dependency is silently withdrawn.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
