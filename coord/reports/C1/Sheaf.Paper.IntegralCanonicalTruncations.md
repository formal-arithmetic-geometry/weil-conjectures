## What changed

Restored the assigned quarantined module `Sheaf.Paper.IntegralCanonicalTruncations`
from `quarantine/Sheaf/Paper/IntegralCanonicalTruncations.lean`, preserving all twelve
existing declarations and their signatures. No source-library file, public definition,
or target statement changes.

Proved `pbc_flat_cohomology_torCompatible` using the generic single-complex flatness
criterion, scalar extension of flat sheaves, and tensor cohomological bounds.
Two truncation triangles isolate each cohomology single; its scalar extension is
again a flat single. The sufficient condition works for any adic datum and unbounded
ambient complex; no DVR, completeness, boundedness, or constructibility assumption
has been added.

Reduced the converse flatness criterion to the independent lifted-coefficient DVR
normal-form result. Reused the already proved private descent, equational-criterion,
and nilpotent-cokernel helpers through `import all Sheaf.Paper.AdicTorFlatCriterion`.
Only those helpers are used: the unlifted Padic flatness theorem does not have the
coefficient presentation required here.

Proved the main theorem from flatness and actual-completed-coefficient canonical-tower
reconstruction. The Lean proof constructs normalized finite and restricted-ambient
truncation comparisons by uniqueness of distinguished truncation triangles. It proves
naturality of the quotient transition from the scalar adjunction, proves coherence of
both comparisons by the truncation adjunctions, and transports the complete truncations'
Roos triangles along the products of these coherent isomorphisms. The equations with
the actual truncation counit and unit are retained, including quotient index zero.
There is no arbitrary choice of a derived-limit object.

All additional imports are private proof imports. All three sandbox modules compile
in import order through `lcompile.py --all`, without warnings (the item takes about
15 seconds). No public signature or definition repair is included. The conservative interface
checker requires a change record for the added file-local instance-priority
commands; this is `coord/changes/integral-canonical-truncations-local-instances.md`.
The attributes are local and export no changed registry to consumers.

## Proved and sorry left

Original holes closed, all in node `thm-weil-pbc-integral-truncations`:

- `AlgebraicGeometry.Scheme.pbc_flat_cohomology_torCompatible`: complete proof from
  existing declarations; no new hole is used for this sufficient condition.
- `AlgebraicGeometry.Scheme.pbc_torCompatible_iff_flat_cohomology`: complete combining
  proof, decomposed through the independent local torsion normal form below.
- `AlgebraicGeometry.Scheme.pbc_integral_truncations`: complete combining proof,
  decomposed through actual coefficient reconstruction below, and the preceding
  flatness criterion.

The item itself has zero remaining `sorry` bodies. Two named holes are added:

- `AlgebraicGeometry.Scheme.pbc_integral_cohomology_torsion_normal_form`, in
  `Sheaf.Paper.IntegralCohomologyTorsionNormalForm`, node
  `lem-weil-pbc-integral-cohomology-torsion-normal-form`.
- `AlgebraicGeometry.Scheme.pbc_actual_completed_reduction_reconstruction`, in
  `Sheaf.Paper.ActualCompletedReductionReconstruction`, node
  `lem-weil-pbc-actual-completed-reduction-reconstruction`.

Thus this is one proof and two decompositions: three original holes closed and two
source lemmas added, for a local net reduction of one hole, before the project's
import-closure ledger calculation. Neither new statement assumes the Tor hypothesis
or has the original truncation theorem's conclusion. The normal form is a local
free/torsion decomposition for arbitrary integral objects with a Tor-obstruction
projection, without assuming flatness. Reconstruction applies to every intrinsically
complete object, without constructibility, flatness, or any truncation. Both have
source references and complete proofs in words in their docstrings and nodes.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.AdicTorFlatCohomology`
- `Sheaf.Paper.BoundedConstructibleTower`
- `Sheaf.Paper.CompletedRlimFunctor`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteReductionReconstructionCompleted`
- `Sheaf.Paper.IntegralUniformCoefficient`
- `Sheaf.Paper.KoszulReconstruction`
- `Sheaf.Paper.LevelwiseAdicTruncations`
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`

The old levelwise-truncation construction, homotopy-colimit construction, special
finite-reduction reconstruction, and total inverse-limit functor are not steps of
the new main proof. Its direct dependencies are ambient truncation closure, generic
tensor bounds, normalized scalar adjunctions, and canonical-tower reconstruction.
The old direct `AdicTorFlatCohomology` import is replaced by the smaller criterion
module solely for its proved private descent helpers; the all-cutoff unlifted
flatness equivalence and supplied-model flatness equivalence are not invoked.
The underlying coefficient datum and bounded-complete definitions remain required
through the public interface; removing their redundant direct imports does not
withdraw their nodes. No Lean module or existing declaration is deleted, and no
claim of global unreachability is made.

Removed obsolete direct proof dependencies and tool approvals for
`prop-weil-pbc-rlim-functoriality`, `prop-weil-pbc-koszul-reconstruction`,
`lem-weil-pbc-standard-quotients-perfect`, `lem-weil-tower-category-levelwise-abelian`,
`lem-weil-pbc-finite-reduction-reconstruction`, `lem-pur-derived-change-of-rings`,
`lem-weil-heart-short-exact-triangles`, `def-kun-truncations`, and
`lem-weil-derived-scalar-extension-restriction-adjunction` from the parent node.
The new reconstruction node still uses generic scalar extension and the completed
Koszul Roos theorem, with those dependencies recorded there. The generic datum's
own dependencies, and any other consumers of these nodes, remain intact.
`prop-weil-pbc-levelwise-truncations` and
`lem-weil-pbc-adic-tor-flat-cohomology` are also no longer direct proof dependencies
of the parent. The former's module remains available transitively for its shift
API and the criterion's types; its holed construction theorem is not applied.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined, not withdrawn. Its archived source and twelve-declaration
Lean attachment have been preserved; no `deleted.txt` entry is made.

The available `pbc_adic_tor_flat_cohomology` and its normal-form input use
`E : Type (u + 1)` and the unlifted `pbcPadicCoefficientDatum`. The assigned theorem
uses `E : Type u` and `pbcIntegralDatum`, whose valuation ring is lifted. These
are not definitionally the same coefficient category. Applying the unlifted theorem
would require transporting the entire completion, quotient, and constructibility
interfaces. The new normal-form statement instead matches the existing integral
stratified-perfect characterization directly and keeps all original hypotheses.

Likewise the existing completed Koszul Roos theorem is stated on the constant
completed-ring model tower. The assigned diagram uses the actual completed ring
and the adjunct-normalized quotient transitions. The new reconstruction lemma
isolates that coefficient-presentation transport; it does not silently treat the
two sequences as definitionally equal.

The generic tensor bounds give a shorter route to normalized comparisons than
constructing separate strict truncated towers and then recognizing their limits.
The unit record `sk-rem-rest` has no realized statement or proof steps, so no
protected unit route is bypassed. The current blueprint's canonical truncations,
reductions, cohomology, and canonical triangle all remain represented.

## New nodes

`lem-weil-pbc-integral-cohomology-torsion-normal-form` records the local DVR
normal form and consecutive-quotient torsion obstruction in exactly the lifted
integral coefficient presentation. Its source is the DVR elementary-divisor and
periodic-resolution part of the flatness criterion, as already separated in the
unlifted normal-form node. It assumes no Tor vanishing. Zero complexes and empty
charts are covered by a zero torsion summand and the map to zero; outside the
cohomological range the same choice applies.

`lem-weil-pbc-actual-completed-reduction-reconstruction` records the canonical-tower
consequence of the blueprint's Koszul reconstruction in the actual coefficient
presentation. Its proof plan transports the completed Koszul Roos triangle through
exact coefficient equivalences and normalized level comparisons. It includes the
zero ideal (constant tower), the unit ideal (complete object zero), the empty
scheme, and unbounded complexes. The only change record is
`coord/changes/integral-canonical-truncations-local-instances.md`, documenting the
file-local elaboration priorities flagged by the conservative interface checker.
No existing statement or definition is changed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
