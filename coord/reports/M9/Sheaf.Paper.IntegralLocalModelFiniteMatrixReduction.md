## What changed

Replaced `integral_local_model_finite_matrix_reduction`'s single sorry by a complete
assembly proof. It proves finite ramified ell-power residues by cofinality and a
surjective factor of a finite uniformizer quotient; constructs an injective scalar
matrix by a PID basis of the kernel of a finite presentation; proves finite and
finitely presented reduced kernels and cokernels; and proves global vanishing by
sheaf separatedness on exactly the original covering sieves. The local finite-type
conclusions retain those same sieves. No statement or hypothesis changes.

Moved the existing coefficient, functor and simultaneous-model definitions verbatim
into `Sheaf.Paper.IntegralMatrixModelData`, publicly reexported from the item. This
avoids import cycles for the two new independent proof obligations. Every moved
normalized signature and body was compared with the source. Change record:
`coord/changes/integral-matrix-model-data.md`. There are no downstream Lean importers
to adapt; the two unfinished DAG parents still use this item.

## Proved and sorry left

Closed the body of
`AlgebraicGeometry.ProEtale.IntegralMatrix.integral_local_model_finite_matrix_reduction`
(node `lem-sp-integral-local-model-finite-matrix-reduction`): 1 original hole removed.
Added exactly two public theorem holes, each its whole proof:

- `AlgebraicGeometry.ProEtale.IntegralMatrix.local_resolution`, node
  `lem-sp-integral-matrix-local-resolution`, supplies the completed exact sequence and
  normalized comparisons for a given scalar resolution. It has no finite-residue,
  cohomology, global vanishing, or cover conclusion.
- `AlgebraicGeometry.ProEtale.IntegralMatrix.matrix_cohomology`, node
  `lem-sp-integral-matrix-cohomology`, computes homology of any given derived object
  already identified on one slice with a constant matrix cone. It requires no
  scalar resolution, local-model hypothesis, cover, finiteness, or quotient squares.

This is a decomposition, not a complete proof: 1 upper hole closed, 2 strictly
smaller holes added, net -1 textual hole. Zero holes remain in the item or data
module; every private helper is proved. No data is chosen from either new theorem
in a definition. The original normalized universal-pair choices remain unchanged.

## No longer needed

No mathematical dependency is withdrawn: the two smaller lemmas retain the
substantive derived/flatness dependencies of the original plan. No module or node
is deleted. The following old private imports are removed from the item's data
prefix because none of its definitions needs them; their proof content is retained
in the new obligation nodes where needed:

- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`
- `Sheaf.Algebra.Homology.FiniteFreeResolutionTensor`
- `Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr` (available through coefficient imports)
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.CategoryTheory.FiniteTypeConstantExact`
- `Mathlib.LinearAlgebra.FreeModule.PID` (proof import retained in the main theorem module)
- `Mathlib.LinearAlgebra.Dimension.Free`
- `Mathlib.RingTheory.PrincipalIdealDomain`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`

The direct locally-constant predicate API is unnecessary for the theorem's explicit
covering-sieve conclusion. The explicit finite-generators-and-relations construction
is replaced by Mathlib finite-ring Noetherianity and finitePresentation_of_finite.
The parent's top-level tool approvals for K-flat resolution, derived coefficient
adjunction, localized tensor restriction, finite-free tensor resolution, exact K-flat
restriction, completion flatness and exact constant realization are removed there;
these tools remain dependencies of the new local-resolution or homology statements.
The DVR approval is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Some named plan APIs are not direct small-site
specializations: completed_constant_sheaf_reduction uses the scheme's larger site,
and strictPerfectConstantSheaf_exact is a different constant realization interface.
The new obligation docstrings spell out the required concrete comparisons rather
than treating the interface transport as definitional equality. The original
plan's scalar and descent portions are implemented directly from Mathlib and the
sheaf axiom. Edge cases checked: zero ranks, zero scalar module, noninjective
reduced matrix (torsion is retained), empty covering sieves and ramified ell.

## New nodes

`def-sp-integral-matrix-model-data`: relocation of the existing concrete definitions,
without modifying data or public names. It adds no proof hole.

`lem-sp-integral-matrix-local-resolution`: original steps 1--4 after supplying the
scalar exact sequence, independent of the residue finiteness and cohomology claims.

`lem-sp-integral-matrix-cohomology`: original step 6 and the exact-restriction part
of step 8 for an arbitrary derived matrix comparison on one slice.

All nodes retain the original chapter and unit. The unit has no proof steps, so
its route is unchanged. Source and complete proofs in words are in each new theorem
docstring and node. Change record: `coord/changes/integral-matrix-model-data.md`.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
