## What changed

Proved the unchanged `IntegralQuotient.integral_quotient_direct_image_comparison`
from the recorded resolution, scalar normalization, scalar mate projection and
scalar mate transitivity declarations. The proof uses dualizability of the actual
bounded two-term resolution and the existing categorical dualizable projection
lemma in place of the general perfect projection theorem. The tower witnesses are
made global using uniqueness of successive normalized comparisons by the universal
property of the left derived functor.

Added `Sheaf.Paper.NormalizedScalarRestrictionPush`, identifying the composite
right-adjoint-uniqueness comparison with the canonical geometric mate. This is a
generic normalization identity, with no quotient, tensor formula or invertibility
assertion. Its proof reuses proved generic private mate calculations from the
integral-residue modules, without altering those modules. The main file also checks
the actual coefficient pullback using localization and the single-degree embeddings.
The final proof uses stricter transparency for type comparisons, avoiding expansion
of localization types. Generic private lemmas
keep exact-localization and tower calculations separate from quotient-ring
specialization, avoiding repeated expansion of the large normalization statements.
A private instance fixes the section-derived-category choice throughout the proof;
the public statement is elaborated with the original monoidal instances.

Repaired the returned duplicate-instance declarations by importing
`Sheaf.Paper.IntegralResiduePullFlatModelMateNormalized` with `import all` and
using its existing `cachedProofInstance1` through `cachedProofInstance5` and
`cachedProofInstance7` through `cachedProofInstance12` as local instances. Removed `proofTensorFour`, `proofTensorLeft`, `proofTensorRight`,
`proofLeftColimits` and `proofRightColimits` entirely. Also removed the redundant
`proofMonoidal`, `proofPreadditive`, `proofCoproducts`, `proofColimits`,
`proofFlatResolutions` and `proofExactColimits` caches, reusing the existing ones
to avoid repeated instance construction. These caches concern the
same internal module category (`Modules` unfolds to the existing `Mod` category),
so no new theorem or change to the existing theorem module is needed. The imported
caches are disabled while elaborating the public theorem statement, just as the
removed local caches were. The import is private to the proof.

The revised main module compiles through `lcompile.py` in 53.7 seconds; the
normalization module also compiled successfully. No proof hole was added by the
repair.

Updated the parent DAG proof and dependencies to the implemented argument.
The new identity was checked at identity morphisms, zero coefficient rings and empty
schemes; the counit characterization handles these cases without extra hypotheses.

## Proved and sorry left

Original item: one hole in
`AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_direct_image_comparison`.
Closed that hole. Added zero holes. No `sorry` remains in the delivery.

Also proved
`AlgebraicGeometry.ProEtale.QuotientChange.normalized_scalar_restriction_push`
(node `lem-sfb-normalized-scalar-restriction-push`).

Zero holes were split off. The existing imported theorems `integral_quotient_resolution_normalization`,
`internal_scalar_pullback_normalization`, `internal_scalar_mate_projection` and
`internal_scalar_mate_transitivity` remain dependencies, with their existing holes
unchanged. No axiom or holed definition was introduced.

## No longer needed

Removed all eleven redundant local cache declarations named above; the proof
now uses the existing caches directly, without restating or reproving them.

Removed the following direct proof imports from the assigned module:

- `Sheaf.Paper.PerfectProjectionFormula`: replaced by the categorical projection
  theorem for dualizable coefficients and dualizability of the two-term resolution.
- `Sheaf.Algebra.Homology.FlatScalarCyclicResolution`: its result is already packaged
  by the declared quotient-resolution normalization dependency.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison` and
  `Sheaf.Paper.SectionDerivedPushpullNormalization`: their transport work is already
  packaged by the scalar normalization and projection dependencies.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` and
  `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`: the proof takes place in the
  given internal derived monoidal categories and uses the actual internal maps.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`: use the declared
  scalar mate transitivity theorem and the uniqueness of its normalized witnesses.

Removed parent proof dependencies `lemma-weil-pbc-perfect-projection-formula` and
`def-weil-pbc-projection-formula-map`. Removed obsolete direct `tool_uses` entries
for those nodes and `lem-sfb-successive-derived-quotient-normalization`,
`lem-sfb-ringed-derived-monoidal-comparisons` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
These removals concern this proof; no upstream declaration or dependency still
needed by another proof is withdrawn. No Lean module is deleted.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified five private cache statements that duplicated
existing declarations. This repair reuses those declarations through `import all`.

The parent plan omitted the explicit bridge between `restrictPush.hom`, defined by
uniqueness of right adjoints for composite scalar/geometric adjunctions, and
`scalarRestrictionPush`, defined as the geometric mate of exact restriction/pullback.
These are different definitions, so applying the stated scalar projection theorem
alone does not prove the parent's exact equation. The new normalization lemma
supplies this bridge. The coefficient maps likewise require an exact-localization
calculation; their equality is proved explicitly. The section-module proof imports
introduce another pullback monoidal instance, so the private coefficient calculation
selects the canonical `CondensedRing.monoidal_upperStar` locally. No statement was changed.

## New nodes

`lem-sfb-normalized-scalar-restriction-push`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-normalized-scalar-restriction-push.json`,
realized by `Sheaf.Paper.NormalizedScalarRestrictionPush`: the right-adjoint comparison
conjugate to a counit-normalized scalar balancing isomorphism equals the canonical
geometric mate of restriction/pullback. The proof computes scalar mates on
representatives, uses uniqueness of the total left derived functor, and applies
Mathlib's iterated-mates identity. No change record is needed: existing public
signatures and definitions are unchanged.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
