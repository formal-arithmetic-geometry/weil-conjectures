## What changed

Proved `AlgebraicGeometry.Etale.module_cohomology_conventions` without changing its
statement or either comparison definition. Added one fully proved private helper
`moduleForget_injective_evaluation_isZero`. It combines the existing constant-ring
module equivalence, injective module-presheaf theorem, universe-compatible Cech
cocycle lifting, categorical Cech comparison and etale Cech vanishing criterion.
The remaining proof uses canonical acyclic derived base change for evaluation and
the existing canonical D+ direct-image comparison. Updated the theorem's proof
explanation and its DAG proof route. No definition or statement repair, consumer
adaptation, new module, new node, or change record was needed.

Searches: msearch.py leanfinder for exact coefficient forgetting and derived evaluation
returned unrelated smooth-sheaf results; Loogle for rightDerived/IsZero returned
Mathlib's injective-vanishing theorem; grep for injective evaluation/acyclicity
returned no applicable Mathlib comparison. Source searches found the canonical
acyclic base-change theorem and the proved private Cech helper reused here.

The proof keeps arbitrary schemes, arbitrary commutative coefficients in Type (u+1),
all etale objects, and every nonnegative derived degree. Positive-degree vanishing
uses q=n+1; q=0 in both comparison clauses follows from the same canonical maps.
The empty scheme and zero ring require no exclusions.

Validation: the final module compiles through lcompile.py without warnings. The
required delivery dry run performs the independent signature and axiom checks.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.module_cohomology_conventions`
(node `det-pbc-conventions-module-cohomology`).

Added 0 holes; split off 0 statements. No `sorry` remains in this delivery.
The proof uses the project's existing dependency declarations; this does not
assert that all of those dependencies are already free of transitive holes.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`
- `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`
- `Mathlib.CategoryTheory.Abelian.RightDerived`

The original public imports are retained as the module's public re-export interface.
Only unused proof imports are pruned, so no consumer API changes are introduced.

Removed direct proof dependencies (and any corresponding obsolete tool approvals):

- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-cohomology-over-object-localization`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`
- `lem-weil-pbc-derived-functor-injective-vanishing`
- `lem-weil-pbc-etale-constant-ring-module-equivalence`
- `def-weil-pbc-direct-image`

These are pruned from this node's direct proof route; no claim is made that they
are unused elsewhere or absent from every transitive dependency.
The module itself remains needed and is not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan suggested applying the common-universe ringed-site evaluation
comparison directly. Its SmallCategory/common-value-universe interface does not
directly fit the small etale category here (objects and values in Type (u+1), homs
in Type u), and the separate etale enough-injectives statement takes smaller
coefficients R : Type u. Rather than change these declarations, this proof reuses
the existing universe-compatible Cech argument from the private helper in
ModuleAbelianDerivedDirectImageComparison. Exactness and enough-injectives instances
needed for canonical derived base change are already available through retained
imports. No false statement is asserted or weakened.

The route uses existing tools from other units: module-sheaf-constant-ring-equivalence,
ringed-site-injective-module-injective-presheaf,
injective-presheaf-module-cech-cocycle-lift-max,
etale-site-cech-complex-comparison, cech-vanishing-criterion, and
src-right-derived-functor-plus-base-change-of-right-acyclic (full node identifiers
are in proof_deps). They supply encoding, Cech acyclicity and generic canonical
base change; this convention unit has no separate realized statement or proof
steps that this route could bypass. Any additional tool approvals are left for the
maintainer; the delivery only removes obsolete approvals, as required.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
