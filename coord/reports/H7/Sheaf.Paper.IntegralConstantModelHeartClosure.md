## What changed

Proved `AlgebraicGeometry.ProEtale.isConstantModelConstructible_serre_padicIntegers`
from the existing integral local-finite-presentation closure and constant-model comparison.
The statement and all existing public imports are unchanged. Four proof imports add the
comparison, integral closure, local-finite-presentation coefficient transport, and ULift.
Private proved helpers transport finite constant models through coefficient isomorphisms.
The coefficient isomorphism is explicitly constructed by continuous postcomposition with
the norm-preserving ring equivalence on integer rings. No arbitrary witness supplies data
to a definition. The item node records this shorter route. No other modules are adapted.
Change record: `coord/changes/integral-constant-model-heart-closure.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.isConstantModelConstructible_serre_padicIntegers`
(node `lem-sfb-integral-constant-model-heart-closure`), the sole original hole.
Added: none. Remaining in delivered Lean files: none (one original hole closed, zero
holes added, zero split off). The retained proof compiles against the current sources
in 15.6 seconds through `lcompile.py`. The proof uses the existing
`integralLfpConstantModelComparison` theorem, whose existing hole remains a dependency;
it is not a newly introduced hole or a claim of an axiom-free target proof.

## No longer needed

No original public imports were removed: they supply the unchanged statement interface.
The old adic route is not used. Removed the five original proof imports:
`Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`,
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
`Sheaf.Paper.AdicStratifiedPerfect`, and
`Sheaf.Paper.IntegralCohomologicalAdicCriterion`. The DVR theorem is still used through
the existing public coefficient imports; the other four modules are not used.
Specifically these former proof dependencies are pruned
from this item's proof: `det-prop-sfb-qlbar-colimit-x-integral-limit`
(`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`),
`lem-weil-pbc-proetale-immersion-limit-preservation`
(`Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`),
`lem-sfb-adic-stratified-perfect` (`Sheaf.Paper.AdicStratifiedPerfect`),
`lem-sfb-integral-cohomological-adic-criterion`
(`Sheaf.Paper.IntegralCohomologicalAdicCriterion`),
`def-weil-abstract-derived-category` (`Mathlib.Algebra.Homology.DerivedCategory.Basic`),
`lem-weil-pbc-complex-ses-triangle` (`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`),
`lem-weil-l-adic-extension-complete`, and
`lem-weil-l-adic-extension-absolute-value` as separate completion/absolute-value steps.
`pqf-def-locnoeth`, `def-weil-pbc-quasi-compact-scheme`, and
`def-weil-sheaf-of-modules-category` remain part of the statement's meaning but need no
separate proof step. The DVR membership characterization and constant-model definition
are retained. Removed the seven obsolete top-level `tool_uses` approvals for the
coefficient limit, immersion-limit preservation, adic criterion, adic stratified-perfect
closure, short-exact triangle, completion, and absolute-value steps; kept the DVR approval.
These modules may still be needed elsewhere; this is pruning of this route.

## Where the brief, the DAG or earlier work was wrong

The retained report said that the adic criterion and stratified-perfect sources were
absent; both are present in the current checkout. The shorter route still avoids them.
The existing
integral constant-model comparison ties the coefficient field universe to the scheme
universe, so applying it directly to the small embedded field fails. The proof lifts the
field and explicitly transports coefficients and both constructibility predicates.
The blueprint unit's `realized` lists are empty, and this shorter route does not bypass
any realized unit statement or proof step. Zero presentations, empty strata and the
affine-local convention are preserved by the transport; no new statement is assumed.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
