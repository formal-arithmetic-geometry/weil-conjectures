## What changed

Proved `AlgebraicGeometry.Scheme.integral_cohomological_adic_criterion` in
`Sheaf.Paper.IntegralCohomologicalAdicCriterion`, preserving its statement, universes,
public imports and the existing small-site instance. All new helpers are private and proved.
No existing definition or statement was changed and no other module was adapted.

The proof follows Bhatt--Scholze Proposition 6.8.11(3): finite free scalar resolutions
supply the degree-zero case, bounded cohomological devissage gives the forward implication,
and cohomology of local perfect models gives the converse. It retains the integral-model
unit route and uses `adic_stratified_perfect` for its advertised equivalence and closure
properties; that existing dependency is deliberately not proved in this delivery.

Reused existing proved helpers through private `import all`: the exact constant functor
from CompletedConstantSheafReduction, inverse-image exactness and adjunctions from
ProEtaleOperations, coefficient-integers adic completeness from AdicLimitFiniteModules,
and the double-complex augmentation from ScalarModelFiniteFlatResolution. The scalar
resolution itself uses Mathlib's finite-presentation surjection and `Submodule.basisOfPid`.
The final bounded assembly uses the proved `DerivedCategory.prop_of_bounded_of_degreewise`.

The key comparison identifies extension along the identity of the inverse-image ring with
the identity by uniqueness of left adjoints. Comparing the derived functors on actual
complex representatives then identifies `sfbLocalRestriction` with the derived exact
inverse-image/slice composite. Both local-model predicates retain that same inverse-image
coefficient ring, so no coefficient transport to a separately constructed stratum ring is
needed. Exact scalar realization and restriction give the required homology isomorphisms.

Validation: the complete module compiled cleanly through `lcompile.py` in 9.1 seconds.
All Lean lines are at most 100 characters.

Updated only `proof`, `proof_deps`, `proof_origin` and obsolete `tool_uses` in
`lem-sfb-integral-cohomological-adic-criterion`. No new nodes or public declarations. The preflight-required change record for added
section commands and private helper instances is
`coord/changes/J4-integral-cohomological-criterion-proof-context.md`.
It records all 14 downstream modules; none needs adaptation.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.integral_cohomological_adic_criterion`
(node `lem-sfb-integral-cohomological-adic-criterion`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes left in the item: 0.
No split-off statements, no holes in private helpers or definitions, and no additional
files containing holes. Existing imported theorem holes remain their original items.

The scalar argument permits rank zero and torsion modules; it never assumes the presented
module is torsion-free. The perfect-complex cohomology argument needs only Noetherianity,
not flatness of its homology. Empty strata and the empty scheme are handled by the
unchanged cover/stratification witnesses and the existing zero/bounded devissage clauses.

## No longer needed

Removed the following original private imports:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`: its theorem is still used through
  the imported proved coefficient-completeness module, so this direct import is redundant.
- `WeilConjectures.CategoryTheory.TruncationTriangle`: the existing bounded degreewise
  devissage theorem supplies the finite truncation induction.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`: compare the already defined
  restriction with the derived exact functor directly.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: its interface is already available
  through the scalar exactness dependencies; the direct import is redundant.
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`: the proof works over the
  common inverse-image coefficient ring and does not identify it with a new completion.
- `Sheaf.Paper.CondensedConstantConstructibility`: neither implication uses condensed models.
- `Sheaf.Paper.ConstantModuleSectionProperties`: use the actual constant-module functor's
  proved exactness and exact completed scalar extension.

The new proof does not require the former proof dependencies
`lem-sfb-integers-profinite-tower`,
`lem-sfb-finite-constant-model-two-term-free-resolution`
(module `Sheaf.Paper.FiniteConstantModelResolution`),
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`lem-weil-pbc-truncation-triangle`, or
`lem-sfb-local-integral-perfect-model-cohomology`
(module `Sheaf.Paper.LocalIntegralPerfectModelCohomology`).
The PID/Noetherian elementary fact is supplied by the existing DVR instances.
The constructibility witnesses use `IsCompletedConstantStratified` directly.

Deleted obsolete top-level tool approvals for
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`det-prop-integral-criterion-constant-coefficients`,
`lem-weil-pbc-constant-module-section-properties`, `def-pc-flat-sheaf-modules`,
`lem-weil-pbc-truncation-triangle`,
`lem-weil-pbc-proetale-immersion-limit-preservation`,
`def-weil-pbc-ringed-derived-restriction`, `lem-sfb-integers-profinite-tower`, and
`lem-sfb-finite-constant-model-two-term-free-resolution`.

The unit-route private import `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
is retained after preflight identified its unit-route status. Its theorem is not required
for the direct local-model comparison; its module remains imported.

These are removed direct imports/proof edges, not module withdrawals. Their declarations,
existing proofs and any other consumers remain intact. No source-library module is edited
or deleted; no UNIT statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. The planned local perfect cohomology child is
stated for unlifted coefficients and transports them to the completion on the stratum.
The item uses ULift coefficients and both published local-model predicates instead restrict
global models to the same inverse-image ring. Comparing these exact functors directly is
shorter than adding that coefficient transport. Similarly, the existing bounded degreewise
devissage theorem already implements the planned truncation induction.

The scalar presentation and augmentation are proved using existing Mathlib and library
results; no new unresolved intermediate theory was necessary. The coefficient-completeness
helper is already fully proved, so the larger profinite-tower theorem is unnecessary here.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
