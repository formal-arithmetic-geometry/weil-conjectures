## What changed

Proved all nine unfinished theorems in
`Sheaf.Paper.CompletedAdicCoefficientDatum`, preserving the existing statements,
definitions and public imports. Commutativity descends from continuous functions
through sheafification and the completed inverse limit. Quotient transitions are
linear by the limit-cone equation. K-flat resolutions and the resolving-class
theorem construct the strict derived tower. Exact scalar restriction retains the
underlying abelian sheaf. Composed ordinary adjunctions give the normalized
balancing isomorphism and its uniqueness.

Added two proved general comparison lemmas in
`Sheaf.CategoryTheory.DerivedCategory.ResolvingModelComparison` and
`Sheaf.Algebra.Homology.RestrictedChangeTensorComparison`. The finite-reduction
proof transports the two K-flat counits to a common homotopy functor and applies
the resolving-model comparison. Explicit local instances and abstract functor
arguments prevent repeated unfolding of the completed ring during this step.
All added imports of the item module are private proof imports.

Validation: `lcompile.py --all` passed for the three delivery modules; the
item compiled in 53.9 seconds. Every delivery module has zero holes. Both new
node signatures match their Lean statements, and proof dependencies match the
union of their proof steps.
The delivery dry run passed. Its appended axiom probe for the item exceeded
60 seconds; preflight reports that the merge will rerun that probe. The
standalone source compilation passed as recorded above.

## Proved and sorry left

Closed all 9 original holes:

- `completedAdicRing_mul_comm`
- `completedAdicFiniteModuleStep_exists`
- `completedAdicOrdinaryTower_additive`
- `completedAdicReduction_exists`
- `completedAdicFiniteRing_mul_comm`
- `completedAdicRestriction_exact`
- `completedAdicFiniteReduction_comparison`
- `completedAdicBalance_exists`
- `completedAdicCommProjection_comp`

No holes remain in the item. No holes were added or split off. Both new public
lemmas, `CategoryTheory.Functor.nonempty_iso_of_resolving_models` and
`SheafOfModules.nonempty_restrictedChangeTensorIso`, are proved in full.

## No longer needed

None. No original import, declaration, node or module is withdrawn. The proof
uses the stated K-flat-resolution, scalar-extension and resolving-class APIs,
and retains the unit's strict-tower route. No adopted source module is changed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The main datum node had an empty construction
proof; its current blueprint update moves it from order 1239 to order 1307.
The proof record now describes the completed-coefficient realization proved here.
The library lacked the two general comparisons below. In particular, the
ordinary tensor comparison at equal site universes does not specialize to this
pro-etale site, whose objects and morphisms have different universes.

## New nodes

`lem-pbc-resolving-model-comparison`: two functors on a derived category are
naturally isomorphic when their comparisons with one triangulated homotopy
functor are invertible on a resolving class. The proof uses the existing
resolving-class theorem, the universal derived lift and essential surjectivity
of the homotopy localization. Zero categories and unbounded models are included.

`lem-pbc-restricted-change-tensor-independent`: restricted scalar extension is
naturally right tensor by the restricted target ring, with independent site and
coefficient universes. The proof constructs the section tensor identification,
commutes restriction with sheafification and uses the braiding. No flatness is
assumed; zero rings and modules are included.

Change record: `coord/changes/completed-adic-proof-context.md` documents the
extra private-helper universe names and section-local monoidal attribute
flagged by the interface checker. Existing public declaration entries and
public imports are identical; no consumer needs adaptation.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
