## What changed

Replaced the sole admission in `Sheaf.CategoryTheory.RingedCechKoszulDualLimit`,
`CategoryTheory.exists_ringed_koszul_cech_comparison`, by a complete Lean assembly.
All existing public signatures, universes, structure fields, definitions and public
imports are preserved. The repair exposes an existing private theorem publicly, with
its type and proof unchanged. There is no target or definition repair or forced adaptation.

The assembly explicitly constructs the strict tensor-tower presentation by localization
and the existing total-right-derived-inverse-limit theorem, on the site and each slice.
It transports unit-normalized source restriction comparisons through theta, uses
the existing naturality theorem for the actual completion unit, proves all normalized
uniqueness fields by unit cancellation, and proves arbitrary restriction coherence by
normalizing the composite candidate. This includes the actual further-slice coherence
field. The empty-list strict unit is invertible because its Cech unit is evaluation at
one composed with a K-injective replacement. The outer theorem's colimit, telescope,
and finite-dual K-flatness arguments are unchanged.

Seven new statement modules isolate the argument. Five of their public statements are
proved: construction on one site; unit cancellation from the two actual idempotence
maps; normalized completion restriction; augmented finite-Cech restriction; and
restriction of one localization factor. The last calculation proves the localization
unit square from the defining sheafification-adjunction equation and the identity on
fractions, constructs the two-term complex isomorphism degree by degree, and checks its
augmentation. The finite-Cech argument extends the natural tensor restriction comparison
to total complexes and inducts on the finite list of augmented arrows. At internal Hom,
normalizing by the comparison at the ring object removes an automorphism of restriction;
there is no assumption that a chosen existential Hom comparison already preserves units.

The two remaining analytic statements are described below. This delivery changes proofs
and introduces statement modules and nodes. It also makes the existing naturality theorem
public in its original module, with its original proof and fully explicit type unchanged.
Scratch experiments are outside `lean/` and are not part of the delivery. The node for
comparison existence now records the actual route. The visibility repair has change record
`coord/changes/C1-completion-unit-naturality-public.md`.

## Proved and sorry left

Original module: one named hole replaced by a complete proof:
`CategoryTheory.exists_ringed_koszul_cech_comparison`.
`CategoryTheory.ringed_cech_koszul_dual_limit` remains a complete proof with the same
statement. The comparison structure and every existing signature are unchanged.

Five new public theorems are proved, with zero holes in their modules:

- `CategoryTheory.exists_ringed_cech_koszul_comparison_on_site`.
- `CategoryTheory.ringed_cech_completion_unit_hom_injective`.
- `CategoryTheory.exists_ringed_cech_completion_restriction`.
- `CategoryTheory.exists_ringed_augmented_cech_restriction`.
- `CategoryTheory.exists_ringed_localization_factor_restriction`.

Exactly two admissions remain in the delivery, each a named public theorem with source,
a full natural-language proof, and its own new module and node:

- `CategoryTheory.exists_ringed_cech_koszul_hom_limit_comparison`, in
  `Sheaf.CategoryTheory.RingedCechKoszulHomLimitComparison`, node
  `lem-weil-pbc-ringed-cech-koszul-hom-limit-comparison`. What remains is the natural,
  unit-compatible telescope/Hom-to-Roos comparison for an already specified strict
  presentation: finite duality with its sign, products of K-injectives, and transport
  through the right-derived universal property. It does not construct a presentation,
  prove uniqueness, or mention any slice restriction.
- `CategoryTheory.ringed_cech_completion_unit_idempotence`, in
  `Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence`, node
  `lem-weil-pbc-ringed-cech-completion-unit-idempotence`. What remains is invertibility
  of the actual maps L(eta_E) and eta_(L E): contract the localized factors, filter the
  augmentation cone, show both projections K tensor K -> K are quasi-isomorphisms,
  and identify their internal-Hom images with those actual maps on representatives.
  Naturality and the argument cancelling these maps are already proved separately.

This is a decomposition: one original hole closed and two holes added, a net change
of minus one in holes closed minus holes added before any unrelated project changes.
It is not a claim that the comparison is axiom-free, or that net sorry progress is one.
Existing imported admitted theorems are used in the intended stage-3 sense; their
independent proofs are not claimed here. No hole occurs in a definition, private helper,
or anonymous proof. No axiom, unsafe declaration or opaque replacement was introduced.

The existing `CategoryTheory.completion_unit_natural` is exposed publicly in
`Sheaf.Paper.ExtendedCechCompletionModel`; its proof is reused unchanged. No additional
hole is closed or added by this visibility repair. The original module has zero holes.

Validation on this continuation: all nine delivered modules passed
`lcompile.py --all` against the published build, including the fresh rerun on
2026-10-18 at 20:05 UTC. The import-direction check was rerun and again reported no cycle. The existing naturality theorem's
binders, statement and proof match current main exactly; its visibility and new
documentation are the only changes in ExtendedCechCompletionModel. The duplicate
naturality source module is absent from both current main and the sandbox. All six
external calls reuse `completion_unit_natural`, and every delivered node's
`proof_deps` is the union of its proof-step `uses`.

The previous completed dry run reached preflight and rejected only `lean.file` on
the naturality node's existing-declaration attachment. That field has been removed.
A subsequent retry timed out during worktree checkout before validation; no delivery
process remained active when this continuation began. The fresh dry run completed at
20:31 UTC with `OK (dry run)`, commit a23c9df107, review class CODEX. Three appended
axiom probes received no server response within 195–205 seconds; the tool explicitly
reports that the merge reruns these probes. All nine ordinary module compiles passed.
The required push is run through the unchanged delivery tool. No launcher script or shared repository
file is edited. The two remaining holes are the retained decomposition, not new work
introduced by this duplicate-theorem repair.

On the resumed repair at 2026-10-18 22:51 UTC, no interrupted delivery or compile
process remained active. A read-only remote-branch query confirmed that the branch
still pointed to the returned commit fddc7dbe2b, so no earlier repair push completed.
All nine retained modules then passed a fresh `lcompile.py --all` run. The existing
completion-model file still differs from current main only by the theorem's visibility
and documentation; its statement and proof are unchanged. The import-cycle check and
all nine proof-step/dependency consistency checks passed again.

The fresh dry run passed compilation but rejected the naturality node because its
existing-declaration attachment still contained `lean.file: null`. This node is new,
not a landed node, so its `file` key is now omitted entirely, as the gate requires.
The refreshed downstream query reports 1620 consumers and still just one existing
caller of the theorem name, in its original module. The change record now lists all
consumers from both queries with refreshed holders; no consumer adaptation is needed.

## No longer needed

The item drops these 25 direct proof imports:

- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.Algebra.Homology.HomComplex`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Algebra.Homology.DerivedInternalHom`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`.
- `Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`.
- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`.
- `WeilConjectures.Algebra.Homology.KernelShiftedMappingCone`.
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`.
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.

These are removals from the item's direct implementation, not claims that all 25 modules
become globally unreachable. Some remain transitively needed by the existing strict-tower,
internal-Hom restriction or finite-dual K-flatness theorems, and some remain the declared
proof dependencies of the two new analytic items. The source library's global closure
and other groups' proofs may also retain them.

The former single-step existence plan is replaced by the five recorded assembly steps.
Its generic triangulated filler dependency `lem-sf-triangle-morphism-iso` is not used:
all normalization, uniqueness and coherence are concrete natural-isomorphism equations.
The former restriction proof via preservation of the whole Roos tower is also unnecessary
for the assembly: source Cech completion restriction suffices, and target restriction is
transported through theta. No direct strict-tower restriction theorem or new coherence
admission is needed. The comparison proof uses the two actual Cech unit maps for cancellation. The existing
completion-model module is now imported to reuse its naturality theorem; its global
ideal/gluing reflector theorems are not applied by this comparison proof. That import
retains their transitive implementation dependencies, so it is not a pruning claim.

The new single-site construction also compiled after removing its redundant private
`Sheaf.Algebra.Homology.KFlatCoefficientUniverse` import; the original public import
of that module is retained unchanged in the item.

The original outer colimit, telescope and dual K-flatness dependencies remain. No unit's
statement or realized proof step is bypassed, no existing module is withdrawn, and no
whole-library pruning is claimed: a static import-overlay audit found no modules
removed from either the Challenge or TargetsCheck closure. The ledger remains authoritative.

The unlanded duplicate module `Sheaf.CategoryTheory.RingedCompletionUnitNaturality`
is removed from the sandbox delivery. Its three consumers now privately import
`Sheaf.Paper.ExtendedCechCompletionModel` and apply its existing theorem directly.
The retained naturality node now attaches to that existing declaration. No landed
module is deleted; the duplicate was absent from current main.

## Where the brief, the DAG or earlier work was wrong

Repair of the return at fddc7dbe2: the previous delivery duplicated
`CategoryTheory.completion_unit_natural` as
`CategoryTheory.ringed_cech_completion_unit_natural`. The binders and conclusions are
identical. The existing declaration was private, so simply importing its module did
not expose it. This repair makes it public in place, adds its source/proof docstring,
removes the duplicate module, and updates every delivery consumer and the node record.
`tools/import_direction.py may` confirmed the new import creates no cycle.
`tools/downstream.py --uses completion_unit_natural` found only the original internal
use, whose type and proof remain unchanged. The completed canonical query on this continuation lists 1573 transitive consumers.
All retain their signatures; the change record includes every reported consumer and
the three delivery consumers with current claim holders. The changed original module is unclaimed; no forced
adaptation is made to a module held by another group.

The existing statement is retained unchanged and no disputed statement was encountered.
The old existence node described telescope comparison, reflector uniqueness, all slice
restriction and all coherence as one step; it did not supply the necessary typed
intermediate interfaces. This delivery supplies those interfaces and writes their
combination in Lean. The admitted analytic portions are strictly parts of that argument.

The existing existential internal-Hom restriction theorem need not choose the comparison
at the ring object that agrees with evaluation at one. The proof therefore computes the
resulting automorphism of restriction and corrects the source comparison before imposing
unit normalization. It does not silently assume a missing normalization clause.

An early compile lacked recently landed finite-dual/colimit olean files; the published
build caught up and the subsequent compile succeeded. The previous retry's staging
timeout and provider interruption are recorded in the validation paragraph.
No launcher script or shared repository file was edited. No other group was
asked to do work and no second-reader section is claimed.

## New nodes

`lem-weil-pbc-ringed-completion-unit-naturality`: attached to the already proved
`CategoryTheory.completion_unit_natural` in `Sheaf.Paper.ExtendedCechCompletionModel`,
now public. Its original proof is reused; there is no second naturality declaration.

`lem-weil-pbc-ringed-cech-koszul-comparison-on-site`: proved construction of the strict
presentation and application of the prescribed-presentation analytic comparison.

`lem-weil-pbc-ringed-cech-koszul-hom-limit-comparison`: the remaining telescope/Hom and
strict-derived-limit calculation for a supplied presentation, with the actual unit.

`lem-weil-pbc-ringed-cech-completion-unit-idempotence`: the remaining two-projection
Cech tensor/Hom argument for the two actual completion-unit maps.

`lem-weil-pbc-ringed-cech-completion-hom-injective`: proved naturality and categorical
cancellation from the preceding idempotence theorem.

`lem-weil-pbc-ringed-cech-completion-restriction`: proved unit-normalized restriction,
using arbitrary Hom restriction comparisons and correcting their ring-object component.

`lem-weil-pbc-ringed-augmented-cech-restriction`: proved finite tensor induction and
passage through exact derived restriction, with the actual augmentations.

`lem-weil-pbc-ringed-localization-factor-restriction`: proved the sheafification unit
square, two-term complex comparison and augmentation, for both kinds of slice functor.

Every node inherits chapter `sec-proper-base-change` and unit `sk-thm-properbasechange`.
The blueprint ancestor and place are the current completed-pullback derived-limit formula
and its completion-unit sentence. Whole-blueprint searches for Cech completion, the
relevant Stacks tags, localization restriction, completion units and strict tensor towers
found no equivalent blueprint node. Mathlib searches were run through msearch.py and
recorded in searches.jsonl; the new nodes record actual LeanSearch, Loogle and grep queries.
Change record: `coord/changes/C1-completion-unit-naturality-public.md`, recording
the existing theorem's private-to-public visibility change and all consumers.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
