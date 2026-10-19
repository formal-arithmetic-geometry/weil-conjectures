## What changed

`Sheaf.Paper.IntegralModels.integral_models` now has a complete Lean proof assembling
all nine conjuncts. The statement, universes, binders, definitions and public names are
unchanged. The Tor equality uses `localizingClosure_ctf_equals_bc`; the three operation
clauses use `CondensedRing.integralModelsOperations`; the two generation clauses and
all positive-exponent reductions use `integral_models_generators`.
The inverse-image clause also uses `cartesianCoefficients`, the canonical
`CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`, and isomorphism stability from
`constantModelConstructibleFiniteTor_wellDefined`. The exactness instances come from the
existing cartesian-coefficients theorem.

The three remaining coefficient comparisons are named public statements for source steps 2, 3 and 4--5.
The complete-object comparison is now proved from the ambient coefficient presentation
and `ConstantCompletion.equivalence`. The proof restricts the ambient equivalences using
`Equivalence.congrFullSubcategory`, composes them with the existing completion equivalence,
and constructs the natural functor comparison by associators, whiskering and the unit.
The Stacks comparison and residue criterion are composed with `Iff.trans`.
The residue criterion itself is proved: arbitrary-object completeness is reflected using the
Koszul completion-unit criterion; the specified residue realization is exact by reflection
through additive sheaves; the existing finite-ring essential-image criterion then supplies
etale origin. Its remaining coefficient/cohomology comparison is separate from completeness
and etale origin.
The ambient coefficient presentation is also now proved: section-action and small-site
equivalences give the actual derived equivalences, the first-reduction squares identify
kernel ideals, and exact restriction reflects local completeness. The proof constructs
the scalar-restriction natural isomorphism before deriving it. Its remaining hypothesis
is strictly a diagram of four ring sheaves and three specified maps; it contains no
module-category, derived-category or completeness conclusion. The remaining holes cover
that normalized ring diagram in step 2, step 3, and the coefficient/cohomology part of
steps 4--5.
Seven other top-level conjuncts are assembled entirely from existing declarations.

The canonical definitions move to `Sheaf.Paper.IntegralModelsDefinitions`, publicly
re-exported by the item, avoiding an import cycle. Explicit result types retain the previously
inferred types. An explicit K-injective-resolution instance fixes repeated instance synthesis
in `integralModelResidueEtaleOrigin`; the actual right-derived functor is retained. Profiling
located the cost there; the complete definition module compiled in 38.7 seconds in the
earlier all-module verification.
No target signature or mathematical definition changes. The earlier consumer scan has 336
transitive importers and just one textual residue-origin user, the item itself; no existing
consumer is adapted. The complete extraction also re-exports `restriction`; the follow-up scan has 337 importers, and preflight
matched five additional files by the basename `restriction`. Source inspection shows
namespace-local constants, fields or parameters, with no use of the moved definition;
all five textual matches are now listed in the change record. The exact old and new blocks and consumer effects are recorded in
`coord/changes/integral-models-definition-extraction.md`.

Verification before the final ring-diagram refinement: remote `lcompile.py --all`
completed all nine then-present modules with exit code 0 and no warnings. Individual
times were 38.7 seconds (definitions), 20.2 (presentation), 39.2 (realization), 6.4
(Stacks comparison), 9.8 (completeness reflection), 17.3 (complete restriction), 39.4
(residue comparison), 20.6 (residue criterion), and 35.9 (item). The new ring diagram
and the completely proved presentation then compiled together in 11.3 and 20.3 seconds.
The unchanged direct consumer `Sheaf.Paper.IntegralConstantModelHeart` compiled against
the sandbox modules in 5.8 seconds (`consumer-interface-check.log`); its temporary test
copy is outside the delivery. A source comparison confirms the original `integral_models`
signature is byte-for-byte unchanged. The current packet has three holes, all exactly
the public theorem bodies named below, and no Lean line exceeds 100 characters.
The final `lcompile.py --all` (`compile-delivery-final-all.log`) completed all ten
modules with exit code 0 and no warnings. Times in import order were 1.6, 14.1, 1.8,
1.7, 30.8, 2.0, 12.8, 19.1, 21.0 and 21.8 seconds. All ten node proof-dependency
lists equal the union of their proof-step uses, every recorded Lean statement occurs
verbatim in its module, and all referenced dependency node IDs exist.

The first full dry run (`dry-run-ring-diagram.log`) reached server preflight and
returned six record diagnostics: a missing LeanSearch entry for the exactness node,
and five textual restriction-name matches absent from the user table. The search and
all five inspected user entries are now recorded. The residue-realization axiom probe
timed out on that pass. A profiled copy with the unmodified standard probe then passed
in 34.4 seconds, reporting `SHEAF-PROBED 5` and no unsupported axioms
(`residue-realization-profile-probe.log`). The diagnostic copy is outside the delivery.

The repaired required dry run (`dry-run-repaired-records.log`) passed: commit
`505f4ce0d8`, review class CODEX, no push. It compiled all production modules and passed
server preflight. The repeated axiom probes timed out for the item and residue realization
on that run. The item's probe passed in the first full run, and the explicit standard
residue-realization probe passed in 34.4 seconds as recorded above. The other probes
passed. These repeat timeouts are preserved here; the maintainer's merge probes again.

## Proved and sorry left

Original holes: 1, `AlgebraicGeometry.ProEtale.integral_models`.
This hole is closed by a complete assembly proof, but the delivery is a **decomposition**,
not a net proof: it adds the following 3 strictly smaller holes.

- `AlgebraicGeometry.ProEtale.embeddedIntegral_coefficient_ring_diagram`
  (`lem-sfb-embedded-integral-coefficient-ring-diagram`): the four normalized ring-sheaf
  isomorphisms and three commuting scalar/first-reduction squares. All subsequent
  module, derived, local-completeness and restriction transport is proved in this delivery.
- `AlgebraicGeometry.ProEtale.embeddedIntegral_stacks_comparison`
  (`lem-sfb-embedded-integral-stacks-comparison`): still needs transport of the existing
  Stacks criterion, preserving residue maps, constructibility and relative Tor intervals.
- `AlgebraicGeometry.ProEtale.embeddedIntegral_residue_comparison`
  (`lem-sfb-embedded-integral-residue-comparison`): the canonical first-reduction comparison,
  constructible cohomology transport and residue-field Tor/boundedness calculation.
  This statement contains neither completeness nor etale-origin predicates.

Additionally proved, with zero holes in their modules:

- `AlgebraicGeometry.ProEtale.embeddedIntegral_coefficient_presentation`: constructs
  the ambient derived equivalences, proves preservation/reflection of first-reduction
  completeness and the natural comparison of actual scalar restriction functors from
  the normalized ring diagram. The new private transport helpers are fully proved.

- `AlgebraicGeometry.ProEtale.embeddedIntegral_complete_restriction`: the complete-subcategory
  equivalence and comparison of the specified ambient restriction functor.
- `AlgebraicGeometry.ProEtale.embeddedIntegral_complete_iff`: completeness reflection for
  arbitrary complexes, from the Koszul completion units and faithful derived restriction.
- `AlgebraicGeometry.ProEtale.integralModelIntrinsicRealization_exact`: finite-limit and
  finite-colimit preservation for the actual constant-scalar realization. Its induced
  termwise derived functor is constructed as `integralModelIntrinsicDerivedRealization`.
  `integralModelFirstDerivedReduction` fixes the original first reduction's source and
  target categories. `integralModelConstantResidueCondition` and
  `integralModelIntrinsicBoundedConstructible` name the same cohomology/Tor and ordered-bound
  predicates that appear in the residue comparison. Their bodies use the original scalar
  maps. These explicit interfaces avoid repeated elaboration of large tensor and localization
  instances when exporting the comparison module. Every construction has zero holes.
- `AlgebraicGeometry.ProEtale.embeddedIntegral_residue_criterion`: combines completeness
  reflection, first-residue cohomological comparison and the existing finite-ring
  constructible derived-origin theorem, using the canonical right-derived/termwise iso.

These are reductions from the three remaining comparison statements and existing library
results; they do not assert that the imported holes are proved.

Each remaining hole is in its own new module, with proof exactly `:= by sorry`, a source, a full proof in
words, and a matching node. No hole occurs in a definition. The definition module adds
zero holes. Local counts are 1 closed, 3 added, 3 left, net minus 2 before the ledger's
import-closure accounting. Existing imported sorries are not reported as newly proved.

Edge cases checked mathematically: arbitrary unbounded input K in the comparison clauses;
zero objects and empty schemes; pi is a generator of the maximal ideal, so exponent one
has a nonzero finite residue field; no assumption that the entire ambient constant and
continuous coefficient categories are equivalent. The residue criterion deliberately
contains no bounded-constructible-integral condition: it is the separate comparison of the
Stacks predicate with completeness and residue etale origin, not a restatement of the item.

## No longer needed

The main assembly removes these proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`
  (`lem-pc-sites-modules-sheafification-flat`).
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
  (`lem-pc-bounded-above-flat-kflat-site`).
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
  (`sk-thm-pe-constructible-comparison`).

The first two remain planned dependencies of the residue-comparison node, so this is
import pruning at the assembly level, not a claim that their work disappears globally.
For the last, the more specific existing
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
(`lem-weil-pbc-finite-ring-constructible-derived-origin`) supplies exactly the intrinsic
bounded-derived essential-image criterion needed by that residue step. The general
comparison theorem need not be applied separately in the item.

The parent no longer directly uses
`det-prop-integral-criterion-constant-coefficients`,
`det-lem-integral-models-stacks`, `lem-weil-pbc-constant-completion-equivalence`,
`lem-pc-sites-modules-sheafification-flat`,
`lem-pc-bounded-above-flat-kflat-site`, or `sk-def-sfb-derived-tensor-hom` as proof steps;
the coefficient comparisons now record the needed lower dependencies. The tensor
assertion is supplied by the existing operations theorem. The parent's obsolete tool-use
entries for completion comparison, flat sheafification and bounded-flat K-flatness are
removed; their mathematical uses remain documented in the lower residue/completion nodes.
The localizing-closure tool-use approval is retained. The original public imports are
retained through the definition module to preserve the exported interface. The main file
consolidates its 16 repeated public imports into that one public import; each remains
publicly available through `IntegralModelsDefinitions`. The previously scratch-only
small-site equivalences are now used in the proved coefficient presentation. Unused
lifted spectral integer helpers and the Stacks helper imports `Sheaf.NumberTheory.Padics.CoefficientExtension`,
`Mathlib.Algebra.Field.ULift`, and `Mathlib.LinearAlgebra.FiniteDimensional.Basic`, were
removed from the delivered comparison modules. The compiled explorations remain scratch
work only. No entire
existing module is withdrawn, and no global module-pruning credit is claimed.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies do exist and can be used despite their sorries. The obstacle is
an interface mismatch: `IntegralModelsStacks` and `IntegralConstantCompletion` use
`Padic.coefficientExtensionIntegers` with spectral norm and a chosen uniformizer, whereas
the item uses the embedded `PadicAlgCl.integers`, its induced topology, an arbitrary supplied
uniformizer, and an intrinsic continuous-residue realization. These are mathematically
isomorphic, but their ring sheaves, module categories, derived restriction maps and
completeness predicates are not definitionally identical. The new comparisons name the
missing transport argument; applying the old theorem verbatim does not type-check.
There is also a universe issue: the existing Stacks and integral-constant-completion
theorems bind `E : Type u` and `X : Scheme.{u}`, whereas the embedded finite subfield is
in `Type 0` and this item allows `X : Scheme.{u}`. A direct application specializes the
scheme to `Scheme.{0}`. Lift the field to `ULift.{u} E.1` first, then transport the
coefficient ring, its topology and its actual scalar and residue maps.

The actual residue's finiteness and discreteness are proved by private helpers in
`IntegralModelsResidueCriterion`: rewrite the uniformizer ideal as the maximal ideal,
use `Valuation.mem_maximalIdeal_iff` to identify it with the open unit ball, and apply
`QuotientAddGroup.discreteTopology`. The earlier scratch version compiled in 21 seconds;
the complete criterion now compiles in 20.6 seconds. No additional public hole is needed.

The resumed scratch calculation proves that the spectral integer subring equals the
embedded valuation subring: provide the normed-space structure induced from Qbar, apply
`NormedAlgebra.norm_eq_spectralNorm`, use the DVR witness's membership characterization,
and reduce real versus nonnegative-real inequalities with `NNReal.coe_le_coe`. This
calculation compiled in 19 seconds. The follow-up lifted isometry and homeomorphism,
with the actual spectral and embedded topologies specified explicitly, compiled in 12.6
seconds (`embedded-spectral-topology-final.log`). The induced condensed ring-object
isomorphism then compiled in 19.7 seconds (`embedded-spectral-point-iso2.log`). Existing
`Sheaf.Paper.IntegralCoefficientExtComparison` also contains the corresponding embedded
versus lifted spectral comparison, but does not identify the actual scalar, residue,
and local-completeness diagrams of this item. These calculations identify the continuous ring sheaves. They do not identify the constant
scalar and first-residue diagrams together with local completeness and derived reduction.
The naturality square for the actual constant-to-continuous maps also compiled in
24.7 seconds (`embedded-spectral-scalar-naturality7.log`), after comparing their adjunction
mates and making the topology/forgetful functors explicit. These calculations are retained
as scratch work; no unused public declaration or additional hole is added.

The unit's route is retained: Tor equality; complete-object restriction; Stacks and residue
criteria; inverse image, tensor and locally closed extension; finite-E and algebraic-closure
generation; and all lattice reductions. No unit statement or realized route is bypassed.
The main theorem's existing docstring continues to record that twelve-step source route.

A further scratch calculation proves flatness of every sheaf of vector spaces and the
interval equivalence between Tor amplitude and concentrated cohomology, using flat
sheafification and bounded flat representatives. This is in the ordinary module-valued
sheaf presentation. The remaining residue hole includes transporting it through the
specified internal coefficient realization; the scratch theorem is not counted as a proved
internal comparison.

The dispatcher reference clock reset across resumptions. The preserved search ledger starts
at 2026-10-18 20:23 UTC, while the current `.budget` start is 2026-10-19 17:07:47 UTC.
Earlier dry-run logs (`dry-run-current.log`, `dry-run-continuation.log`) show separate
14-minute, 4-minute and 18-minute reference readings despite retained proof work. These are launcher
metadata, not proof time limits; no budget file or launcher script was edited. Proof work
continued after each resumption.

## New nodes

`def-sfb-embedded-integral-model-coefficients` owns the unchanged canonical definitions
formerly attached to the item, in `IntegralModelsDefinitions`. It has zero holes. The
parent reaches this ownership node through the comparison statements; its Lean
attachment retains only `integral_models`. The mathematical statement and statement
dependencies of the parent are unchanged. See `coord/changes/integral-models-definition-extraction.md`.

`lem-sfb-embedded-integral-complete-restriction` isolates proof step 2 in
`IntegralModelsCompleteRestriction`, with exactly the specified ambient restriction
comparison. It is proved from the general completion equivalence and the new ambient
coefficient-presentation statement; it leaves zero holes.

`lem-sfb-embedded-integral-stacks-comparison` isolates proof step 3 in
`IntegralModelsStacksComparison`. It leaves one hole for transporting the existing Stacks
criterion to the embedded coefficient presentation.

`lem-sfb-embedded-integral-residue-criterion` isolates proof steps 4--6 in
`IntegralModelsResidueCriterion`. It is proved from the three comparison/exactness results
below and the finite-ring derived-origin theorem. Its statement is independent of the
integral bounded-constructible predicate, making composition with the Stacks criterion
substantive. The new nodes use the item's chapter, unit and source and carry recorded
Mathlib searches.

`lem-sfb-embedded-integral-coefficient-presentation` isolates the ambient category
comparisons and compatibility with local completeness and scalar restriction in
`IntegralModelsCoefficientPresentation`. It now leaves zero holes: the section-module,
small-site, coefficient-isomorphism, local-completeness and derived restriction transport
is fully proved from the normalized ring-sheaf diagram.

`lem-sfb-embedded-integral-coefficient-ring-diagram`, in
`IntegralModelsCoefficientRingDiagram`, isolates only the normalized scalar and two first
reduction squares from source step 2. It has one hole. It has no module or derived
category assertion and is strictly smaller than the proved coefficient presentation.

`lem-sfb-embedded-integral-complete-reflection`, in `IntegralModelsCompleteReflection`,
proves preservation and reflection of arbitrary-object completeness. It has zero holes.

`lem-sfb-embedded-integral-residue-realization-exact`, in `IntegralModelsResidueRealization`,
proves exactness of the specified finite residue realization. It has zero holes.

`lem-sfb-embedded-integral-residue-comparison`, in `IntegralModelsResidueComparison`,
is the remaining first-reduction coefficient/cohomology comparison, with no completeness
or essential-image conclusion. It has one hole and a source proof following steps 4--5.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
