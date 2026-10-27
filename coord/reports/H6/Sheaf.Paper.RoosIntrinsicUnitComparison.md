## What changed

Proved the normalized comparison in `Sheaf.Paper.RoosIntrinsicUnitComparison` without
changing its theorem statement or the bodies of its four public definitions.
Explicit return types pin the principal tower, its fiber, the quotient tower and its
comparison to their definitionally equal coefficient-module presentation. The proof constructs the signed
mapping-fiber isomorphism and both zero-component augmentations, checks their strict
compatibility, and evaluates Roos on every K-injective tower resolution with the specified
ordinary-limit normalization. It transports the existing ordinary completion functor and
its unit through a natural isomorphism of strict quotient towers. Existing completeness
equivalences then give invertibility on complete objects and stability under shift.

Adapted the unclaimed `Sheaf.Paper.PrincipalIntrinsicCompletion` only by adding the
explicit result types of its `tower` and `fiber`; their bodies and all other declarations
are unchanged. Its only current repository consumer is the assigned item.

Added `Sheaf.Paper.QuotientTensorScalarTowerComparison`: the independent algebraic
comparison of the total tensor quotient tower with ordinary termwise scalar reduction,
including transitions, naturality, and the actual quotient augmentation. Its construction
uses degree-zero totalization and the sheafified balanced exchange of tensor factors.
It assumes neither K-flatness nor completeness. Both modules publicly import only
`PrincipalIntrinsicCompletion`, which already reexports the statement APIs they need.
In particular, its public import of `PrincipalKoszulStrictReplacement` publicly reexports
`CoefficientExtensionFinite`; the coefficient-extension unit route and its coefficient
datum remain in use.
Additional proof imports are private. No adopted source-library declaration is changed.

## Proved and sorry left

Closed the original hole
`WeilConjectures.RoosIntrinsicUnitComparison.roos_intrinsic_unit_comparison`
(node `lem-a1-roos-intrinsic-unit-comparison`) by a complete Lean proof from the stated
library declarations. The new theorem `WeilConjectures.quotientTensorScalarTowerComparison`
(node `lem-a1-quotient-tensor-scalar-tower-comparison`) is also proved, including its
transition, naturality and augmentation assertions.

Original holes closed: 1 of 1. Holes added: 0. No `sorry` remains in any of the three delivered modules.
There are no deferred intermediate statements. Existing imported statements with their
own holes remain separate items of the project. The modules are checked through
`lcompile.py`. The delivery command performs the required compilation and preflight checks.
Private categorical transport lemmas avoid repeatedly unfolding the completion comparison
when checking unit, naturality and completeness identities. The concrete comparison uses
the standard derived-category instance for its actual coefficient-module presentation.
The cokernel computation handles the degree-zero unit, and the Roos coordinates prove
augmentation naturality. The scalar proof restricts its generator rewrite to the right-hand side, avoiding an
unnecessary comparison of sheafification maps. The main proof needs only individual
quotient-tower maps, so its redundant functor construction and functor-law proofs are removed.
The degree-zero scalar comparison is assembled as a natural isomorphism before taking
components. Its naturality is then the naturality of that isomorphism. The tensor
presentation is compared through inverse morphisms. The signed lift uses the existing
proved cocone naturality lemma; shifted K-flatness uses the existing proved
`KFlatFixedTensor.shift_kFlat` lemma.

## No longer needed

The route no longer applies the planned declarations of
`Sheaf.Paper.IntegralScalarExtensionWellDefined`,
`Sheaf.Paper.FiniteFreeCompletedScalarComparison`, or
`Sheaf.Paper.IntegralReductionTowerWellDefined`, nor does it invoke the large existential
comparison theorem of `Sheaf.CategoryTheory.StrictRoosComparison`. The corresponding
proof-dependency and tool-use entries were removed from the item's node. Instead it uses
the primitive quasi-isomorphism statements of `StrictRoosDerivation` and the already
specified completion on slices. The old intrinsic-definition proof reference is replaced
by the module owning the actual principal intrinsic fiber used in the statement.

The proof also avoids importing `CompletedScalarShiftDescent`,
`IntegralReductionTowerCanonical`, `IntegralReductionTowerUnrestricted`, and
`KFlatRoosRepresentativeInvariance`: shift stability uses the existing
local derived-Hom criterion and the proved K-flat tensor shift lemma. These were exploratory proof
imports. The unused public import of `StrictRoosComparison` is removed. There are no
current Lean importers of the item module. Some avoided modules remain reachable through
other target imports, so this report makes no claim that they leave the global target
closure. No module or public declaration is withdrawn. The unused proof-local quotient functor
is removed; the specified individual tower maps supply all the maps the proof needs.
The duplicate acyclicity-under-shift, acyclicity-under-isomorphism, and tensor-shift
proofs are removed in favor of `KFlatFixedTensorTriangulated.shift_kFlat`. The unused
generic rearranged-square lemma is removed after the strict comparison square is
checked directly in the chosen coefficient category.

The removed planned node dependencies are
`lem-weil-integral-scalar-extension-well-defined`,
`lem-weil-finite-free-completed-scalar-comparison`,
`lem-weil-integral-reduction-tower-well-defined`,
`lem-weil-strict-roos-comparison`, `def-weil-integral-reduction-tower`,
`def-weil-pbc-intrinsic-completion`, and `def-weil-abstract-derived-category`.
The proof uses the ordinary tower on slices, the actual principal intrinsic fiber,
and Mathlib's standard derived category instead. The redundant private import of
`PrincipalKoszulStrictReplacement` was removed because the preserved public import
of `PrincipalIntrinsicCompletion` already exports it.

The redundant public imports removed from the item are `IntegralOperationsWellDefined`,
`CoefficientExtensionFinite`, `CompletedIntegralConstantMapOfUniverses`,
`KFlatIndependentCoefficients`, `FlatOnSite`, `Mathlib.Algebra.Homology.BifunctorShift`,
and `Mathlib.Algebra.Homology.DerivedCategory.Basic`. The new scalar module also drops its
redundant public import of `IntegralDerivedOperationsOnSlices`. These APIs remain publicly
available through `PrincipalIntrinsicCompletion`. Four redundant private Mathlib imports
are removed: `EnoughInjectives`, `Localization.Predicate`, `HomotopyCategory.Acyclic`, and
`Data.Nat.Prime.Infinite`, already publicly reexported by that same import.
The private `import all IntegralOperationsWellDefined` is also removed. The private
import of `IntegralDerivedOperationsOnSlices` remains necessary for its primitive cone-map
and cocone-lift identities. Good representatives are supplied by the existing localization of flat-term K-flat
complexes and its essential surjectivity.

The item node's base `proof_deps` entries no longer used are
`lem-a1-principal-augmented-roos-descent`, `lem-a1-signed-fiber-roos-normalization` and
`lem-a1-quotient-unit-shift-completeness` (unsplit planned helpers, proved directly inside
the item module; the item was their only citer, so they are no longer needed by any node),
`lem-weil-finite-free-completed-scalar-comparison`, and
`lem-weil-proetale-countable-products-exact` (the proof uses
`AlgebraicGeometry.Scheme.ProEt.products_exact`, node `det-pe-products-exact`, instead;
reviewer correction). The reviewer also added `lem-weil-pbc-ring-sheaves-grothendieck`
(`SheafOfModules.isGrothendieckAbelianOfUniverses`, used for the K-injective Roos
normalization) to the node's step 4 and `proof_deps`.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The planned finite-free scalar comparison is unnecessary:
tensoring with a degree-zero quotient agrees with ordinary scalar extension for every
complex, and the already available completion comparison performs the localization step.
The unit's realized route is preserved. Local transparency settings keep chosen limits,
the Roos functor and derived localization opaque behind proved APIs, while exposing
coefficient aliases and the canonical preadditive fields of the abelian instance.
The local settings change no public data. The separate result-type annotations are
definitionally equal to the former inferred types, as recorded for independent review.

## New nodes

`lem-a1-quotient-tensor-scalar-tower-comparison`, realized by
`WeilConjectures.quotientTensorScalarTowerComparison` in the new module, records the genuine
algebraic normalization step before derived localization. Its proof checks transitions and
the unit on tensor generators, with the source and full argument in the theorem docstring.
The construction covers empty schemes, zero complexes and unbounded complexes. The change
record for the import interface and local proof context is
`coord/changes/h6-roos-unit-comparison-api.md`; no existing statement or definition changes.

The result-type interface repair is recorded in
`coord/changes/h6-principal-intrinsic-result-types.md`; the item interface and imports
are recorded in `coord/changes/h6-roos-unit-comparison-api.md`.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
