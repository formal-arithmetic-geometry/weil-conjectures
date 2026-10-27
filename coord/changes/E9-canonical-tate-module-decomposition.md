# Canonical Tate comparison module decomposition

## Reason

After proving the integral product and pullback-unit clauses, the original file
still exceeded the 60-second compilation limit. Profiling identified repeated
Roos completeness checking and expansion of completed and common-stage comparison
data. Local opacity, canonical derived-instance priorities, reuse of the proved
orientation tensor helpers, and a shared private completeness lemma reduced the
cost, but the whole file still took 60.3 seconds in one profiled run and 111 seconds
in the final run. Split its existing declarations into separate complex, completed, scalar and
common-stage constructor modules, with reduction squares in the original module.

## Old

All declarations were defined in `Sheaf.Paper.CanonicalTateComparisons`, with the
following public imports, retained verbatim in that module:

```lean
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.Paper.CartesianCoefficientTwists
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.OrientationIntegralCoefficientTwists
public import Sheaf.Paper.IntegralTwistBaseChange
public import Sheaf.Paper.SignedTwistReductionComparison
```

Every existing declaration signature and every public definition body of the item
is unchanged. The consumer equality-proof elaboration change is documented below.
The two formerly missing theorem proofs and the private completeness refactor are
the only changes to existing declaration bodies.

## New

The original module additionally re-exports:

```lean
public import Sheaf.Paper.CanonicalTateCommonComparisons
```

`CanonicalTateCommonComparisons` publicly imports
`CanonicalTateScalarComparisons`, which publicly imports `CanonicalTateCompletedComparisons`,
which publicly imports `CanonicalTateComplexComparisons`. The complex module retains
all seven original public imports. The original declaration names and namespaces
remain exactly the same: complex/flatness declarations occur in the complex module,
completed operation comparisons in the completed module, realization and scalar
comparisons in the scalar module, and common-stage declarations in the common-stage module, and reduction-square
declarations in the original module. Four matching constructor nodes carry the relocated declarations;
the original node now assembles these dependencies. Four original mathematical
holes remain in the support modules, all relocated, and no new hole or theorem statement is added.

## Users

All users retain the same names, types, public definitions and exported imports.
The two direct importers receive only local elaboration settings after their
original sources finish without type errors but exceed the 60-second limit.
Their signatures, imports, attributes visible to other modules, and theorem proof
bodies are unchanged. One rational consumer definition now supplies the finite
stage explicitly in its equality proof; its eqToIso value is unchanged. Both are unclaimed at the time of adaptation. The table includes textual downstream users of the relocated
names, including consumers that only mention a name in a comment.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Local priorities/opacity and compilation split; same declarations and proof bodies. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Local priorities/opacity, explicit equality-proof stage and compilation split; same declarations and comparison data. |

The consumer local context changes are:

```lean
-- CanonicalTateArrowNaturality: added after open FrobeniusCoefficientTwists.
attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] HasDerivedCategory.standard
  integralPull finitePull rationalPull commonPull
  integralProduct finiteProduct rationalProduct commonProduct
  proEtaleRingModulePullback proEtaleRingModuleAdjunction
```

```lean
-- RationalPurityTraceCoherence: replace the old priority declaration.
-- Old:
attribute [local instance 3000] integralTowerHasDerivedCategory
-- New:
attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
```

The original naturality consumer takes 70 seconds (66 seconds when profiled),
with 13 seconds of typeclass search and repeated checking of concrete comparison
data. Its adaptation takes 41.1 seconds. The original rational purity consumer
takes 81.2 seconds; prioritizing the same standard derived-category instance
aliases brings the profiled run to 52.4 seconds. That improvement was insufficient in the final unprofiled run (79.9 seconds),
so the common-stage definition was profiled and repaired as below. Profiling
options are removed from delivered sources. All selected instances define the same standard derived
localizations, and the opacity attributes are local to the consumer file.

The largest common-stage elaboration was `commonPullInclusion` (8.78 seconds in
the labeled profile). Move the existing local irreducibility attribute for
`commonStageDerivedPullback` to the start of `CommonSources`, before that definition.
Its equality proof now explicitly unfolds that wrapper and supplies the literal
stage pair, avoiding inference through the full functor implementation.

Original consumer definition, verbatim:

```lean
def commonPullInclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (i : Index l Ω) (K : Stage l Ω Y i) :
    (commonStageDerivedPullback l Ω f).obj ⟨i,K⟩ ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion i).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω i) f).obj K) :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _)
```

Delivered consumer definition, verbatim:

```lean
def commonPullInclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (i : Index l Ω) (K : Stage l Ω Y i) :
    (commonStageDerivedPullback l Ω f).obj ⟨i,K⟩ ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion i).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω i) f).obj K) :=
  by
    unfold commonStageDerivedPullback
    exact eqToIso
      ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 ⟨i, K⟩)
```

The endpoints and eqToIso constructor are identical. Equality proofs are proof
irrelevant, so making its input stage explicit preserves the same comparison
object definitionally. No data or choice is replaced. This consumer has no direct
Lean importers (checked by rg over both library roots); its DAG meaning and target
statements are unchanged.

The optimized full rational consumer still took 92.3 seconds, so its existing
constructors are subdivided into two supporting modules:

```lean
-- RationalPurityTraceCoherence additionally re-exports:
public import Sheaf.SecSmoothPurity.RationalPurityCommonComparisons
-- The common module re-exports:
public import Sheaf.SecSmoothPurity.RationalPurityLineComparisons
```

The line module retains the five original public imports and all original
line/source declarations, with no holes. The common module retains the original
rational/common support and source composition constructors and composition clauses,
including the unchanged commonSupportComposition_existsUnique hole. The original
consumer retains all trace, base-change and coherence declarations and its original
main-theorem hole. No declaration is renamed or weakened; the original public
imports stay verbatim in the consumer. Private proof imports follow their users.
The original consumer node keeps its statement and complete original proof route,
updates its declaration list, and cites the two new compilation nodes. This is a
file subdivision, not a new mathematical decomposition or added hole.

The first delivery attempt pushed nothing: the repeated naturality consumer compile
took 62 seconds despite its earlier 41.1-second accepted run. After the canonical
instance and opacity optimizations, subdivide its existing constructors as follows:

```lean
-- CanonicalTateArrowNaturality additionally re-exports:
public import Sheaf.Paper.CanonicalTateScalarNaturality
-- The scalar constructor module re-exports:
public import Sheaf.Paper.CanonicalTateOrdinaryNaturality
-- The ordinary constructor module re-exports:
public import Sheaf.Paper.CanonicalTateNaturalityLaws
```

The law module retains the nine original public imports. The original consumer also
keeps those nine imports verbatim. All predicates, ordinary/complex comparisons,
scalar comparisons, root-system laws and theorem proofs retain their original
names, signatures and bodies. The original module keeps the all-stage assembly,
geometric setting, original core hole, parity proof and final theorem. The private
conjugation helper is reused by the scalar proof via `import all` of the ordinary
module. The original local essentially-small instance context is retained in the
scalar and final modules. The private CochainCoefficientArrows import follows the
ordinary and scalar comparison proofs. No mathematical statement or hole is added.
The naturality node's declaration list and proof dependencies, and the core node's
constructor dependencies, record these locations. No unit or node statement changes.
There are no direct Lean importers of the naturality consumer (checked across both
roots), so no further consumer adaptation is required.

The second delivery attempt also pushed nothing: the combined common-stage and
ordinary reduction-square item file took 63 seconds. Separate its existing common
constructors into `Sheaf.Paper.CanonicalTateCommonComparisons`, which publicly
imports `CanonicalTateScalarComparisons`. The original item now publicly re-exports
`CanonicalTateCommonComparisons` and retains its original seven public imports.
It contains only the original ordinary reduction-square constructions, with no
local hole. The common-product hole moves unchanged to the common-stage module.
Every original signature and public definition body stays verbatim. The item's
node attaches its remaining reductionSquare constructor and cites the new common
constructor node; the original overall node statement and unit route are unchanged.

After separating the common-stage constructors, the reduction file was still just
over 60 seconds. Its final proof context additionally uses:

```lean
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
private local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
```

These keep the chosen module adjunction data abstract and select the existing
Mathlib site-smallness proof. Existing declaration signatures, public definition
bodies and theorem proof bodies are unchanged. A profiled run compiled in 34.4
seconds; profiling commands are removed from the delivered file.

## Status

landed 20261027T021317-L-2756189 2026-10-27 (merge of deliver/E9/Sheaf.Paper.CanonicalTateComparisons)

## Reviewer correction (cc review, 2026-10-27)

Statement-level citations follow the relocated declarations. Each node below uses,
in a statement or a definition body, declarations now owned by a new node of this
delivery; that new node is added to its `stmt_deps` (proof_deps unchanged):

- `def-pur-canonical-tate-comparisons`: + the complex, completed, scalar and common
  comparison nodes (its definitions use `integralComplex`, `integralGood`,
  `finiteRealization`; the node's statement defines all five comparison families,
  so citers of this node reach the relocated owners through it).
- `def-pur-canonical-tate-naturality-laws`: + complex, completed, scalar, common
  comparison nodes (`coefficientLaws` and the stage laws use `integralPull`,
  `rationalPull`, `commonPull`, the products, squares and scalar lines).
- `def-pur-canonical-tate-ordinary-naturality`: + complex comparisons
  (`integralComplex`, `integralProductComplex`).
- `def-pur-canonical-tate-scalar-naturality`: + `def-pur-canonical-tate-comparisons`
  (`ordinaryReductionSquare`).
- `lem-pur-canonical-tate-arrow-naturality-core`: + naturality-laws, scalar-naturality
  (`coefficientLaws`, `strictCoefficientLaws` in its statement).
- `lem-pur-canonical-tate-arrow-naturality`: + naturality-laws, ordinary-naturality,
  scalar-naturality (`allStageLaws`, `geometricTateLaws`).
- `prop-pur-rational-purity-trace-coherence`: + the line and common comparison nodes
  (`rationalSourceBaseChange`, `RationalCompositionClause`, `CommonCompositionClause`,
  `commonSourceBaseChange`).

The unused proof import `import all Mathlib.CategoryTheory.Limits.HasLimits` is
removed from `Sheaf.Paper.CanonicalTateComplexComparisons` (the module compiles
without it; `import all` is not seen by its importers).
