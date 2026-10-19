## Worker report

The delivery states `AlgebraicGeometry.ProEtale.sp_reduction_tower_normalized` in
`Sheaf.Paper.SmoothPurityReductionTowerNormalized`. Its single postponed proof asserts
existence of `SpReductionTower`, the fully specified reduction construction together
with precisely the node's normalization and constructibility conclusions. There is no
statement correction, new DAG node, or dependency replacement. The stage-1 repair note
is resolved (stage 1); its required unchanged statement and expanded proof route are
retained. No assertion of proof completion is made.

Hypotheses and clauses, read against the node:

- The fixed prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. All integral rings
  are the recorded `Padic.coefficientExtensionIntegers l E`.
- `T : Scheme.{u}` is arbitrary for the construction and normalization. The existing
  small site has object universe u+1 and morphism universe u; coefficients and module
  sections lie in u+1. The common ambient universe contains both E and the scheme.
  No equality of site object and morphism universes is imposed.
- R_T is the actual pulled-back condensed integer ring. `spIntegralCondensed` aliases
  `sfbCondensedIntegers.X`; `spIntegralSectionRing` is its existing reconstructed
  section-ring sheaf, and `spIntegralModuleEquivalence` is exactly the recorded
  internal/sectionwise equivalence. `spIntegralInternalization` is its exact derived
  inverse. Thus the source is the ordinary unbounded D(R_T), without completeness,
  boundedness or constructibility imposed on its objects.
- `SpReductionTower.coefficient` identifies this same R_T with the existing completed
  integral ring. `coefficient_normalized` fixes its underlying section functions to
  `spIntegralAbComparison`, selected from the unique normalized comparison of
  `sfb_integral_coefficient_limit`. The selection includes that theorem's finite
  representation and cone; its uniqueness condition, not bare existence, fixes the
  comparison. `spIntegralEllProjection` is the commutative-ring lift of the projection
  through the uniquely constant-scalar-normalized `sp_completed_coefficient_limit`.
- The coefficient at n is exactly O_E/(ell)^(n+1); index zero means positive exponent
  one. `spIntegralReductionScalar` is the actual projection R_T -> R_(T,n+1), with
  commutativity retained. These are not uniformizer-power levels substituted silently.
- `ordinary`, `level`, and `transition` specify the strict degreewise tensor functor:
  the existing scalar-extension model at each level, with x tensor c sent to x tensor
  quotient(c) by every iterated transition. The local tensor generator is
  `systemModelTmul` (scalar-first convention), transported by `level.inv`. The
  transitions are the actual `D.equivalence` transitions, whose section and map
  normalization is part of the dependency's recorded interface.
- `red` has values in `spDerivedCoefficientTowers`, the ordinary derived category of
  the recorded abelian tower category, rather than only a functor-category of derived
  levels. `counit`, `universal`, and `computes` make it the left derived functor of
  the specified strict ordinary tensor construction, with its K-flat computation.
  `evaluation` identifies its level functors with the existing derived scalar models.
  These conditions determine the derived pair up to its counit-compatible isomorphism;
  they do not substitute an arbitrary functor or map for reduction.
- `normalized` is quantified over every source M and uses `IsSpNormalizedTower`,
  hence asserts invertibility of every actual canonical `D.reduction h`, including
  equal indices. It has no qcqs premise.
- Only `constructible` requires `CompactSpace T` and `QuasiSeparatedSpace T`, the
  recorded quasi-compact and quasi-separated scheme conditions. Its M premise is
  exactly `constantModelBoundedConstructible` after the canonical internal transport:
  bounded cohomology with the parent's finite-constant-model constructibility.
- Its first conclusion is `DerivedCategory.finiteTorAmplitude` for M, its second is
  the recorded `spNormalizedConstructibleTorTowers` predicate. This includes each
  level's finite Tor amplitude and constructibility in the precise finite-coefficient
  predicate `Scheme.IsConstructibleProEtaleModuleSheaf`, and uniform support and Tor
  intervals. The final universally quantified ordered a,b clause preserves *every*
  Tor interval of M: `Scheme.HasProEtaleTorAmplitude` at every positive level, and
  `IsZero` of every cohomology sheaf in degrees i<a or b<i.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`
  and its imported integral coefficient constructions.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`, `spEllIdeal`,
  `spCoefficientRings`, `sp_completed_coefficient_limit`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`: `SpCoefficientTowersAbelian`,
  `spCoefficientCommRings`, `spCoefficientEvaluation`, and its `scalar`, `reduction`,
  `equivalence`, `hasDerived` interfaces.
- `Sheaf.Paper.CondensedConstantConstructibility`: `constantModelBoundedConstructible`;
  `Sheaf.Paper.ConstantModelTorAmplitude` and
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`: the existing
  `DerivedCategory.finiteTorAmplitude` and `DerivedCategory.torAmplitudeIn` predicates.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spDerivedCoefficientTowers`,
  `spDerivedCoefficientEvaluation`, `IsSpNormalizedTower`,
  `spNormalizedConstructibleTorTowers`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparatedSpace` as
  the quasi-separated-scheme condition equivalent to `QuasiSeparated` of the terminal map.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`: `Scheme.IsConstructibleProEtaleModuleSheaf`
  through the normalized-tower predicate;
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`: `Scheme.HasProEtaleTorAmplitude`.
- The existing foundational comparison
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionRingSheaf`, `sectionModuleEquivalence`. Its
  current published source was read through `scompile.py --source`, because the local
  shared source does not contain that file. It leaves underlying sections unchanged.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`: `sfbCondensedIntegers`,
  `sfbCompletedIntegersAb`, `sfb_integral_coefficient_limit`, imported by coefficient
  towers. The continuous-map commutativity is the existing
  `Profinite.isCommMonObj_continuousMapRingObjOfUniverse`.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`: `systemModelTmul` and the existing
  normalized scalar model; `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  its ordinary/derived universal pairs. These are already public dependencies of D.

Available stated proof dependencies are imported privately, preserving the stage-3
proof plan. The unrecorded `det-def-localizing-closure-ctf-equals-bc` has no import yet;
its role is explicitly recorded in proof step 4. Mathlib proof leaves are already in
the imports' closure. The declaration docstring follows all eight node proof steps,
including the one-factor K-flat argument and the common global stratification.

Edge cases checked: empty T uses the allowed positive one-empty-stratum partition;
M=0 has zero reductions; the first positive level is n=0; m=n is included and is the
canonical tensor unitor; all m<=n are covered, not just consecutive levels; no
flatness of R_T -> R_(T,n+1) is assumed. Ramified E and torsion modules are included,
with the two-term DVR resolution accounting for the degree -1 term. Arbitrary
unbounded M are allowed before the separate qcqs bounded-constructibility implication.

Searches made:

- `msearch.py ... leanfinder`: "Derived reduction of a complex of integral coefficient
  sheaves gives a normalized coefficient tower, preserving constructibility and Tor
  amplitude" returned eight generic derived-category/t-structure results; no match.
- `msearch.py ... leansearch`: "Derived reduction of complexes of sheaves gives normalized
  inverse systems preserving constructibility and Tor amplitude" returned generic
  `DerivedCategory`, its localization and exact derived functors; no reduction theorem.
- `msearch.py ... loogle 'DerivedCategory, tensor'`: no hit (tensor unknown as a queried
  identifier). The existing scalar-model declarations were found and read directly.
- `msearch.py ... grep 'reduction.?tower|normalized.?tower'`: zero Mathlib hits.
- Direct `rg` of Mathlib for normalized/reduction towers: no match. Direct source
  search in WeilConjectures for the blueprint id: no match. Searches in `lean/Sheaf`
  found `IntegralReductionTowerCanonical` (inverse systems in a fixed coefficient
  derived category), `AdicCoefficientDatum` and the normalized-tower predicates.
  None asserts the present strict D(Tow) functor with this node's constructible/Tor
  conclusions. They were read to avoid redefining the scalar or tower notions.
- The chosen new declaration names were searched in WeilConjectures and lean/Sheaf;
  no existing declaration matches them.

## Second reading by Q19

This is the author's second reading; the dispatcher forbids starting other agents,
and the maintainer supplies the independent delivery review. I reopened the node,
its resolved stage-1 repair note, the blueprint reduction paragraph and the generated
Lean file. I checked the clauses field by field as above. In particular normalization
is unconditional in T, qcqs occurs only in the constructibility implication, the
source is unbounded, the strict transitions are fixed on tensor generators, and both
finite-level Tor amplitude and support preserve every ordered Tor interval. The
coefficient comparison is fixed to the published normalized comparison rather than
an arbitrary isomorphism. No statement mismatch or disputed mathematical assertion
was found. The first compiler pass identified a hidden commutativity instance; the
existing continuous-map instance and explicit reconstruction universes repair it.

Validation: `scompile.py Q19 det-sp-reduction-tower-normalized` accepted the complete
module with no errors or unexpected warnings, both as sandbox and final library
module (53.4 s and 34.3 s, respectively; unchanged 60 s limits). Factoring the long
conditions into named definitions removed the combined structure's kernel timeout.
The helper definitions retain the exact original formulas. Only the node's `lean`
field differs from the repository node; there are no dependency-node changes.

## Returned delivery repair (2026-10-18)

The returned immutable head `99f851370127` timed out in the 60-second sandbox
compile. The retained packet first passed a dry run (`3698d1b42b`), but its push
check reproduced the timeout and server confirmation also failed. Profiling in a
scratch copy located the cost in the kernel check of `IsSpReductionTransition`:
42.0 and 49.6 seconds, with structure checking waiting on that declaration.

The repair names two actual section functions. `spReductionGenerator` is the
existing scalar-first `systemModelTmul` transported by `(level n).inv.app M`,
with its section target written explicitly. Factoring that generator alone did
not reliably prevent the timeout: an isolated profile still measured 43--48
seconds in the transition predicate, whereas the generator itself checked quickly.
`spStrictTransitionSection` therefore abstracts the actual strict transition's
underlying section function over its coefficient ring tower B. Restriction of
scalars leaves its additive sections unchanged. Naming that function before
specializing B avoids repeatedly unfolding the concrete constant quotient-ring
construction when checking the transition equation's types.

`IsSpReductionTransition` now uses these two functions in exactly the original
equation. Unfolding them recovers the previous formula, with every m ≤ n, U, c
and x unchanged. This introduces no postponed theorem or additional hypothesis.
Both helpers are recorded in `lean.declarations`; only `lean` changes in the node.

Self-check: reopened the current node and its dependency records, the blueprint
reduction paragraph, the source module and the normalized-tower definitions.
The coefficient projection and quotient formula remain the canonical ones,
normalization remains unconditional, and qcqs bounds remain confined to the
constructibility implication. The theorem signature and all edge cases in the
worker report are unchanged. `scompile.py` accepted the repaired complete module
in both sandbox and final module forms, with no errors or unexpected warnings
(reported times 31.5 and 19.6 seconds, unchanged 60-second limits). Development
profiling is confined to `scratchpad/` and is absent from the delivered module.
