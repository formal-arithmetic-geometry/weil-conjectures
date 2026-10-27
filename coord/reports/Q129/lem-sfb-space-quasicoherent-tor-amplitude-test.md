## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQuasiCoherentTorAmplitudeTest` states
`AlgebraicGeometry.AlgebraicSpace.torAmplitude_iff_quasiCoherent_lower_tests`.
Its only new declaration is a theorem with proof `sorry`. No definition is copied
or introduced. The module docstring and theorem docstring name Tags 08IL and 08IS;
the theorem docstring gives the seven steps of the accepted DAG proof.

Source checked: `literature/stacks-project/spaces-perfect.tex`,
`lemma-tor-qc-qs` (Tag 08IL), both statement and proof. Its full-interval
quasi-coherent criterion specializes to the node by the upper tensor bound from
its cohomological bound at c. The bound is justified by good truncation and a
bound-preserving bounded-above flat resolution, exactly as the node's step 1.
No statement correction or mathematical dispute is needed.

Clause-by-clause rendering:

| Node clause/hypothesis | Lean rendering |
| --- | --- |
| Work in the chosen size convention | Explicit `universe u w`, `Scheme.{u}`, and `[HasDerivedCategory.{w} Y.SmallModules]`; no auto-bound implicit variables. |
| S is a scheme | `{S : Scheme.{u}}`. |
| Y is an algebraic space over S with its small étale structure sheaf | `(Y : AlgebraicSpace S)` and its existing `smallStructureSheaf` on `smallEtaleModelTopology`. |
| Module sheaves and unbounded D(O_Y) | `Y.SmallModules`, `Y.DerivedModules`; these are the recorded equivalent small affine model, with the original coefficient and section universe u. |
| Canonical module functors | Public import of `AlgebraicSpaceModuleOperations`; they are used by the proof dependencies, with no additional map or functor argument. |
| K-flat derived tensor with flat terms | `SheafOfModules.siteDerivedTensorIndependentCoefficients.{u,u,u,w}` applied to the recorded topology and commutative structure sheaf. Its existing descent specification defines its resolving class by K-flatness and flatness of every term. |
| K-injective direct images | Existing `derivedDirectImage` in the public derived-calculus interface; no direct image occurs in the conclusion, and no arbitrary direct image is introduced. |
| Y is quasi-separated, without a condition on S | `(hY : IsAbsolutelyQuasiSeparated Y)`, the existing absolute affine-pair/diagonal criterion, not a relative quasi-separatedness hypothesis. |
| K belongs to D(O_Y) | `(K : Y.DerivedModules)`. |
| K has quasi-coherent cohomology | `(hK : Y.derivedQCohProperty K)`; this transports each cohomology sheaf back along the specified module equivalence and tests Mathlib's `IsQuasicoherent`. |
| Integer c and H^i(K)=0 for i>c | `(c : ℤ)` and `hupper : ∀ i : ℤ, c < i → IsZero ((DerivedCategory.homologyFunctor Y.SmallModules i).obj K)`. |
| Any integer a≤c | `(a : ℤ) (hac : a ≤ c)`. |
| Conditions (1) and (2) are equivalent | The outer `↔`. |
| (1) every module G | `∀ (G : Y.SmallModules)`, with no quasi-coherence restriction or additional hypothesis. |
| G in degree zero | `(DerivedCategory.singleFunctor Y.SmallModules 0).obj G`. |
| (1) all degrees outside [a,c] | `∀ i : ℤ, i < a ∨ c < i → IsZero (H^i (K tensor^L G[0]))`, expanded in the signature using `homologyFunctor` and the recorded tensor. |
| (2) every quasi-coherent module F | `∀ (F : Y.SmallModules), ((Y.smallModuleEquivalence.inverse).obj F).IsQuasicoherent → ...`. |
| (2) all degrees i<a, with F in degree zero | `∀ i : ℤ, i < a → IsZero (H^i (K tensor^L F[0]))`, with the same expanded tensor and `singleFunctor`. |

The model does not restrict the test objects. The specified equivalence
`Y.smallModuleEquivalence : Y.Modules ≌ Y.SmallModules` takes every original
module sheaf to this category and every small-model module back to an original
one. Quasi-coherence is explicitly tested after that inverse. Exact equivalences
preserve cohomology, zero objects and the specified K-flat tensor construction.
The theorem is the full derived-tensor statement; it does not replace an
isomorphism assertion with per-degree isomorphisms.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `structureSheaf`, `Modules`; these give the actual
  fppf algebraic spaces and small étale regular-function structure sheaf.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent specialization of Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`; `DerivedCategory.homologyFunctor` and `singleFunctor` are
  supplied by the public derived-calculus imports.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, the slice sheafification instances,
  and the unchanged Mathlib predicate `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`, with the chart-limit and tensor-unit normalization.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallModules`, `smallStructureSheaf`, `smallEtaleModelTopology`,
  `smallModuleEquivalence`, with the actual affine-chart restriction functor.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`:
  `DerivedModules`, `derivedQCohProperty`, `derivedDirectImage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients` and its
  `SiteDerivedTensorDescentSpec`, including flat-term K-flat representatives.

The last four interfaces are already landed nodes, added to `stmt_deps` under
brief §5's permission to cite existing landed interfaces. No other field changes
except `lean`. There are no new nodes or dependency repairs.

All recorded proof dependencies with usable declarations are imported privately:
`KFlatResolutionIndependentCoefficients`, `FunctorialBoundedAboveClassResolution`,
`BoundedAboveFlatSheafKFlat`, `AlgebraicSpaceQuasiCoherentPushforward`,
`SpaceDerivedEtaleChartCalculus`, `RingedTopoiCanonicalTensorPullbackOfUniverses`,
`SpaceEtalePullPushRetract`, `DerivedEtaleZariskiEquivalence`, and upstream
`TorAmplitudeQCohTest`. Mathlib `AffineScheme` supplies the affine qcqs and
basis inputs. The proof-only nodes `lem-sfb-space-affine-source-qc-separated`
and `lem-sfb-etale-tor-dimension-descent` currently have no Lean module recorded,
so there is no module to import for them. Their steps remain in the docstring;
they are not missing notions required to type this statement.

Edge cases checked before writing: a=c (singleton interval), negative a and c,
zero K and zero test modules, the empty algebraic space (all module cohomology
zero), non-quasi-compact Y, non-quasi-separated S, and arbitrary localization
morphism universe w. No hypothesis excludes these cases. Without `hupper` the
one-sided test would fail for a complex concentrated above c, so it is explicitly
retained. Both bounds use strict inequalities, so degree a and degree c are
retained in the amplitude interval. No tests are restricted to coherent,
finite-type, flat or degreewise finite modules.

Searches performed through the required `msearch.py` wrapper (2026-10-24):

- LeanFinder: “On a quasi-separated algebraic space a bounded above complex with
  quasi-coherent cohomology has Tor amplitude in an interval if tensoring with
  every quasi-coherent module vanishes below its lower endpoint”. Eight hits,
  including `DerivedCategory.isGE_iff`, `isLE_iff`, and bounded representative
  lemmas; no algebraic-space quasi-coherent Tor test.
- Loogle: `HasTorAmplitude, torAmplitudeIn, IsQuasicoherent`. Zero hits;
  unknown identifier `HasTorAmplitude`.
- Mathlib grep: `torAmplitude|TorAmplitude|tor_amplitude` in AlgebraicGeometry.
  Zero hits.
- Direct project/upstream `rg`: searches for quasi-coherent Tor tests,
  `IsQuasiSeparated`, `HasTorAmplitude`, `derivedQCohProperty`, the existing
  tensor declaration, and the assigned blueprint id. Upstream
  `AlgebraicGeometry.torAmplitude_of_quasiCoherent_tests` is for schemes on the
  Zariski site only, not algebraic spaces; read its full statement and docstring.
  `SpacePerfectUniformTor` states existence of a finite interval for perfect K,
  not this equivalence. The small model, derived calculus, tensor descent and
  absolute quasi-separatedness already exist and were reused.

Validation: the required `scompile.py Q129` invocation compiled both its sandbox
probe and the actual module on the server, cleanly (26.7 s and 25.9 s respectively).
No diagnostic declarations remain.

## Second reading by Q129

A second in-session reading checked the original node and the complete final
signature against the source and the clause table above. This is a self-check;
no additional agent was started, as instructed by the dispatcher. The maintainer's
independent review remains the independent reading of this delivery.

Checked that the main quantifier is all modules, the right quantifier is exactly
quasi-coherent modules transported to the original site, the upper vanishing
hypothesis is on K itself, and a≤c is explicit. The right side tests only i<a;
the left tests both complementary degree ranges. Checked that the quasi-separated
predicate is absolute and adds no quasi-compactness or separation of the base.
No mismatch was found and no source statement was corrected. The four extra
statement dependencies only record already-existing interfaces used by the file.
