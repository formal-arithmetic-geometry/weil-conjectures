## Worker report

The module `Sheaf.Paper.RadicialEtaleRationalUnitRetraction` states
`AlgebraicGeometry.ProEtale.radicial_etale_rational_unit_retraction`, with proof
`sorry`. It also constructs four canonical maps/comparisons belonging to this same
trace assertion; all four definitions have real data. No other theorem is postponed.
The source is the continuous internal-module extension explicitly written in the
node's eight-step proof, using Stacks 03SE (sum trace and degree), 09AB (pro-etale
topological invariance), and 015F (right derivation of an exact functor). Those local
source passages were opened. There is no claim that Stacks itself already states
the full continuous-coefficient generalization.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Distinct primes p and ell | `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)` |
| k is a field of characteristic p | `(k : Type u) [Field k] [CharP k p]` |
| Finite normed extension E/Q_ell, norm topology | `[NormedField E] [NormedAlgebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]`; the normed-algebra compatibility is exactly extension of the p-adic norm, whose unique finite-extension norm is the coefficient convention |
| Valuation ring O_E | Available from `Padic.coefficientExtensionIntegers`; neither an O_E-module nor invertibility of d in O_E occurs in this assertion |
| All three schemes separated finite type over k, maps over k | `W T S : Over (Spec (.of k))`, each with `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` structure map; `u₀ : W ⟶ T`, `e : T ⟶ S` |
| f = e after u | `u₀.left ≫ e.left`, definitionally the specified composite; no extra unrelated morphism or factorization assumption |
| u finite universal homeomorphism | `[IsFinite u₀.left]` and `(topologically IsHomeomorph).universally u₀.left` |
| e finite etale surjective, constant degree d >= 1 | `[IsFinite e.left] [Etale e.left] [Surjective e.left]`, `hd : 1 ≤ d`, `hdegree : ∀ s, e.left.fiberDegree s = d` |
| A_E,X = p_X^* C(-,E), all continuous functions | `condensedRingObj (normContinuousRing E).X X`; `normContinuousRing` is the recorded `continuousMapRingObjOfUniverse` with its canonical multiplication |
| Arbitrary internal modules, no lisse condition | Every `M` ranges over `Mod (Sheaf (Scheme.ProEt.topology S.left) Ab.{u+1}) (condensedRingObj ... S.left)` |
| Ordinary unbounded derived categories | The helpers use `moduleObjectDerivedPushforward`, `derivedUpperStarLowerStarAdjunction`, and `DerivedCategory.singleFunctor _ 0`; no bounded/constructible subcategory or replacement coefficient ring |
| Constructible and lisse terminology in the preamble | Recorded constructibility and lisse modules are publicly imported; neither property is assumed of M, as the node explicitly requires |
| u_*, e_*, f_* exact | `PreservesFiniteLimits` and `PreservesFiniteColimits` for all three functors; `hF` is the existentially concluded finite-colimit preservation of f_*, used by its canonical comparison |
| Identify u_*u^* e^*M with e^*M by the actual unit | `a : 𝟭 _ ≅ upperStar ... u₀.left ⋙ lowerStar ... u₀.left` with `a.hom = ...unit`; `rationalTraceRadicialComparison` uses `a.symm` and the existing composition isomorphisms |
| A_E,S-linear natural trace | `∃! t : upperStar ... f ⋙ lowerStar ... f ⟶ 𝟭 _`; components are module-category morphisms, hence linear; the natural transformation enforces naturality |
| Local splitting into d sheets | Etale `q : U ⟶ S.left`, `s : Fin d → (U ⟶ T.left)`, `hs : s j ≫ e.left = q`, and `IsColimit (Cofan.mk (pullback e.left q) ...)`; the cocone arrows are the actual lifts `(s j, 𝟙 U)` |
| Trace is the sum on the splitting | `map (t.app M) = map comparison.hom ≫ ∑ j, rationalTraceSheetProjection ...`; the projection is obtained from the actual e-adjunction counit and pullback composition, not an arbitrary product isomorphism |
| Unit is diagonal on the same splitting | For every sheet j, restricted unit followed by the radicial comparison and that sheet projection equals `𝟙 _` |
| t eta = d identity | `...unit.app M ≫ t.app M = d • 𝟙 M` (Lean categorical composition is left to right) |
| 1/d exists in E even when ell divides d | `(d : E) ≠ 0` is a conclusion; `(d : E)⁻¹` is used directly, with no primality-to-ell hypothesis |
| Canonical Rf_*(f^*M[0]) comparison | `rationalTraceDerivedComparison ... hF M` is exactly `singleFunctorCompRightDerivedFunctorIso`, specialized to the stipulated total right-derived pushforward |
| Actual derived unit agrees with eta[0] | `rationalTraceDerivedUnit` starts with the actual `derivedUpperStarLowerStarAdjunction.unit`; its postcomposition with the right comparison equals `singleFunctor.map ordinaryUnit`; the helper uses `singleFunctorCompLeftDerivedFunctorIso` to identify Lf^*(M[0]) with f^*M[0] |
| Normalized trace and ordinary retraction | `∃ r, r.hom = (t.app M).hom ≫ normContinuousScalar S.left (d : E)⁻¹ M` and `ordinaryUnit ≫ r = 𝟙 M`; this uses the existing actual constant-scalar action |
| Normalized derived retraction | `derivedUnit ≫ comparison.hom ≫ (singleFunctor _ 0).map r = 𝟙 _`; it displays the retract of the exact Rf_* object in the node |
| d = 1, inverse unit rather than field trace | In addition to the degree identity, `d = 1 → t.app M ≫ ordinaryUnit = 𝟙 _`; with d=1 the two composites are identity, including a nontrivial purely inseparable factor |

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, and its imported `Padic.coefficientExtensionAbsoluteValue` / `coefficientExtensionIntegers`; the latter are the spectral norm and its valuation ring. No finite coefficient reduction is substituted for E.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`: `CondensedRing.compactificationOverField` and the separated finite-type `Over` setting; no compactification is needed in this theorem's conclusion.
- `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingObjOfUniverse`, its MonObj and commutative structure.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`, `condensedRingObj`, and preservation of commutativity.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its morphisms and their action compatibility.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`, and the publicly imported actual `derivedUpperStarLowerStarAdjunction`.
- `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`, `constantModelBoundedConstructible`; these provide the preamble convention, with no constructibility premise added.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`; no lisse premise added.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`; `Mathlib.CategoryTheory.MorphismProperty.Limits`: `MorphismProperty.universally`, applied to `topologically IsHomeomorph`; `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`; `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Sheaf.Paper.NormContinuousMonodromyData`: `normContinuousRing`, `normContinuousScalar`. Its owning landed node `def-sfb-norm-continuous-monodromy-data` is added to stmt_deps to cite these exact constructions; no monodromy equivalence is assumed.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`: `Scheme.Hom.fiberDegree`, the field-dimension degree used by the recorded `IsFiniteLocallyFreeOfDegree`; its owning landed node `def-pc-finite-locally-free` is added to stmt_deps. No finite-locally-free hypothesis beyond the given finite etale condition is added.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`: `upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, `upperStarComp`, `lowerStarComp`.
- Exact derived comparisons: the published `Functor.singleFunctorCompRightDerivedFunctorIso` and `Functor.singleFunctorCompLeftDerivedFunctorIso`, with their full signatures read. Proof-dependency modules are imported as plain imports as required.

Edge cases checked before and after writing: d=0 is excluded exactly by `hd`;
d=1 includes the identity cover and purely inseparable maps; ell dividing d is
allowed (there is no invertibility premise on O_E); M=0 is allowed because M is
arbitrary, with no positive rank; empty S and its empty finite covers are allowed,
with the fibre-degree condition vacuous and all map identities on zero objects;
disconnected S and variable local module ranks require no connectedness premise.
An etale splitting is asserted for every actual coproduct splitting, without
assuming a preferred basis, indexing permutation, product isomorphism, or existence
of global sheets. Inverses use the actual radicial unit and canonical derived
comparisons. The helpers introduce no independent choices or hollow data.

Searches for an existing statement (all via the prescribed msearch and read-only rg):

- LeanFinder query: `Finite universal homeomorphism followed by finite etale cover normalized rational trace retracts adjunction unit for module sheaves`; 8 hits, all normalization-diagram geometry, no module trace/retraction statement.
- Loogle query: `CategoryTheory.Adjunction.unit, CategoryTheory.IsSplitMono`; 1 hit, `CategoryTheory.mem_essImage_of_unit_isSplitMono`, an abstract reflective-subcategory result, not this assertion.
- Mathlib grep query: `(trace|retraction).*(etale|proetale)|universalHomeomorph.*(Mod|module)`; 0 hits.
- LeanSearch query: `For finite etale covers of positive degree the rational module sheaf adjunction unit is split by the sum trace divided by the degree`; 8 hits including generic module adjunction units and algebraic normalized field trace, no pro-etale continuous-module trace theorem.
- Read-only searches of `lean/WeilConjectures` and `lean/Sheaf` for radicial/rational trace and retraction names found unrelated algebraic traces, geometric radicial statements, and the downstream `TamePairProperGenerators` proof plan; no existing statement of this item.
- Read-only blueprint-id search of `lean/WeilConjectures`, and declaration-name searches of both source roots and `dag/lean_names_upstream.json`, found no declarations with this item's id or the new helper/theorem names.

No statement correction, disputed statement, new notion node, or dependency-record
repair is needed. Only the item's Lean record and two added landed statement
dependencies change. Every existing hypothesis and clause is preserved.

Validation: the initial version compiled in both sandbox and final-module modes
through scompile.py; name resolution was repaired by explicitly selecting
`CondensedRing.upperStar`, `CondensedRing.lowerStar`, and its module adjunction
outside that namespace. The final version additionally spells out the sheetwise
diagonal identity and also compiled cleanly in sandbox and final-module modes. All lines are at most
100 characters; `autoImplicit` is false; every theorem proof is `sorry`.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
