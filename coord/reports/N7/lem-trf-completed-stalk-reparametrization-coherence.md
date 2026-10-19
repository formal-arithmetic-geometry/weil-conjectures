## Worker report

The module `Sheaf.Paper.CompletedStalkReparametrizationCoherence` states
`WeilConjectures.CompletedStalk.coherence`. The node statement is unchanged.
Its conclusion supplies a simultaneously specified integral comparison system, the
integral equations, and the corresponding raw rational equations. All theorem
proofs are `sorry`. Every definition has actual data; choices of maps occur only
from existence-and-uniqueness theorems fixing those maps, or from the dependency's
already specified equivalence/universal property.

The following names are in namespace `WeilConjectures.CompletedStalk`.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed finite-field datum, algebraic closure k, coefficient prime distinct from p | `D : FiniteFieldDatum.{u}`, `l : ℕ`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]`. `D.k` is the recorded algebraic closure. `pointUnits` derives invertibility on s; it is not an additional assumption. |
| Finite extension E/Q_l, O_E, uniformizer, all positive quotient levels | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`; the existing `Padic.coefficientExtensionIntegers`, uniformizer, and `unrestrictedIntegralFiniteComplex` are used. Tower index n represents the positive exponent n+1. |
| Arbitrary schemes Z -> Y -> X, with l invertible | Universally quantified `Scheme.{u}`, `f : Y ⟶ X`, `h : Z ⟶ Y`, and instances `∀ x, Invertible (l : X.residueField x)`, similarly for Y and Z. No finite-type, separatedness, or map to the finite-field base is imposed on these arbitrary schemes. |
| Small pro-etale sites | All completed module categories, finite reductions, and pullbacks use the dependency's `Scheme.ProEt`, object universe u+1 and morphism universe u. No equality of those two universes is assumed. |
| Integral D^b_c and raw rationalization | `sfIntegralConstructibleCategory l E X` and `sfRationalConstructibleCategory l E X`; no Karoubi completion or perfectness/Tor-amplitude restriction. |
| Geometric points v:s -> T | Binders `v : Spec (.of D.k) ⟶ X`; `pointFibreBaseIsAlgClosed` supplies the existing algebraically closed field instance. |
| J_v = Fib_s Lv* | `integralFibre` is the recorded ambient pullback followed by `pointFibreIntegralAmbient`, restricted to the actual integral full subcategory. This is exactly `constructibleIntegralPullback ⋙ pointIntegralFibre` followed by the faithful inclusion of its point target. `rationalFibre` is the actual `rationalDerivedPullback ⋙ pointRationalFibre`, followed by that target's full inclusion and the recorded fully faithful module-size lift. |
| c is the specified composition comparison | `comparison` is literally `(pointFibreIntegralAmbient D l E).mapIso (integralComparisonComposition l E C v f M).symm`. Thus it uses the entire-system counit normalization of the recorded dependency, not an arbitrary compositor. |
| r has finite germ rule [U,u,a] -> [U,u delta,a] | `germSection` is the pullback-unit section restricted along the pointed lift. `towerReparam_existsUnique` specifies its image as the same section at `proEtaleStalkNeighbourhoodReparam v α`. Through the finite pullback-stalk comparison these are exactly the node's two germs. The equation quantifies every P, level, degree, neighbourhood, and section. |
| Integral construction is a map of simultaneous strict reduction diagrams | `towerReparam` is a natural isomorphism with values in the category of entire strict towers of complexes. Transition compatibility is part of its type. `reparam_existsUnique` equates its `integralOperationsRoosMap` with r after the canonical `realization`, for every good representative P and every Q(P) ≅ K. |
| Maps are specified on the whole cone, not detected by reductions | `sectionsRoos_existsUnique` prescribes BOTH `roosFirst` and `roosSecond` in every degree and every product coordinate. `realization` uses that unique comparison. `integralOperationsRoosMap` is the dependency's diagonal product map on both shifted-cone summands. No faithfulness of individual reductions is asserted or used. |
| Naturality in arbitrary integral morphisms | c: `IntegralCoherent.naturality`; r: the type `integralFibre ... ≅ integralFibre ...` returned by `reparam_existsUnique`, a natural isomorphism on the complete derived full subcategory. The normalization runs over every representative, not just a fixed resolution or chain-map presentation. |
| Composition equation for c | `IntegralCoherent.composition`; its first RHS factor is exactly the fibre of `integralComparisonComposition ... h f M`, followed by the two c factors in the node's order. |
| Identity c | `IntegralCoherent.identity`, expressed against the specified `integralComparisonUnit` under J_v. |
| Mixed c/r equation | `IntegralCoherent.mixed`. |
| Source automorphism composition and identity | `IntegralCoherent.reparamComposition`, with `α.trans β` (beta after alpha), and `reparamIdentity`. `sourceIso` has hom definitionally `Spec.map (CommRingCat.ofHom α.toRingHom)`. |
| The specified j, including insertion and kappa | `sectionRestriction_existsUnique` fixes restriction on every section in the dependency's canonical sectionwise inverse-image model. `derivedSectionRestriction` descends it through exact localization. `sectionMap` then composes with `inverseImagePullbackComparisonDerived`, retaining its actual chosen-resolution, zero-shifted-coordinate map. |
| Identity-point comparison and c_delta,id j = r_id,alpha | `identityFibre` is Fib of the specified completed pullback unit; `IntegralCoherent.sections` inserts its inverses on the two occurrences of J_id and states precisely the displayed equality of the specified maps. |
| Rational constructions are images of integral ones | `fieldTensor`, `rationalPointNormalization`, `rationalUnderlyingPullback`, and `rationalNormalization` use the recorded scalar extension, object equality, and size-descent counit. `rationalComparison_existsUnique` and `rationalReparam_existsUnique` fix every component to the transported image of the corresponding integral component. |
| All rational equations and arbitrary rational morphisms | `RationalCoherent.composition`, `identity`, `mixed`, `reparamComposition`, `reparamIdentity`, `sections`. The chosen c and r are natural isomorphisms on the raw rational categories, so naturality covers nonintegral pure tensors and their finite sums. `rationalCompositor` and `rationalUnit` are explicitly images of the same integral comparisons. `rationalSectionMap` is the image of the specified integral j. |
| Lambda-linearity | Every component is a morphism in the derived category of coefficient modules, so it is coefficient-linear. The coefficient/module lifts transport exactly the same scalar actions. No arbitrary underlying additive map is substituted. |
| Any finite succession, compatible with v | The universally quantified binary action and unit equations imply the finite-succession assertion by induction, including the empty succession. Combining the mixed and sections equations gives its compatibility with every v. This is stated in the main theorem's proof docstring. |
| No Weil datum, periodic point, or endomorphism | There is no such binder or structure anywhere in the statement. |

Heterogeneous equalities (`HEq`) in the coherence structures account only for the
ordinary equality of scheme maps under associativity, identity composition, and
contravariance of Spec on composed ring maps. They compare the specified actual
morphisms. They do not replace an equation by an existence statement or by agreement
of separate reductions. In particular alpha followed by beta on germs gives
`Spec beta ≫ Spec alpha ≫ v`, the same point as `Spec (beta ∘ alpha) ≫ v`.

Dependency declarations used (all read in their source, including signatures and
docstrings):

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`; the module's global datum
  and finite extension conventions are rendered by their underlying `FiniteFieldDatum`
  and finite coefficient extension binders, rather than requiring an unrelated X₀.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.mk`, `ProEt.forget`, and its topology.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory` (derived completeness, every constructible
  reduction, and one uniform finite cohomological interval).
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, with unchanged integral objects.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: publicly retains
  `integralDerivedPullback`, `integralDerivedPullbackComparison`, and the global
  strict-tower operations. The item's schemes use that global interface.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, `IntegralComparisonRealizationCoherence`,
  `integralComparisonComposition`, `integralComparisonUnit`. The main theorem
  supplies C with that dependency's normalized realization coherence.
- Geometric points: the recorded `IsAlgClosed` convention and `Spec (.of D.k) ⟶ X`;
  no alternative point notion is defined.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFibreIntegralAmbient`,
  `pointIntegralFibre`, `pointRationalFibre`, `pointRationalFibreObjIso`,
  `pointFibreModuleLift`, `pointFibreSizeLift`, `pointFibreRationalLarge`,
  `pointFibreSizeLift_equivalence`; the rational counit normalization is the one
  used in that recorded module, without inventing another rational fibre.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`: the module-stalk functors,
  publicly used by the finite coherence module. `ProEtaleGeometricNeighbourhood`
  is the recorded pointed-neighbourhood category, not a private copy.
- `Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence`:
  `proEtaleStalkNeighbourhoodReparam`, the normalized finite
  `proEtalePullbackStalkComparison` and `proEtaleStalkReparam` used in the
  `towerReparam_existsUnique` proof plan.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived`, with the
  dependency's sectionwise `inverseImageIntegralModules` and `inverseImageIntegralDerived`.
- Existing operational interfaces used without duplication:
  `constructibleIntegralPullback`, `rationalDerivedPullback`,
  `rationalDerivedPullback_existsUnique`, `integralOperationsPullbackTowerFunctor`,
  `integralOperationsGoodComplex`, `integralOperationsRoosMap`,
  `unrestrictedIntegralFiniteComplex`, `integralOperationsPullbackGenerator`.

Every stated proof dependency with an available declaration is imported, directly
or publicly by the statement dependencies. The proof-only normalization node
`lem-weil-isomorphism-derived-pullback-comparison-normalization` has no recorded
module; it is mentioned in the complete copied proof plan and is not needed as
an object for stating this item. No duplicate statement for it is introduced.

Edge cases checked before and during the second reading: f = id, h = id,
alpha = 1; two noncommuting source automorphisms (the order is beta after alpha,
not alpha after beta); the zero coefficient object; empty scheme targets (there
are no geometric point binders to instantiate); the first positive quotient
(index zero means exponent one); and complexes with unbounded K-flat terms and
no finite Tor amplitude. The good-complex quantifier has no bounded-term
hypothesis. Rational arrows include arbitrary sums of pure tensors. The point's
small-Hom derived localization is explicitly the same shrinking construction as
in the recorded fibre, rather than the unrelated larger standard localization.

Searches for an existing statement:

- `msearch.py ... leanfinder "Completed proetale geometric stalk functor comparison for pullback and source field automorphism coherent with composition"`:
  eight ordinary scheme/structure-sheaf stalk composition hits; none about the
  completed integral or raw rational coefficient tower comparison.
- `msearch.py ... loogle '"sheafFiberComapIso"'`: three hits in
  `Mathlib.CategoryTheory.Sites.Point.Comap`; read the canonical ordinary sheaf
  fibre comparison. It does not supply the integral quotient-cone normalization
  or source action and section equation here.
- `msearch.py ... grep 'sheafFiberComapIso|stalkPullbackIso' CategoryTheory`:
  one generic site-point comparison hit, no completed comparison.
- `msearch.py ... leansearch "Completed geometric stalk pullback comparisons coherent with source field automorphisms for derived complete adic sheaves"`:
  eight hits, including topological stalk pullback and ordinary sheaf module
  pullback. They do not state this completed coefficient result.
- `rg` in Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for completed stalk/source reparametrization
  and the proposed namespace; no exact existing declaration. The existing
  finite `ProEtalePullbackStalkCoherence` is used rather than copied.
- `grep -rn` for the exact node id in upstream `WeilConjectures`: no match.

Sources read: the complete DAG statement and all eleven proof steps; all eleven
statement dependencies and their records; Stacks sites.tex at
`lemma-point-functor` and `lemma-point-morphism-sites`, proetale.tex at
`lemma-classical-point`; and the current main-20261015 blueprint's Local powers
input (b). No statement dispute, statement correction, new definition node, or
dependency record repair is needed. The extra declarations are canonical maps,
normalization predicates, and universal constructions belonging to this item.

## Second reading by N7

Performed a separate pass with the node and the completed module open. This is a
self-check under the dispatcher's no-other-agents instruction; the maintainer's
independent review remains separate.

Checked each row above against the actual definitions and the two coherence
structures. The c direction is Fib(chi inverse), and its composition law starts
with J_w(chi), exactly as in the node. Identity laws use the specified completed
unit, not definitional equality with an arbitrary identity functor. The source
isomorphism's hom is the same `Spec.map alpha.toRingHom` as in the recorded finite
reparametrization. The action law uses `α.trans β` and therefore reverses source
scheme composition correctly. The section equation inserts both identity-point
identifications and uses the recorded kappa without replacing it by a convenient
isomorphism. The tower normalization fixes both cone coordinates, and the
realization equation quantifies every good representative and representative
isomorphism, retaining naturality for roofs. Rational normalization uses the
actual recorded raw object map and size-descent counit, and rational naturality
is a natural-isomorphism type over the entire rational category.

Implementation mismatches repaired during this pass: made the small-Hom module
localization explicit to match the point fibre; fixed the explicit full-subcategory
objects in the rational compositor; and exposed the finite-limit/colimit instances
needed by exact derived section restriction. These are typing/interface repairs,
with no mathematical hypothesis or clause changed. No remaining mismatch found.
