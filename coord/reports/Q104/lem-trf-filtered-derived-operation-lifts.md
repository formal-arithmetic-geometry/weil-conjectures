## Worker report

This repairs returned head `27738437c863` in
`Sheaf.CategoryTheory.FilteredDerivedOperationLifts`. The original DAG statement,
source, seven proof steps, and proof dependencies are retained verbatim. The earlier
sandbox's proposed `statement_change` is withdrawn: defects in that Lean translation
were not defects in the mathematical statement. The only added statement dependency
is the already landed `def-trf-finite-filtered-localization`, whose concrete category
and localization functors the signature uses.

### Returned points repaired

1. The specialization is a package over **every** scheme and arbitrary scheme map,
   not unused coefficient-operation data. `compactification` takes an actual supplied
   `c : Compactification f` and lifts the recorded
   `rightDerivedLowerShriekOfCompactificationPlus`. `compactificationFormula` requires
   its filtered functor to equal the composite of the open lift for `c.i` and the
   pushforward lift for `c.g`. `compactificationForget` and `compactificationGraded`
   identify that lift's own comparisons with the composed operation comparisons.
   `ordinaryCandidateFormula` identifies the ordinary expression with the recorded
   `Rp_* j_!` candidate. No compactification existence is assumed or asserted.
2. The former arbitrary `FilteredCompactSupportExchange` record is removed.
   `filteredOperationOrdinaryFormalism` is constructed from the actual pro-etale
   `upperStar`, `lowerStar`, `openImmersionLowerShriek`, and their specified derived
   adjunctions. `ProEtaleFilteredOperationData.toFormalism` uses their actual filtered
   lifts and adjunctions. `FilteredCanonicalMap` generates the canonical expressions;
   its evaluator computes the identity/composition, adjunction, proper square,
   open square, compactification exchange/composition, and refinement maps using
   existing mate formulas and explicit definitions. No constructor accepts an
   arbitrary natural transformation. `RespectsCanonicalMaps` equates the forgetful
   and every graded map of these actual expressions with their ordinary evaluations.
   Primitive comparison isomorphisms are additionally normalized against the
   operation lifts' own comparisons and units/counits.
3. `FilteredTermwiseLift` now records `objectAction` on finite filtered objects,
   its additive structure, its underlying functor comparison with `H`, and a
   comparison of every filtration step with `H(F^p K)`. `stepInclusion` identifies
   the inclusion with `H` of the original inclusion. Naturality of the underlying
   comparison and monicity of the inclusions also determine the induced step maps.
   `localizationComparison` identifies the derived filtered functor, after the
   **actual** localization functor, with that very object's degreewise homotopy
   functor followed by localization. Thus a filtered functor unrelated to the
   termwise action cannot satisfy this record merely by supplying graded isos.

The compactification/refinement clause is explicit as well.
`filteredOperationProperOpen` first applies the inverse Cartesian open comparison,
then the projection onto the clopen section, then the pullback/open composition
comparisons, and finally takes the proper-adjunction mate.
`FilteredOperationClopen` specifies the reverse clopen adjunction by requiring its
counit to be the inverse of the fixed open-adjunction unit; this determines that
adjunction and its projection unit uniquely. Its maps are not arbitrary parameters.
`FilteredRefinementFactorization` gives the geometric pullback and clopen section
of an actual refinement, and `filteredOperationRefinement` is the resulting formula.
`FilteredOperationRefinementPasting` equates the two actual exchange/refinement paths,
including non-Cartesian refinement squares. `FilteredOperationVerticalPasting`
equates the two actual composition/exchange paths for compatible compactification
towers. Both equations occur for the ordinary and filtered formalisms in the package.

### Hypothesis and clause correspondence

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Abelian categories A and B with enough injectives | Explicit `Category`, `Abelian`, `EnoughInjectives` binders for both; independent object, morphism and localization universes |
| Ordinary D+ and filtered DF+ | `DerivedCategory.Plus` and recorded `FiniteFilteredDerivedPlus`; `none` permits all finite filtrations and `some (a,b)` fixes an interval |
| Forgetting and every associated grade | Recorded `finiteFilteredDerivedEvaluation bounds none` and `bounds (some r)` |
| T additive and left exact | `(T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]` |
| Exact filtered right-derived lift | Existential `FilteredDerivedOperationLift T.rightDerivedFunctorPlus`, with actual shift comparison and triangulatedness fields |
| Natural forgetful and graded comparisons | `forgetComparison` and `gradedComparison : ∀ bounds r, ... ≅ ...` |
| Exact additive H acts termwise | Quantification over `[H.Additive]`, `[PreservesFiniteLimits H]`, `[PreservesFiniteColimits H]`, with the termwise/localization record above |
| If exact L is left adjoint to T | Conditional quantification over `L : B ⥤ A`, both exactness instances and an actual `(adj : L ⊣ T)` |
| Filtered adjunction and its unit/counit under forgetting and grading | `FilteredDerivedAdjunction adj.derivedPlus`, its actual `filteredAdjunction`, and the four `unitForget`, `counitForget`, `unitGraded`, `counitGraded` equations using the explicit transport definitions |
| Finite commutative coefficient ring | Independent `(R : Type u) [CommRing R] [Finite R]`, not tied to the universes of A or B |
| Small pro-etale constant-ring modules | `FilteredOperationCoefficients R X` is the fixed-scalar presentation in the **recorded** `sfIntrinsicModuleEquivalence X R`, with `ModuleCat.{u+1} (ULift R)` and the original small-site universe |
| Same intrinsic ordinary operations | Package fields `intrinsicPullback` and `intrinsicPushforward` compare canonical `sfIntrinsicTransport` of these sheaf functors to the recorded `proEtaleConstantRingPullback/Pushforward`; `intrinsicOpen` identifies the transport with recorded `sfIntrinsicExtensionByZero` |
| Ordinary, uncompleted pullback, derived direct image, open extension | `upperStar.mapDerivedCategoryPlus`, `lowerStar.rightDerivedFunctorPlus`, `openImmersionLowerShriek.mapDerivedCategoryPlus`, with their actual adjunctions |
| Supplied c=(j,p), Rp_*j_!, and its filtered composite | `compactification`, `compactificationFormula`, `ordinaryCandidateFormula`, `compactificationForget`, `compactificationGraded` |
| Canonical identity, composition, proper and open comparisons | `FilteredCanonicalMap` constructors and the real `eval` definitions; proper/open special compactifications also use the identity-comparison and unitor constructors |
| Unit-square-counit mate for any commutative square | `properSquare` evaluates to `CompactSupportFormalism.pfBaseChange`, defined by `mateEquiv (adj r) (adj l) sqIso.inv`; no Cartesian or invertibility assumption is added |
| Open extension comparison | `openSquare` and its Cartesian inverse evaluate to the actual `baseChange` mate and its inverse |
| Actual compactification exchanges | `compactificationExchange` evaluates to `shriekBaseChange`, composing the proper-factor mate with the inverse open-factor comparison |
| Composition/refinement comparisons | Constructors `compactificationComposition`, `refinement`, `properOpen`, and `clopenProjection` evaluate to the displayed actual formulas |
| Forgetful/graded maps are exactly ordinary maps | `comparison bounds p`, primitive normalization fields, and `canonicalMaps : RespectsCanonicalMaps` for all `p : Option ℤ` |
| Composition and whiskering | Recursive `comp`, `left`, `right`, associator, equality-transport and unitor constructors evaluate by literal composition and whiskering; `comparison.operation` uses the same associators |
| Invertibility on admissible domains | `detectsIsomorphisms` is objectwise: all ordinary graded evaluations must be isomorphisms, then the actual filtered map is an isomorphism; this permits inverses precisely where all graded inputs are admissible |
| Bounded-below and conditional bounded-constructible/finite-Tor restriction | All functors act on D+/DF+; no subdomain preservation or global proper-base-change invertibility is postulated. Full-subcategory restriction is available when its objects and all grades lie in the stated domain |
| Arbitrary base maps, no fixed-field linearity | All geometric parameters are `Scheme.{u}` morphisms, with no field or algebra-linear structure |
| Vertical Cartesian pasting | `ordinaryPasting` and `filteredPasting` state `FilteredOperationVerticalPasting` for the actual maps. The raw equality becomes the node's composition-isomorphism equation when those comparison arrows are inverted on the admissible domain |
| Refinements intertwine that equation | `ordinaryRefinementPasting` and `filteredRefinementPasting`, together with the same canonical composition/exchange expressions, give the actual refinement-intertwining equation |

### Dependency declarations and source reading

Every original statement dependency's statement and Lean/mathlib record was read.
The concrete interfaces used are:

- `Sheaf.Algebra.Homology.FiniteFilteredLocalization`:
  `FiniteFilteredObjects`, `filteredEvaluation`, `FiniteFilteredDerivedPlus`,
  `finiteFilteredQh`, `finiteFilteredDerivedEvaluation`; their signatures and
  localization docstrings were read. The category is not a new localization copy.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`:
  `DecreasingFiltration`, its recorded step/graded interface, and `FilteredObject`;
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `complexStep`, `complexQuotient`, `complexQuotientπ`, `complexCycles`,
  `complexBoundaries`. The lift uses these same filtrations and inclusions.
- `Mathlib.CategoryTheory.Abelian.Basic`: `Abelian`;
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`,
  `EnoughInjectives`; `...Injective.Resolution`: `InjectiveResolution`.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `Functor.Additive`;
  `Mathlib.CategoryTheory.Limits.Preserves.Finite`: `PreservesFiniteLimits`;
  `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived` and its
  resolution interpretation. The total bounded-below functor used here is
  `Functor.rightDerivedFunctorPlus` from Mathlib's derived-category interface.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the ordinary localization;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `Adjunction.derivedPlus`; `...PlusExact`:
  `Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  recorded `proEtaleConstantRingPullback`, `proEtaleConstantRingPushforward`,
  `proEtaleConstantRingAdjunction`, `proEtaleConstantRingDerivedPullback`;
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicModuleEquivalence`, `sfIntrinsicExtensionByZero`;
  the reexported `sfIntrinsicTransport` is the actual canonical realization transport.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, its bounded-below counterpart
  `rightDerivedLowerShriekOfCompactificationPlus`, and their compatibility iso.
- `WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange` and its imports:
  `CompactSupportFormalism`, `pfBaseChange`, `baseChange`, `exchange`, `shriek`,
  `shriekBaseChange`, `pfComp'`, `shComp'`, and the existing raw composition formula.
  Their definitions were read, especially the mate directions.

The proof docstring is a complete seven-step natural-language construction, following
the unchanged node's proof. Stacks `derived.tex` was checked at filtered localization,
the definition of the filtered derived functor, and `equation-commute-gr` /
`equation-commute-forget` (Tags 015Q, 015S, 05U2, 015U, 015V). The canonical-map and
pasting clauses follow the node's stated Varshavsky Lemma 5.1.4 and §§5.2.1–5.2.2,
and Stacks proper/open formulas (Tags 0F7B–0F7F).

### Searches and edge cases

The saved searches and fresh repair searches were retained. `msearch.py leanfinder`
for “filtered derived functors on finite filtered complexes commute with forgetting
filtration and associated graded, and derived adjunction units and base change maps
lift to filtered derived categories” returned eight ordinary derived-functor/factorization
hits, with no filtered-operation theorem. The repair search for “An exact functor
applied termwise to finite filtered objects descends to the filtered derived category”
also returned ordinary derived-factorization results only. `loogle` for
`CompactSupportFormalism, filteredInjectiveComparison, mapHomotopyCategoryPlus`
returned no result. The saved loogle query for `CategoryTheory.Functor.rightDerived,
CategoryTheory.Adjunction` likewise had no match. Mathlib grep for
`FilteredDerived|filteredRightDerived|filtered.*derived|derived.*filtered` had no
match. `rg` of upstream `WeilConjectures` and `lean/Sheaf` found the ordinary
operations, canonical mate formalism and recorded finite-filtered localization,
but no theorem stating this item. Searching the item id found no existing upstream
statement. Existing notions are reused; all supporting records/expressions here
belong to this theorem's interface and are listed in `lean.declarations`.

Checked: zero functor; zero/one-piece filtrations; every integer grade, including
outside a supplied interval; `none` and empty fixed intervals; identity adjunction;
identity and open/proper special compactifications; arbitrary finite rings including
the zero ring; arbitrary non-field-linear scheme maps; a noninvertible ordinary
proper exchange (the mate is still defined); admissible inverses requiring every
graded input; Cartesian refinements (clopen projection is identity) and a proper
refinement with a nontrivial complementary component (the clopen projection kills
that component). The refinement and vertical-pasting formulas use actual maps, not
faithfulness of forgetting. No `STATEMENT-DISPUTED` mathematical fault was found.

Only the named main theorem has `sorry`; definitions contain real data. Every
universe and variable is explicitly bound, and `autoImplicit` is disabled.

## Second reading by Q104

No independent second worker was started: the dispatcher's explicit instructions
forbid delegation and assign the independent review to the maintainer. I performed
an author self-check with the unchanged DAG statement and final module open.
It caught and repaired the three returned omissions, the spurious statement-change
record, missing normalization of candidate comparisons, and omission of the clopen
refinement formula. The clause table above records the final check. This section
does not claim an independent review.
