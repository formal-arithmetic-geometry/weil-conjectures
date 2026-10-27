## Worker report

The delivery states `WeilConjectures.FiniteCounitTowers.finiteCounitRestrictionTowers`
in `Sheaf.Paper.FiniteCounitRestrictionTowers`. Its helpers construct the actual maps
on the vertical coefficient sequence site, evaluate them with a unit-normalized
comparison, and state their identification with the etale counit maps. Every theorem
proof is `sorry`; definitions contain actual data, including additive instances
that reference separate named additive theorems. This is statement work only.

### Hypotheses and objects

- The finite-field datum is `(F : FiniteFieldDatum.{u})`, using
  `WeilConjectures.FiniteFieldDatum` in `Sheaf.Paper.FiniteFieldFiber`. In particular
  `F.k` is the fixed algebraic closure, with its existing field/algebraic-closure instances.
- The coefficient prime and its restriction are `(l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)`.
  The extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. `Ring l E n` abbreviates
  `Padic.coefficientExtensionRing l E (n+1)`: natural level zero is exponent one,
  and no coefficient exponent zero is introduced. These are the project's actual
  valuation-ring quotients, not arbitrary coefficient rings.
- `X,Y : Scheme.{u}` have the named structure maps `aX,aY` to `Spec F.k`.
  The three instances on each are separated, locally finite type, and quasi-compact,
  which together express separated finite type. `(f : X ⟶ Y) [IsFinite f]` and
  `hf : f ≫ aY = aX` make f a finite morphism of these k-schemes.
- The point is exactly `(y : Spec (.of F.k) ⟶ Y)`. It is not required to satisfy
  an additional compatibility with the k-structure: the node does not impose that.
  `S`, `v`, `h` are `Limits.pullback f y`, `pullback.fst f y`, `pullback.snd f y`.
- `Points f y` is the subtype `{x : s ⟶ X // x ≫ f = y}`. It agrees definitionally
  with the existing `Scheme.Hom.GeometricFiber` when `s = Spec k`; the generic
  abbreviation also accepts arbitrary s for the construction helpers. `lift` is
  `pullback.lift x.val (𝟙 s) ...`; its two required identities are the actual
  `pullback.lift_fst` and `pullback.lift_snd`, used in the maps themselves.
- `K : DerivedCategory (scalarReductionSource l E X)` uses the completed integral
  ring on the actual small pro-etale site. `hK : sfIntegralConstructible l E X K`
  is the recorded bounded constructible derived-complete integral condition, not
  a new boundedness/constructibility predicate.
- `Q` is a cochain complex in that category. `hQ` is
  `CochainComplex.IsKFlatIndependentCoefficients` for
  `completedIntegralCommRingSheafUnrestricted l E X`; `hflat` requires
  `SheafOfModules.IsFlatOnSite` of every `Q.X j`. `eQ : DerivedCategory.Q.obj Q ≅ K`
  says it is a representative of precisely K.
- Strict quotients use the existing `CoefficientReductionPresentation` from
  `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`. The main theorem asserts a
  presentation exists, then quantifies over every such presentation `T,κ,eT`.
  `κ n` identifies the evaluation with the termwise `scalarReductionExtension`
  of Q. The predicate includes the derived reduction normalization and the actual
  `coefficientOrdinaryQuotient` transition equations. No free transitions, etale
  origin of each term, or extra hypothesis on representatives are assumed.

### Each conclusion and its map

- `finitePoints` and the first main conjunct give `Finite (Points f y)`.
  `pointSum` is the product of the individual point pullback functors. For this
  finite index this is the canonical finite biproduct, hence exactly the direct
  sum in the statement. It is not a product indexed by arbitrary geometric points.
  The main theorem explicitly states `IsEmpty (Points f y) → IsZero (D.obj T)`.
- `pull`, `push` abbreviate the recorded
  `integralComparisonSequencePullback` and `integralComparisonSequenceDirectImage`.
  Their ordinary adjunction `adj` is `Adjunction.ofIsRightAdjoint` of that very
  sectionwise pushforward; it is not an unspecified adjunction or arbitrary map.
- `square` uses `integralComparisonSequenceComposition` and the actual pullback
  equation. Those recorded compositors are normalized by fibre-product pasting
  on the ordinary unit generators. `exchange` is its `mateEquiv` for f and h.
- `pointRestriction` pulls back the h-counit by `lift f y x`, using the recorded
  identity compositor and `h i_x = id`. `component` further uses `v i_x = x`.
  `restriction := Pi.lift component` has these exact projections. Thus the tuple
  is fixed by the counits, rather than selected from a nonempty set of isomorphisms.
- `B`, `C`, `D` apply these three functors termwise to complexes; `b`, `r` are
  `NatTrans.mapHomologicalComplex` of the two specified transformations. Their
  components are morphisms of module sheaves, so preserve addition and the
  coefficient action. Their natural-transformation types supply naturality for
  every map of complexes, including differentials and maps of representatives.
- `transitionSquares` writes both required quotient squares as equalities of
  chain maps using `coefficientSequenceTransition` and `normalizedDVRModuleRes`.
  It holds for every `n ≤ m`, so includes successive transitions. It is stated
  before applying `DerivedCategory.Q` or any derived functor.
- `fixed` retains each section and restricts its action along the actual
  constant-section map. It reuses `ProEtale.moduleSectionPresheaf`, not a chosen
  inverse equivalence. `fixedDirect_eq` identifies direct-image evaluation
  sectionwise. `fixedPull_existsUnique` fixes inverse-image evaluation by its
  ordinary adjunction unit; `fixedPull` selects this uniquely specified object.
  Thus no arbitrary identification of finite-level endpoints occurs.
- `fixedExchange` and `fixedComponent` identify the actual evaluated maps with
  `proExchange` and `proComponent`. These latter maps are explicitly the
  fixed-scalar adjunction mate and pulled-back counit. `etExchange` abbreviates the existing `Etale.baseChangeMap`;
  `etComponent` uses the existing etale adjunction and compositors.
- `comparisonCounit` states the actual counit equation for the specified
  `ProEtale.lowerStarComparisonUpperStarBaseChange`, normalized as the mate of
  `comparisonUpperStarCompUpperStarIso`. `comparisonArrows` states the commuting
  exchange square and, separately for every x, the component square. These are
  equalities of arrows using these canonical comparisons, not the assertion
  that some endpoint isomorphisms exist. Applying them termwise and localizing
  is the derived identification used for the bounded constructible reductions.
  Etale antecedents are needed only in the proof of invertibility; they are not
  hypotheses about individual terms of Q.
- `etGerm` is the actual `pointSmallEtale id` germ from the identity etale
  neighbourhood. `etGerm_isIso` identifies point sections with that stalk.
  `etComponent_stalk` identifies each component with `Etale.stalkRestrict` for h
  at `id_s` and the lift i_x, with the specified stalk-composition isomorphisms.
  The source and target transports use exactly `id ≫ x=x` and `v i_x=x`.
- `DirectExact` lists preservation of finite limits and colimits by the system
  direct image and by both fixed-scalar site direct images. The second main
  conjunct asserts this for both f and h and every coefficient level. No lfp
  assumption is added to the main theorem; its proof obtains it over the field.
- `Descent` asserts functors on the actual derived coefficient-system category,
  natural transformations between them, natural factorization isomorphisms on
  every complex, and both chain-map factorization equations. The main theorem
  asserts `Descent`. This formalizes representative independence and naturality
  after localization, rather than just existence of unrelated derived arrows.
- For every strict presentation and every level, the main theorem gives
  `QuasiIso` for both level maps and for both maps after point sections.
- It also gives `QuasiIso` of the two system maps and of both restricted tower
  maps, `IsIso` of their images under `DerivedCategory.Q`, and explicitly
  `IsIso` for the restricted maps in the derived category of towers.
- The last two clauses apply the recorded `coefficientSequenceLimit` functor to
  the localized system arrows and assert `IsIso`. This is the total derived
  inverse limit of the restricted towers, not an ordinary termwise inverse limit.

### Reused dependencies

Statement imports retain the recorded declarations for the finite-field datum,
`sfIntegralConstructible`, the integral operations, and `SfIntegralDirectImage`.
The latter remains the recorded tower-direct-image interface. The concrete
sequence-site model uses the already-landed `def-trf-integral-comparison-sequence-systems`,
`def-coef-ringed-sequence-site`,
`def-pur-coefficient-reduction-presentation`, and
`def-coef-derived-system-calculus-data`. Those nodes were added to stmt_deps;
the existing finite-module, section-presheaf and ordinary-exchange definition nodes
were also added. The comparison/stalk lemmas remain proof dependencies. Their dependency closures were checked
and do not lead back to this item.

Other concrete declarations used are `ProEtale.moduleSectionPresheaf` from
`Sheaf.AlgebraicGeometry.ClassicalContinuityMap`,
`ProEtale.finiteCoefficientIntrinsicScalarMap`, the existing etale/pro-etale
`upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, `upperStarComp`,
`upperStarId`, `comparisonUpperStar`, `comparisonUpperStarCompUpperStarIso`, and
`lowerStarComparisonUpperStarBaseChange`; `Etale.stalkRestrict` and
`Etale.upperStarCompSheafFiberIso` from the recorded upstream finite-stalk library;
and Mathlib `mateEquiv`, `NatTrans.mapHomologicalComplex`, and the derived category.
All available recorded proof-dependency modules are plain imports unless also
used in statement signatures. The complete natural-language proof is in the main
theorem docstring, with shorter source/proof docstrings on its subordinate statements.

### Edge cases and audit

Empty X or empty fibre: the subtype may be empty, no inhabitant is chosen, and
its finite product is zero; the main theorem includes the zero-object clause.
The construction allows nilpotent/nonreduced fibres: there is no reducedness or
etaleness assumption on S, and i_x is only a scheme morphism. For f=id, the square,
unit and counit are the recorded normalized ones. For K=0 and Q=0 all maps are
well-typed and the conclusions reduce to zero-complex isomorphisms. Level n=0
means A_1, not the zero exponent; arbitrary quotient gaps are included. There is
no nonemptiness, constant-sheaf condition on Q's individual terms, artificial
common site-object/morphism universe, or extra local-finite-presentation binder.
The small site retains object universe u+1 and morphism universe u.

No source-based statement correction or disputed mathematical clause was needed.
All auxiliary declarations belong to this node's specified maps and assertions;
there are no new independent notions or dependency replacements.

### Searches

- `msearch.py ... leanfinder "finite morphism exchange base change counit geometric
  stalk restriction strict coefficient reduction towers"`: eight hits concerning
  finite scheme base change etc.; no strict coefficient-system/counit theorem.
- `msearch.py ... loogle "CategoryTheory.Adjunction.counit, SheafOfModules.pushforward,
  CategoryTheory.QuasiIso"`: no matching result (the supplied QuasiIso name was
  not recognized by that search index).
- `msearch.py ... grep "finite.*(exchange|counit)|exchange.*finite|restrictionTower"`:
  ten unrelated solid/matroid hits; no match.
- `rg` on Mathlib and the named `WeilConjectures`/`Sheaf` source directories for
  the item ID, finite counit/exchange/restriction towers, adjunction mates,
  coefficient sequence evaluations, and finite-module comparison: no exact
  existing statement. Reused declarations listed above were found instead.
- Source reading: Stacks `etale-cohomology.tex` Tags 0959 and 03QP, including the
  restriction-of-germs description and vanishing of higher finite direct image;
  pro-etale finite exactness/comparison interfaces and their source docstrings.
  The generic weakly-etale `ProEtale.baseChangeMap` was not used, since it imposes
  hypotheses absent from this finite-morphism problem. The required canonical
  mate is constructed directly from the existing ordinary compositors.

### Validation

Compiled with `scompile.py` against the published live server build; no local
lake/global builds were run. One preliminary local wrapper pass exceeded its
60-second budget while the wrapper's live-server confirmation compiled in 21.9s.
After reducing unnecessary imports and avoiding repeated unfolding, the subsequent
sandbox and library passes compiled in 17.8s and 17.2s. The final reduction predicate
reuses `CoefficientReductionPresentation` and both explicit parent projections of the
chosen coefficient calculus. Its final module is recompiled by scompile and the
delivery dry run; no warning is being suppressed.

Self-audit checked the statement against the node clause by clause, including the
ordinary unit/counit normalization, strict transitions, actual stalk restriction,
restricted derived category and derived inverse limit. The maintainer performs
the independent second reading; no other agent was started by this worker.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
