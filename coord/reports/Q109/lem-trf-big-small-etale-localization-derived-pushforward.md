## Worker report

The module `Sheaf.TraceFormula.BigSmallEtaleLocalizationDerivedPushforward` states
`AlgebraicGeometry.bigSmallEtaleLocalizationDerivedPushforward`. Its conclusion is
`Nonempty BigSmallEtaleLocalizationDerivedData`: the fields unpack every clause of
the node, with the actual sites, coefficient categories and canonical maps. There
is one postponed theorem, with the complete ten-step proof plan in its docstring.
All helper definitions have real data. No theorem is proved in this delivery.

Clause-by-clause correspondence:

- Schemes and arbitrary maps: `T S S' : Scheme.{u}`, `f : T ⟶ S`, `g : S' ⟶ S`.
  All comparisons use the chosen Cartesian square `pullback f g`, with upper edge
  `pullback.fst f g` and left edge `pullback.snd f g`. This is the canonical choice
  of the fibre product the node tells us to form; neither edge is assumed étale.
- Big and small sites: `Scheme.etaleTopology.over V` on `Over V`, and
  `V.smallEtaleTopology` on `V.Etale`. Abelian sheaves are Mathlib's `Sheaf` with
  `AddCommGrpCat.{u+1}`. These are the same sites and size convention as the
  recorded `BigSmallEtaleRetractionData`. The bounded-below categories are the
  recorded `DerivedCategory.Plus`; right derived functors are the standard
  `Functor.rightDerivedFunctorPlus`, and exact inverse images are the standard
  `Functor.mapDerivedCategoryPlus`. No separate derived-category construction
  is introduced.
- Small and big geometric morphisms for every `a : V ⟶ W`: the site-data fields
  `smallTopos` and `smallToposDirect` pin the small direct image to precomposition
  with étale base change; `bigTopos` and `bigToposInverse` pin the big inverse
  image to precomposition with `Over.map a`. The abelian big inverse image is
  the existing `bigEtaleRestriction a`, and `bigEtaleDirectImage a` is actual
  precomposition with `Over.pullback a`. `bigAdj` is their adjunction;
  `bigUnit` fixes its unit to restriction along the first projection. This also
  fixes the adjunction's counit and all subsequent mates.
- The continuous and cocontinuous `u_g`: the fields `continuous` and
  `cocontinuous` concern exactly `Scheme.Etale.forget V ⋙ Over.map a`.
  `i` is its geometric morphism, and `iRestriction` is a natural isomorphism of
  underlying presheaf functors, so it includes the section formula and all
  restriction maps. Its actual abelian inverse image is `smallEtaleRestriction a`,
  defined by `sheafPushforwardContinuous` along that same functor. Exactness is
  `smallLimits` and `smallColimits`; these are conclusions of the existential
  package, not assumptions added to the theorem.
- `i_g = g_b ∘ i_id`: `iFactor`, a natural direct-image identification of those
  two geometric morphisms. `piComp` identifies `pi_W ∘ i_a` with `a_s` for every
  `a`, thus in particular both `g` and `g'`. On abelian sheaves,
  `restrictionFactor` identifies small restriction with big localization followed
  by the existing retraction's direct image; `restrictionFactor_sections` fixes
  that identification to identity on sections under `direct_restrict`.
- The exact retractions are `sites.pi V : BigSmallEtaleRetractionData V`, using
  the dependency's actual interface. `directSquare` is the big/small direct-image
  square, pinned to its identity section formula by `directSquare_sections`.
  `inverseSquare` is its adjunction conjugate, using `conjugateIsoEquiv`, with
  both composite adjunctions explicit. It is not a freely selected isomorphism.
- The two natural underived comparisons are `sites.c f g` and `sites.ell f g`.
  Their section maps, `c_sections` and `ell_sections`, are precomposition with
  `etaleLocalizationFibreMap f g U.hom`. This real construction uses
  `pullback.lift` and its two projections, so it is the specified canonical
  fibre-product map, including for all nonétale big objects in the second case.
- `c_{g,M}`: `restriction_iso` asserts that the natural transformation
  `BigSmallEtaleLocalizationSites.restrictionComparison f g` is an isomorphism.
  This is equivalent to a natural isomorphism with precisely the source and
  target in the node for every `M : D⁺(Ab(B_T))`. `restrictionSquare` is the
  inverse adjunction mate of the actual underived `c`. It is a transformation,
  not an isomorphism. `sigma_fac` says `sigma` is its exact termwise descent,
  with every homotopy and derived factorization comparison included.
  `restriction_mate` identifies the derived `c` with the mate of this `sigma`
  under the standard `Adjunction.derivedPlus` adjunctions.
- `ell_{g,M}`: `localizationComparison` is defined as the derived adjunction mate
  of the canonical big inverse-image square `localizationSquare`; the latter
  uses Mathlib's `overMapPullbackComp`, `overMapPullbackCongr`, and the pullback
  equation. `localization_iso` asserts that this natural transformation is an
  isomorphism; `localization_model` identifies it with derivation of the
  sectionwise comparison `sites.ell`. Thus both canonical normalization and
  the claimed source and target are retained.
- The beta arrow is `BigSmallEtaleLocalizationSites.beta f`. It uses exactly the
  `mateEquiv` formula of `def-trf-topos-derived-base-change-map`, specialized
  directly to abelian sheaves and the canonical `derivedInverseSquare`; the
  source, target and standard derived adjunctions are explicit. The recorded
  ringed-topos declaration is imported, and this helper realizes its stated
  constant-integer/abelian specialization without replacing abelian sheaves by
  arbitrary module categories or assuming an unspecified scalar equivalence.
- The identifications `i_a⁻¹ pi_W⁻¹ ≅ a_s⁻¹` are `eta a`. `eta_unit` pins them to
  `restrictionFactor`, the canonical `inverseSquare`, and the retraction unit.
  Invertibility of the latter is already in the dependency's retraction data.
  `derivedRestrictionInverse` descends `eta` using the standard exact-functor
  composition and natural-isomorphism comparisons.
- The precise arrow identification is the field `arrow`: restrict actual `beta`,
  then compose with actual `c` and the upper-edge `eta` under derived direct
  image; this equals the lower-edge `eta` followed by the recorded
  `Etale.derivedBaseChangeMapPlus` for the pullback square. In particular, this
  is equality of the specified maps, not just existence of isomorphic objects
  or an assertion that some exchange is invertible.
- Joint conservativity is `jointly_conservative`: for every derived morphism
  `z : X ⟶ Y` on the big site, invertibility of its restrictions for every
  `S' : Scheme.{u}` and every `g : S' ⟶ S` implies `IsIso z`.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its homs.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.etaleTopology`, and `Scheme.Etale.forget`.
- `Sheaf.TraceFormula.BigSmallEtaleExactRetraction` and its public data module:
  `BigSmallEtaleRetractionData`, including both direct-restriction isomorphisms,
  the geometric and abelian adjunctions, exactness, and the invertible unit.
- `Sheaf.TraceFormula.BigSmallEtalePullbackFormula`: the already existing
  `bigEtaleRestriction`. Its owning landed node was added to `stmt_deps`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`,
  retaining the dependency's Mathlib `Sheaf` encoding rather than redefining it.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism` and `.comp`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.TStructure`:
  `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Plus`.
- `Sheaf.CategoryTheory.DerivedBaseChangeMap`: the ringed derived comparison
  definition and its counit-transpose normalization, specialized as explained above.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `Etale.derivedBaseChangeMapPlus`, with its full source signature and docstring read.
- `Sheaf.CategoryTheory.DerivedExactSquare`:
  `Functor.mapDerivedCategoryPlusSquareIso`, used to descend the canonical
  inverse-image squares. Its landed owning node was added to `stmt_deps`.
- Mathlib `conjugateIsoEquiv`, `mateEquiv`, and over-site composition comparisons;
  upstream `Functor.rightDerivedFunctorPlusBaseChange` and `Adjunction.derivedPlus`.
  The stated proof dependencies are imported for stage 3.

Edge cases checked against the definitions and statement:

- `g = id`, `f = id`, and arbitrary nonétale `g` are included: the square is a
  scheme pullback and no étaleness assumption occurs on these arrows.
- Empty source/base/base-change schemes are included, as are zero sheaves and zero
  or shifted derived objects. All small and big final objects still exist.
- Every lower cohomological bound is allowed by `DerivedCategory.Plus`; no fixed
  bound, degree-zero reduction, or injective-representative hypothesis is imposed
  on `M` or `K`.
- There is no properness, torsion, finite-type, annihilator, characteristic or
  invertibility hypothesis. These belong to downstream proper comparison only.
- The possibly noninvertible restriction inverse-image square is not confused
  with the invertible big localization square.
- Conservativity quantifies over every big object, not only small étale ones.

Searches (no exact existing theorem found):

1. `msearch.py ... leanfinder`: “Restricting derived big etale direct image to the
   small etale site of any scheme over the base agrees with derived direct image
   on the fibre product”. Eight hits: site inclusion, site topology, and unrelated
   underived open-module restriction declarations. No localization/exchange theorem.
2. `msearch.py ... loogle`: `"sheafPushforwardContinuous", "rightDerivedFunctorPlus"`.
   Zero hits.
3. `msearch.py ... grep`: `bigSmall|bigEtale|compareHigherDirectImage` in Mathlib.
   Zero hits.
4. `msearch.py ... leansearch`: “Derived direct image on the big etale site commutes
   with localization and restriction to small etale sites, compatibly with the base
   change mate”. Eight hits: topology, generic derived adjunction and generic
   sheafification compatibility; no exact theorem.
5. `rg` over upstream `WeilConjectures`, side `lean/Sheaf`, and Mathlib for
   `bigSmall|BigSmall|bigEtale|BigEtale|localizationDerived`, and for the proposed
   declaration names. This found the existing retraction, pullback formula, and
   ph comparison consumers. Their full signatures/docstrings were read. They do
   not contain this theorem. The existing big restriction was reused.
6. Item-id search in upstream `WeilConjectures` and `dag/lean_names_upstream.json`:
   no binding. No repair note exists for the item. The main Stacks source passages
   075A(3),(5), 021F, 021I, 0DDA and 0DDJ(2) were read locally.

No statement correction, dependency repair or new independent notion is needed.
The new declarations are helpers and a witness package for the one stated node,
with its blueprint/source tag on every declaration. There is no
`STATEMENT-DISPUTED` issue.

## Second reading by Q109

This is a second pass by the same dispatched worker, not a claim of independent
review. The brief forbids spawning agents and reserves independent review to the
maintainer. I reopened the node and the complete Lean module and matched every
hypothesis and conclusion using the correspondence above. In particular I checked
that the two comparisons have different target sites, that `restrictionSquare`
is not assumed invertible, that beta uses the conjugate of the actual sectionwise
direct-image identity, and that `eta_unit` fixes the comparisons used in `arrow`.
The natural-transformation equality has both eta identifications and the restriction comparison in their
correct directions. Conservativity concerns arbitrary derived morphisms.
No mathematical clause was dropped or strengthened. Helpers were given explicit
universes and all declarations were listed in the node record.

The logical fields are named predicates in `BigSmallEtaleLocalizationSites`
(`IsEtaUnit`, `IsSigmaFactorization`, `IsRestrictionIso`, `IsRestrictionMate`,
`IsLocalizationIso`, `IsLocalizationModel`, `IsExchangeCompatible`, and
`IsJointlyConservative`). Their bodies are exactly the clauses described above.
This avoids a large dependent record forcing the kernel to expand all derived
constructions repeatedly. `restrictedBetaExchange` and `smallExchangeTransport`
write the two sides of the arrow equation as natural transformations with explicit
associators. Equality of these transformations is the node's component equation
for every bounded-below `K`. The six standard derived-functor names and these
clause predicates are transparent definitions, with no postponed data.

Validation: the prescribed `scompile.py` completed successfully for the complete
module in both sandbox and library-path modes (14.3 s and 40.9 s respectively),
with no errors and no warnings. The delivered source has no diagnostic commands,
no raised heartbeat or time limit, no auto-bound implicits, no line over 100
characters, and exactly one postponed theorem proof.
