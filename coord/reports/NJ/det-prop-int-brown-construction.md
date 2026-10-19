## Worker report

The module `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` states
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.integralLocalizingCompactSupport`.
This is a statement delivery: its only theorem proof is `sorry`. All definitions have
real data. The other declarations package the categories, canonical maps and clauses
of this very node; they introduce no independent mathematical prerequisite.
The node is unchanged except for `lean`. There is no statement correction or dispute.
The archived repair note is a resolved stage-1 re-split, not a released stage-2 interface
repair; its seven-step proof plan is retained and included in the theorem docstring.

Hypothesis and clause correspondence:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The finite extension is
  `E : PadicAlgCl.FiniteIntermediateField ℓ`, the existing model of finite extensions
  inside an algebraic closure. Its valuation ring with its ell-adic topology is the
  existing `Profinite.padicIntegersRingObj ℓ E.val`, a condensed commutative ring.
- The ground field and positive characteristic different from ell are
  `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.
- `Spaces k` is the full subcategory of `Over (Spec (.of k))` on separated,
  locally finite-type, quasi-compact structure maps. The last two conditions are
  finite type. Its morphisms are exactly k-morphisms. Morphisms between these spaces
  are automatically separated and finite type; there is no smoothness, properness,
  nonemptiness, projectivity or extra assumption on f, g or the base-change maps.
- `Ambient Λ X` abbreviates the existing ordinary unbounded
  `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})
  (condensedRingObj Λ X))`. The coefficient sheaf is the pulled-back condensed ring.
  `generators` is exactly `constantModelBoundedConstructible Λ X` from the recorded
  constructibility dependency. It does not use upstream's different, broader local
  finite-presentation predicate.
- `localizing Λ X` applies the recorded `CategoryTheory.localizingClosure` to those
  generators. This is Loc(Dbc), not the coefficient-general Loc(Dctf) specialization
  `localizingClosureProEtale`. It uses the same intersection of full replete
  triangulated subcategories and the same ambient ordinary coproducts. There is no
  completed coproduct or derived-completeness condition.
- `Compactifications k f` is the dependency's `Compactification.QuasiCompactObjects`:
  the actual `Compactification` has open immersion `c.obj.i`, proper map `c.obj.g`
  and factorization equality, and its property retains quasi-compactness of the open.
  The middle scheme is again standing via its proper map to the target.
- `image Λ c.obj` is an abbreviation of the dependency's
  `rightDerivedLowerShriekOfCompactification Λ c.obj`, definitionally
  `(openImmersionLowerShriek Λ c.obj.i).mapDerivedCategory ⋙
  (lowerStar Λ c.obj.g).rightDerivedFunctor`. It is the specified Rp_*D(j_!), not
  a total derivation of the underived composite and not a replacement functor.
- `Preservation.maps_localizing` is precisely well-definedness on Loc.
  `Preservation.exact` states preservation of ambient distinguished triangles with
  all vertices in Loc, using the canonical shift structure of the two factors.
  Since the restriction is full and the factors additive, this is exactness of
  the restriction.
- `Preservation.coproducts` requires `PreservesColimit F (image Λ c.obj)` for every
  discrete diagram with its objects in Loc. Its index universe is `u+2`, exactly
  the object/index universe used by the recorded generic localizing closure on this
  ambient derived category (`Ambient` has type `Type (u+2)`, checked by compilation).
  Thus every ordinary ambient coproduct cocone in that closure is preserved.
- `Preservation.maps_constructible` is preservation of Dbc.
- `Comparisons` gives natural isomorphisms between the candidates on the full Loc
  source category, for every pair of compactifications. `Coherence.identity` and
  `Coherence.cocycle` are the displayed identity and cocycle conditions.
  `Coherence.normalized` fixes their values on boundary-preserving refinements:
  the proper-open isomorphism e has transpose satisfying
  `homEquiv e.hom ≫ refinementRestriction = openAdjunction.unit`, where the
  restriction uses actual pullback composition and the proper adjunction counit.
  `refinementIso` is inverse proper composition followed by pushforward of e inverse.
  Hence these are the canonical compactification comparisons. The cocycle law and
  common boundary refinements determine pairwise comparisons independently of choices.
- `Compositions` gives natural isomorphisms from the inclusion followed by
  `image c ⋙ image d` to the inclusion followed by `image e` for every composable
  f,g and every choice of the three compactifications. This is Rg_! Rf_! ≅ R(gf)_!.
  `Coherence.composition_compatibility` is the commuting square for changing any
  or all of these three compactifications.
- `Coherence.base_change` quantifies over every standing cartesian square, represented
  by `IsPullback` of its actual scheme maps, including nonliteral pullback models.
  `baseCompactification` uses the recorded `ofIsPullback` and transports
  quasi-compactness through its recorded open pullback square.
- The base-change map is explicitly `baseChange`: proper exchange followed by the
  inverse open exchange, with associators. `pushExchange` and `openExchange` are
  the actual unit/square/counit mates. `pullSquare` comes from
  `leftDerivedUpperStarComp` and the equality of maps in the supplied square.
  The open inverse uses an `IsIso` proof; no arbitrary inverse or arbitrary map
  is quantified over. `Coherence.base_change` asserts that the resulting map is
  an isomorphism at every object of Loc.
- `Coherence.base_change_compatibility` is its commuting square with the canonical
  comparisons and their pulled-back compactifications.
- `constructible_pull` and `localizing_pull` ensure that the pullback functors in
  the base-change clause have the stated restricted domains and codomains. Together
  with `maps_constructible`, fullness of Dbc in the ambient category restricts the
  *same* comparison, composition and base-change maps and equations to Dbc; it does
  not replace them with unrelated isomorphisms. Membership Dbc ⊆ Loc follows directly
  from the definition of the localizing closure.

The preservation and coherence predicates and the families of natural isomorphisms
are existential conclusions of the theorem, not assumptions on the input. The
statement creates no definition by choosing unspecified data from an admitted
existence theorem. Every canonical-map helper is an explicit construction.

Dependencies read and used:

- `sk-def-sfb-dc-setting`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `CondensedRing.compactificationOverField`, its full standing-setting documentation,
  and the compactification-over-base interface. Current published source was also
  read through `scompile.py --source`; no chosen-compactification interface is copied.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible` and its full
  constant-model/stratification/bounded-cohomology construction.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingClosure`,
  `CategoryTheory.IsLocalizingSubcategory`, `CategoryTheory.localizingClosure` and
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale`. The generic operation is
  applied to Dbc, as this item explicitly requires, rather than to Dctf.
- `sk-def-nagata-sketch-data`: `Sheaf.Compactification.BoundaryRefinement`,
  `Compactification.QuasiCompactObjects` and the equality defining boundary refinements.
- `sk-def-sfb-module-derived-lower-shriek`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`,
  `CondensedRing.rightDerivedLowerShriekOfCompactification`.
- `sk-def-sfb-module-derived-pushpull`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`,
  `derivedUpperStarLowerStarAdjunction`, `leftDerivedUpperStarComp`, and the actual
  generic `Functor.leftDerivedFunctor` and `Functor.rightDerivedFunctor`.
- The open adjunction is the published
  `derivedOpenImmersionLowerShriekUpperStarAdjunction`, transported through
  `leftDerivedUpperStarIsoMapDerivedCategory`. Proper pushforward composition is
  the conjugate of derived pullback composition, using `conjugateIsoEquiv`.
- Of the seven proof dependencies, only `sk-lem-int-tensor` has a recorded Lean module:
  `Sheaf.SixFunctors.IntegralTensorInverseImage`, `integralTensorInverseImage`.
  It is imported without `public`. The other six have no recorded Lean module and
  therefore no proof imports can yet be added. Their ids and complete uses are
  present in the theorem's proof docstring, following the node's seven-step plan.

Edge cases checked before finalizing:

- The empty scheme is included in `Spaces`; no `[Nonempty X]` is imposed.
- Empty and singleton diagrams are included by arbitrary `I : Type (u+2)`;
  no positive-cardinality or nonempty-index restriction is imposed.
- Zero complexes and their triangles are included. Maps and mate normalizations
  are defined in the existing additive derived categories without nonzero hypotheses.
- Identical compactifications are covered by `identity`, repeated ones by `cocycle`.
- The base-change square can be an identity square, and can use any isomorphic
  pullback model; it is not restricted to a chosen fibre-product construction.
- Compactifications may have extra boundary components and need not be dense.
  Normalization is required on boundary-preserving refinements; pairwise comparisons
  are quantified for every quasi-compact compactification, not only dense ones.
- E may be the base ell-adic field (degree one), ell may be 2, and the only exclusion
  on the positive characteristic is the specified inequality with ell.
- The site remains Scheme.{u}.ProEt (objects in u+1, arrows in u); coefficient
  abelian sheaves are in u+1 and the ordinary derived category has objects in u+2.
  No equality between those universes was imposed.

Searches (2026-10-18):

- `msearch.py ... leanfinder`: "Compactly supported integral pro etale derived
  pushforward preserves ordinary coproducts on the localizing closure of bounded
  constructible complexes, with compactification comparison composition and base change".
  Eight hits included `Scheme.Modules.pushforwardComp`, ordinary sheaf-pushforward
  composition and condensed colimit results, not this theorem.
- `msearch.py ... loogle`: "rightDerivedLowerShriekOfCompactification,
  PreservesColimitsOfShape". No hits; the project-specific name is unknown to Loogle.
- `msearch.py ... leansearch`: "Integral compact support pushforward on localizing
  derived categories preserves coproducts and is compatible with composition and
  base change". Eight hits concerned underived sheaf pushforward, its associativity,
  and preservation of finite coproducts; none matches this statement.
- `msearch.py ... grep`: "localizing.*[Ll]owerShriek|[Ll]owerShriek.*localizing|[Bb]rown"
  in Mathlib/CategoryTheory. Only author-name hits for Thomas Browning; no match.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf` for
  the item id, `localizingLowerShriek`, and `integral.*[Bb]rown`: no match.
  Follow-up searches for `rightDerivedLowerShriekOfCompactification` found the generic
  derived constructions, finite/discrete-coefficient comparison modules and their
  proper/open interfaces. Those do not state this integral module-object theorem.
- Read the exact blueprint statement and proof under
  `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-int-brown/`.
  The already reviewed stage-1 node's standing-scheme restoration is respected.

Validation: `scompile.py NJ det-prop-int-brown-construction` is used for every file
compile; no direct Lean/Lake/global build or repository Git command was run. The final
compiler and delivery-preflight results are recorded below after their completion.

## Second reading by NJ

The delivered version of this section was a worker self-check that said "no independent
worker reading is claimed here" (delivery-errors H11). The maintainer's independent
reader (cc review service, 2026-10-18) did the reading below and put it in its place.
It reads the node (statement, seven proof steps, six stmt_deps), the source place
(main-20261015 sk-prop-int-brown-construction and its proof), and the module
`Sheaf.SixFunctors.IntegralLocalizingCompactSupport` at 63b0d38287d8.

Clause by clause (node → Lean → verdict):

- Prime ℓ → `(ℓ : ℕ) [Fact ℓ.Prime]`: correct.
- Field k, char p > 0, p ≠ ℓ → `(k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]`: correct. Positive characteristic is the primality of `ringChar`.
- Finite E/Q_ℓ with valuation ring O_E as a condensed ring →
  `E : PadicAlgCl.FiniteIntermediateField ℓ`, `Profinite.padicIntegersRingObj ℓ E.val`.
  This is C(S, O_E) for the ℓ-adic topology restricted from the algebraic closure
  (`RingObjects/Condensed/EllAdic.lean:135`), as a commutative ring object: correct.
- Standing schemes and k-morphisms → `Spaces k`. This is the full subcategory of
  `Over (Spec k)` on separated, locally-finite-type and quasi-compact structure maps (=
  finite type). Over-morphisms are exactly k-morphisms: correct. No extra hypothesis. The
  empty scheme is allowed.
- Pulled-back coefficients and the unbounded module-object derived category → `Ambient`,
  `DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab) (condensedRingObj Λ X))`: correct.
- Dbc of sk-def-sfb-constructible → `generators = constantModelBoundedConstructible`. This
  is the recorded declaration of that node: bounded, with every cohomology sheaf
  `IsConstantModelConstructible`. Correct.
- Loc(Dbc) with ordinary small coproducts (sk-def-localizing-closure) →
  `CategoryTheory.localizingClosure (generators Λ X)`, the generic closure in
  `Sheaf.Paper.LocalizingClosure`. That closure is re-exported by the recorded
  module and indexes coproducts by the object universe of the ambient category. Correct.
- Compactification c = (j quasi-compact open, p proper) → `Compactifications k f =
  Compactification.QuasiCompactObjects f.hom.left`. This is the recorded nagata datum:
  open immersion `i`, proper `g`, `f = i ≫ g`, plus `QuasiCompact i`. Correct, and density is
  not required.
- Rf_!^c = Rp_* D(j_!) → `image Λ c.obj = rightDerivedLowerShriekOfCompactification`.
  This is the recorded declaration of sk-def-sfb-module-derived-lower-shriek. Correct.
- "restricts to an exact functor Loc → Loc" → `Preservation.maps_localizing` and
  `Preservation.exact` (distinguished triangles with vertices in Loc go to distinguished
  triangles under the canonical shift structure): correct.
- "preserving small direct sums" → `Preservation.coproducts`. It requires `PreservesColimit`
  for every discrete diagram indexed by `Type (u+2)`, the closure's index universe, with
  objects in Loc. Correct; the empty family is included.
- "carrying Dbc into Dbc" → `Preservation.maps_constructible`: correct.
- Canonical comparison isomorphisms with identity and cocycle → `Comparisons` and
  `Coherence.identity`/`cocycle`. `Coherence.normalized` pins them on boundary-preserving
  refinements by the open-unit / proper-counit normalization. Correct. Normalization on
  non-dense boundary-preserving refinements is consistent with det-sf-comp-coherence-cocycle,
  whose comparisons go through common dense refinements. A dense refinement w → c composed
  with r is the unique refinement w → d, and the refinement isomorphisms compose.
- Natural composition isomorphisms Rg_!Rf_! ≅ R(gf)_!, compatible with comparisons →
  `Compositions` and `Coherence.composition_compatibility`, for all three choices of
  compactification. They agree with the node's wording ("natural", "compatible"). The node
  does not pin the composition map further, and neither does the Lean.
- Base change v^*Rf_! → Rf'_!u^*, an isomorphism on Loc for every cartesian square →
  `Coherence.base_change`, with the specific map `baseChange`: the proper exchange mate
  followed by the inverse of the open exchange mate. It quantifies over every `IsPullback`
  square of standing schemes. The invertibility of the open exchange on the whole ambient
  category is clause (1) of det-sf-comp-composition-base-change (v'^*j_! ≅ j'_!u^* on
  D(X)), so this is not an unintended strengthening. Correct.
- Compatibility of base change with comparisons → `Coherence.base_change_compatibility`
  with `baseCompactification` (the recorded `ofIsPullback`, quasi-compactness transported):
  correct.
- Restriction to Dbc → fullness of Dbc together with `maps_constructible`,
  `constructible_pull` and `localizing_pull`. The pullback clauses are what make the
  base-change functors land in the stated categories (sk-lem-int-tensor, and Loc by
  exactness and sums). They are implicit in the node's statement: correct.

Edge cases: the empty scheme, the empty and singleton coproducts, the zero complex,
identical compactifications, identity squares, non-literal pullback models, non-dense
compactifications, E = Q_ℓ and ℓ = 2 are all covered. The universes are those of the
site, the coefficients (u+1) and the derived category (u+2). No equality is imposed.

Gates: every definition has real data (abbreviations and explicit mates; the only tactic
block is `letI` inside the `baseChange` construction). The only `sorry` is the theorem
proof. The module and declaration docstrings carry the source place and
`(blueprint: det-prop-int-brown-construction)`. The theorem docstring carries the node's
proof plan, with node steps 3 and 4 merged into its step 3. There is no line over 100
characters and no pro-étale substitute. `lean.statement` is verbatim in the file, and the
node is unchanged except for `lean`.

Searches: besides the worker's, `rg` in the side clone's `lean/` for
`localizingClosure`, `rightDerivedLowerShriekOfCompactification` and `Compactification`
found only the dependency declarations used here and finite/discrete-coefficient
analogues. Nothing states this integral theorem.

Compiler: `nt_compile.py` on the delivered module with the local side overlay passed with
no error or warning (51.3 s and 42.8 s, within the 60 s limit).

Changed: nothing in the Lean or the node; only this section.
