## Worker report

Item: `lem-pur-etale-sum-composition-counit`.
Module: `Sheaf.AlgebraicGeometry.EtaleSumCompositionCounit`.
Main declaration: `AlgebraicGeometry.Etale.etaleSumCompositionCounit`.

The module states the derived counit equation and its adjunction-conjugacy consequence.
It also explicitly states the sheaf fold evaluation, its localization on arbitrary
unbounded complexes, and the nested-summand normalization of the sum compositor.
All four theorems have `sorry` as their entire proof, with natural-language proof plans
and this item's blueprint tag. No definition contains postponed data or a new proof hole.
The original node is unchanged except for `lean`.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Finite commutative ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]` in every theorem. The coefficient universe is the existing six-functor convention. |
| Noetherian schemes U, X, T | `{U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]`. Mathlib's `IsNoetherian` is locally Noetherian plus compact, equivalently the finite affine cover by spectra of Noetherian rings required here. |
| Composable separated etale morphisms of finite type | `(e : U ⟶ X) (v : X ⟶ T) [Etale e] [Etale v] [IsSeparated e] [IsSeparated v] [QuasiCompact e] [QuasiCompact v]`. Etale supplies locally finite presentation and locally finite type, so quasi-compactness gives exactly finite type. The composite instances are inferred. |
| Constant-A sheaves on small etale sites | `Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)`, exactly the encoding in the recorded derived-category and sum-extension dependencies. |
| Ordinary unbounded derived categories | `DerivedCategoryModule A Y`, the existing abbreviation for `DerivedCategory` of that sheaf category. There is no boundedness, constructibility, invertible-characteristic, or compactification hypothesis. |
| L_a is sheafified sum extension | The existing `etaleLowerShriek (ModuleCat.{u + 1} A) a inferInstance`. Its source defines it as left Kan extension along the small-site localization, then sheafification. No second sum-extension definition is introduced. |
| S_a = D(L_a), exact restriction, and S_a adjoint to a* | `.mapDerivedCategory` of that existing functor, `(upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategory`, and the existing `derivedEtaleLowerShriekUpperStarAdjunction`. Exactness instances are existing; its definition localizes the termwise sheaf adjunction. |
| Sheaf counit sends i_s(x) to x | `etaleSumCounit_summand`: the inverse of `upperStarIsoLocalizationRestriction` identifies N(W) with the inverse-image section, the restriction-adjunction unit inserts the summand, and the sheaf counit returns it to N(W). Their composite is the identity linear map. Every lift is covered by `(W : U.Etale)`; the corresponding X-object is explicitly `(Over.map ...).obj W`. |
| Derived counit is degreewise evaluation localized on every unbounded complex | `etaleSumCounit_localization`, with arbitrary `K : CochainComplex ... ℤ`. It writes both `mapDerivedCategoryFactors` comparisons, then `DerivedCategory.Q.map` of the termwise sheaf counit, equal to the specified derived counit at `Q.obj K`. |
| The specified nested-sum sigma | `etaleSumSheafCompIso` is constructed by composing the two sum/restriction adjunctions, transporting the right side along literal site restriction composition, and applying `Adjunction.leftAdjointUniq`. This is the universal map out of the two sums, not a choice of an unrelated isomorphism. `etaleSumSheafCompIso_summand` explicitly states that the successive structural inclusions followed by this map equal the single inclusion, with `Over.mapComp` transport. This is precisely the final normalization clause of `quasifiniteCompactSupportExact`, after identifying its support functors with sum extension. |
| Sigma is descended termwise | `derivedEtaleSumCompIso`: inverse `Functor.mapDerivedCategoryCompIso`, then `Functor.mapDerivedCategoryNatIso` of the sheaf sum compositor. |
| Kappa is canonical sheaf pullback composition descended termwise | The existing `unboundedEtaleUpperStarCompIso A e v`. Its body is exactly `mapDerivedCategoryNatIso (upperStarComp ...)` followed by `mapDerivedCategoryCompIso`. This is the declaration named in the note of `def-pur-etale-exact-pullback-unit-composition-comparisons`. |
| For every K, ev_ve sigma = ev_v S_v(ev_e) S_v S_e(kappa) | The first conjunct of `etaleSumCompositionCounit`, with `(∀ K : DerivedCategoryModule A T, ...)`. Lean's `≫` orders composition from left to right, giving sigma then ev_ve, versus S_v S_e(kappa), S_v(ev_e), then ev_v. |
| Composite adjunction | The `.comp` of the two existing derived sum/pullback adjunctions. Its left functor is S_e followed by S_v; its right functor is v* followed by e*. |
| Adjunction conjugate of sigma equals kappa, with direction (ve)* to e*v* | The second conjunct is `conjugateEquiv adj_ve (adj_e.comp adj_v) (derivedEtaleSumCompIso A e v).hom = (unboundedEtaleUpperStarCompIso A e v).hom`. This is equality of natural transformations, not only existence of an isomorphism. |

Helpers `etaleSumRestrictionCompIso`, `etaleSumSheafCompIso`, and
`derivedEtaleSumCompIso` are concrete canonical comparisons belonging to this item's
specified sigma. They use only existing constructions and are listed in `lean.declarations`,
as allowed for missing canonical-map helpers. They do not choose data from a mere existence
or `Nonempty` theorem and do not define sigma as the conjugate of the kappa appearing in
the conclusion. No new independent notion or dependency repair is needed.

Dependencies read and used (full names below omit no namespace except where explicitly noted):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`; the geometric hypothesis uses Mathlib's existing `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`, with its finite affine cover characterization.
- `def-weil-scheme-morphism-properties`: its convention record fixes no declaration; `AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` are the collected Mathlib notions.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, and its public dependency `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `def-weil-pbc-etale-sum-extension`: `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`, `AlgebraicGeometry.Etale.etaleLowerShriek` and `etaleLowerShriekUpperStarAdjunction`.
- `def-weil-presheaf-modules-sheafification`: `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, `PresheafOfModules.sheafification` and its adjunction. Publicly imported as the recorded sheafification dependency; the concrete constant-coefficient functor already implements the equivalent ModuleCat-valued sheafification.
- `lem-amb-etale-adjoint-locality`: `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`; `AlgebraicGeometry.Etale.derivedEtaleLowerShriekUpperStarAdjunction` is now defined upstream in `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection`, which is also publicly imported. The full unbounded exact adjunction, not the bounded-below Plus adjunction, is used.
- `prop-weil-pbc-inverse-image-modules-exact`: `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, `AlgebraicGeometry.etaleInverseImageModulesExact`, imported for the proof plan; inverse image in the statement is the existing constant-coefficient `upperStar`.
- `lem-weil-pbc-etale-inverse-image-restriction`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction` and `localizationRestrictionLowerStarAdjunction`. Despite its module path, the localization comparison is for every etale morphism and requires no open-immersion hypothesis.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and `DerivedCategory.Q`, available through the imported derived modules.
- `lem-sfb-quasifinite-compact-support-exact`: `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`, `AlgebraicGeometry.Etale.quasifiniteCompactSupportExact`, imported for its final nested-summand normalization and the proof plan. Its existential support-functor witnesses are not used to choose arbitrary data.
- `def-pur-etale-exact-pullback-unit-composition-comparisons`: `AlgebraicGeometry.Etale.unboundedEtaleUpperStarCompIso` from `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`, exactly the second owning module named in the dependency's record. Its recorded top-level module `EtaleSumRightAdjointCoherence` is a consumer of this item; importing that module just to obtain this earlier definition would create a proof-import cycle, so the actual owning module is imported directly. This item does not use the other declaration `etaleSumPullbackUnitIso`.
- `def-weil-pbc-composite-adjunction`: Mathlib match `CategoryTheory.Adjunction.comp` in `Mathlib.CategoryTheory.Adjunction.Basic`, with its `comp_counit_app` formula.
- `def-weil-pbc-adjunction-conjugate`: Mathlib match `CategoryTheory.conjugateEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates`.
- Proof-only nodes `lem-weil-pbc-exact-functor-derived-factorization` and `lem-weil-pbc-localization-universal-property`: `Functor.mapDerivedCategoryFactors` in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and `CategoryTheory.Localization.natTrans_ext` in `Mathlib.CategoryTheory.Localization.Predicate`.

Source check: read the local Stacks source at `etale-cohomology.tex`, definition-extension-zero,
equation-j-p-shriek, exercise-jshriek-direct, proposition-describe-jshriek (03S3/03S5),
and `more-etale.tex`, lemma-f-shriek-composition (0F50). Read the current blueprint
`latest/blueprint/sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md`,
Step 1, and `latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.md`.
The sum/evaluation calculation is the node's finer split of that source argument.

Edge cases checked before and during writing:

- Zero coefficient ring is allowed: no nontriviality or cardinality condition is added.
- Empty schemes, empty sets of lifts, and zero sheaves are allowed. The sheaf sum functor
  handles empty sums; no chosen lift or nonempty indexing assumption occurs.
- Identity morphisms remain covered. The comparison is induced by literal restriction
  and the canonical site-composition isomorphism, not a noncanonical scalar automorphism.
- A section over any small-etale object and any lift is tested by a U-etale object W.
  The statement makes no claim that every sheafified section is globally a sum generator.
- K is completely unbounded, and the complex normalization allows every integer degree.
  No passage to bounded-below representatives or resolutions occurs.
- The three schemes have the same standard scheme universe u, while coefficients and
  module values use u+1 as in the recorded derived-category declaration. No new equality
  of object and morphism universes or small-site substitution is introduced.

Searches for existing notions and statements (2026-10-24):

- `msearch.py`, LeanFinder: "The composition comparison of etale sum extension functors
  preserves evaluation counits and is conjugate to pullback composition". Eight hits,
  including `PresheafOfModules.pullbackComp` and generic locally Cartesian closed
  pullback/counit results. None states the small-etale sum counit identity.
- `msearch.py`, Loogle: "CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.comp".
  Twelve hits, including generic whiskering/associator conjugation, and module-sheaf
  pullback composition. These provide categorical tools, not the specified etale sum map.
- `msearch.py`, grep in CategoryTheory: `conjugateEquiv.*counit|comp_counit_app`.
  Sixteen hits, including `conjugateEquiv_counit` and `comp_counit_app`, used as the
  generic definition/formula dependencies rather than a duplicate of this statement.
- `msearch.py`, LeanSearch: "etale extension by zero composition counit sum restriction
  adjunction". Eight hits, mostly algebraic change-of-rings counits plus generic
  adjunction composition/localization; no exact match.
- `rg` in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for the seven delivered
  declaration names: no existing declarations. Searches for `etaleLowerShriek.*Comp`,
  `Comp.*etaleLowerShriek`, `etaleSumComp`, `sumComposition`, and the item's blueprint id
  found the existing adjunction and the consumer's compact-support coherence theorem,
  but no actual sum compositor with this counit theorem. The consumer's theorem has
  different compact-support right adjoints and is not the present assertion.
- Read the generic `sheafPushforwardContinuousComp'`, `Over.mapComp`, and
  `Adjunction.leftAdjointUniq` APIs to assemble the missing canonical helper from
  existing notions. No independent new definition node is needed.

Validation: `scompile.py Q84 lem-pur-etale-sum-composition-counit` compiled the module in
sandbox and library module modes with no errors or warnings. The first attempt found
continuous-functor instance synthesis through the `smallEtaleTopology` alias; the body
now uses the equivalent explicit `smallGrothendieckTopology @Etale`, exactly as upstream.
The final nested-summand statement also compiles cleanly. All variables and the universe
are explicit, `autoImplicit` is disabled, all Lean lines are at most 100 characters.
No statement correction, disputed statement, new nodes, or dependency modules.

## Second reading by Q84

No second reading by another worker: the dispatcher brief explicitly prohibits starting
other agents. The maintainer's independent review reads this delivery. During a separate
self-check I compared every hypothesis and clause with the node and rechecked composition
directions, the conjugate argument order, and the two localization-factorization arrows.
The original draft had only a prose description of the nested-summand normalization;
I added `etaleSumSheafCompIso_summand` so that normalization is an explicit Lean statement.
I also checked that the pullback compositor is imported from its actual earlier owning
module instead of the consumer `EtaleSumRightAdjointCoherence`, avoiding an import cycle.
