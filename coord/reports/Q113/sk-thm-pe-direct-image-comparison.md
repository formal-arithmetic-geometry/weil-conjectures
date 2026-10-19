## Worker report

The saved packet has been retained and repaired against the current source and DAG.
Its initial dry run failed because `lean.statement` contained the final `:=`, whereas
preflight compares the signature ending before that token. The metadata now copies the
signature verbatim with that delimiter excluded. The mathematical self-check also repaired
omissions in the saved Lean statement: exactness at Y, the unbounded comparison, pullback
identity/composition, explicit derived unit/counit equations, and the qcqs scope of the
classicality consequence. The natural-language node has not changed: “In particular” remains
under the preceding qcqs hypotheses, as in proof step 5. No `statement_change` is required.
The saved second-reading section was removed because the separate second reader must now
read the amended packet.

The file `lean/Sheaf/AlgebraicGeometry/ProEtaleDirectImageComparison.lean` contains the theorem
`AlgebraicGeometry.ProEtale.directImageComparison` with proof `sorry` and one helper,
`AlgebraicGeometry.ProEtale.directImageComparisonPullbackPlusIso`, with real data. The helper
composes the existing exact-functor composition isomorphisms and the localization of the
canonical sheaf comparison. It introduces no new inverse image or arbitrary choice.
The module and declaration docstrings identify the source and all six DAG proof steps.

The correspondence of every hypothesis and clause is as follows:

- The discrete commutative coefficient ring is `(Λ : Type u) [CommRing Λ]`.
  Schemes are `{X Y : Scheme.{u}}` and their arbitrary morphism is `(g : X ⟶ Y)`.
  The fixed-module sheaf encoding uses `ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)`;
  the intrinsic module encoding uses the same lifted constant ring via the recorded
  `Scheme.proEtaleDerivedCategory`. No finite, torsion, properness or constructibility
  assumption is present.
- The square of topoi is the existing `comparisonCoefficientDirectImageIso` for set
  sheaves, constructed from `comparisonSiteBaseChangeIso` on the actual fibre products.
  For coefficients, `comparisonUpperStarCompUpperStarIso` has the displayed orientation
  `ν_Y^* ⋙ g_Proet^* ≅ g_Et^* ⋙ ν_X^*`. The theorem's pullback identity and composition
  clauses use that specified isomorphism, rather than quantifying over a replacement.
- Exactness of each of the four inverse images is expressed by eight conjuncts:
  `PreservesFiniteLimits` and `PreservesFiniteColimits` for `comparisonUpperStar ... X`,
  `comparisonUpperStar ... Y`, `Etale.upperStar ... g`, and `ProEtale.upperStar ... g`.
- The unbounded assertion is `IsIso` of the hom of the explicit composite
  `mapDerivedCategoryCompIso.symm ≪≫ mapDerivedCategoryNatIso c ≪≫
  mapDerivedCategoryCompIso`, where c is the canonical sheaf comparison. Its source is
  `ν_Y^*.mapDerivedCategory ⋙ g_Proet^*.mapDerivedCategory`, and its target is
  `g_Et^*.mapDerivedCategory ⋙ ν_X^*.mapDerivedCategory`. This is localization of the
  specified comparison and its inverse; no arbitrary `Nonempty` choice is used.
- The pullback identity clause quantifies over every scheme U and every etale module sheaf
  F; its two paths use `comparisonUpperStarCompUpperStarIso`, `Etale.upperStarId`, and
  `ProEtale.upperStarId`. The pullback composition clause quantifies over every composable
  f : U ⟶ V, h : V ⟶ W and every F on W_et, and compares the two paths through
  `Etale.upperStarComp`, `ProEtale.upperStarComp`, c_f, c_h, and c_(f ≫ h).
  Applying the exact-functor localization to these equalities yields their derived versions.
- `QuasiCompact g → QuasiSeparated g → IsIso (comparisonDirectImageCanonicalMate ... g)`
  asserts invertibility of precisely the canonical natural transformation on D+.
  D+ objects are the existing `DerivedCategory.Plus` of the etale module-sheaf category;
  the natural transformation's type already includes both functors and every bounded-below
  object, with no single-object specialization.
- Write c for `directImageComparisonPullbackPlusIso`, beta for
  `comparisonDirectImageCanonicalMate`, G = ν_Y^*, H = ν_X^*, L1 = g_Et^*,
  L2 = g_Proet^*, R1 = Rg_Et,*, and R2 = Rg_Proet,*.
  The unit clause quantifies over every A in D+(Y_et,Λ) and states
  `G(η1_A) ≫ beta_(L1 A) = η2_(G A) ≫ R2(c_A)`.
  The counit clause quantifies over every B in D+(X_et,Λ) and states
  `L2(beta_B) ≫ ε2_(H B) = c_(R1 B) ≫ H(ε1_B)`.
  The units and counits are those of the recorded inverse-image adjunctions, passed through
  the existing `Adjunction.derivedAdjunctionPlus`, so their normalization is fixed.
- The derived direct-image identity clause quantifies over every U and every L in D+(U_et,Λ)
  and compares beta for `𝟙 U` with the canonical derived identity identifications.
  The derived composition clause quantifies over all composable f,h and every L, and compares
  beta_(f ≫ h) with the two whiskered comparisons using
  `etaleComparisonDirectImageCompIso` and `proEtaleComparisonDirectImageCompIso`.
  These are equations for canonical maps, valid even before imposing qcqs invertibility.
- The final implication has `QuasiCompact g → QuasiSeparated g →` and quantifies over
  every `M : Scheme.proEtaleDerivedCategory X Λ`. Its lower-bound hypothesis is
  `∃ n : ℤ, DerivedCategory.IsGE M n`; its classicality hypothesis is
  `IsClassicalComplex (X := X) Λ M`. The conclusion is classicality of
  `(Scheme.proEtaleConstantDerivedDirectImage g Λ).obj M` at Y. The existing predicate
  quantifies over all integer-degree cohomology sheaves and all affine presentations.

All statement dependencies were checked against their current records and source signatures:

- `def-weil-pbc-site-comparison-morphism`: module
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, declarations
  `AlgebraicGeometry.Scheme.proEtaleSiteComparison`,
  `preservesFiniteLimits_proEtaleSiteComparison`, and `proEtaleSiteComparisonModules`.
  The set construction is unrestricted; its recorded finite-module specialization does not
  impose a finiteness assumption on this node's general `ModuleCat` construction.
- `def-weil-pbc-inverse-image`: module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, declarations
  `AlgebraicGeometry.Etale.upperStar` and `upperStarLowerStarAdjunction`.
- `def-weil-proetale-inverse-image`: module
  `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`, declaration
  `AlgebraicGeometry.Scheme.sfIntrinsicConstantModuleAdjunction` and its reexported
  general ring-sheaf constructions. Its finite realization specialization is not used to
  restrict the arbitrary-ring theorem; the fixed-module functors are the reexported
  `AlgebraicGeometry.ProEtale.upperStar` and `upperStarLowerStarAdjunction`.
- `def-weil-pbc-proetale-operations`: the current record is module
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, declaration
  `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback`, with arbitrary-ring
  pullback, pushforward and adjunction. That module is imported. The final conclusion uses
  the existing canonical sectionwise direct image and its unbounded right-derived functor
  from `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`.
- `def-weil-pbc-derived-categories`: module
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`, the reexported
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory`, and
  `DerivedCategory.Plus`. Its current server source was read with `scompile.py --source`
  because that exact module is absent in the older local checkouts.
- `sk-def-pe-classical-definition`: module
  `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`, existing `IsClassical`,
  `IsClassicalModule`, `IsClassicalCochainComplex`, and its derived specialization
  `AlgebraicGeometry.ProEtale.IsClassicalComplex`.
- `def-weil-pbc-direct-image`: module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, declaration
  `AlgebraicGeometry.Etale.lowerStar` and its existing right-derived-plus interface.
- `def-weil-pbc-constant-sheaf`: module `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  declaration `CategoryTheory.constantSheaf`, sheafification of the constant presheaf.

Edge cases checked: identity and composites containing identities are explicitly quantified;
zero coefficients, the zero complex and empty schemes add no assumptions; arbitrary integer
lower bounds are allowed; the two qcqs hypotheses affect the comparison's invertibility and
its classicality consequence, while exactness and map coherence remain unconditional.
The constant-ring universe lift agrees with both recorded module encodings.

The earlier packet's three kinds of search are retained as evidence: LeanFinder via
`msearch.py` for the qcqs etale/proetale bounded-below derived direct-image comparison
returned generic scheme-module pseudofunctor and sheafification declarations; Loogle and
LeanSearch queries about the canonical mate returned `CategoryTheory.mateEquiv` machinery;
Mathlib grep for `comparison.*[Pp]ushforward|[Pp]ushforward.*comparison|[Pp]ro[Ee]tale.*[Dd]erived`
found no exact theorem. The earlier project searches found the canonical comparison
framework but no theorem with all of this node's clauses.

Additional repair searches used `rg` over the shared `lean/Sheaf` tree and the prescribed
upstream source for `mapDerivedCategoryPlusNatIso`, `mapDerivedCategoryPlusCompIso`,
`comparisonUpperStarCompUpperStarIso`, the proposed helper name and the item id. There is
no existing bounded-below comparison helper of this exact type. The nearby
`properOpenSiteExtensionIso` compares extension by zero, a different functor. An existing
unbounded helper `mapDerivedCategoryComparisonUpperStarCompUpperStarIso` was found in
`WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover`. Importing it with the required
intrinsic dependency failed on the duplicate declaration `upperStarIsoLowerStarInv` in
legacy and finite-coefficient `UpperLowerStar.Iso`. The delivery therefore states the
unbounded clause using the generic localization expression directly and defines no
second unbounded helper. A fresh `msearch.py` Loogle query
`CategoryTheory.Functor.mapDerivedCategoryPlusNatIso, CategoryTheory.Functor.mapDerivedCategoryCompIso`
returned zero hits with “unknown identifier” for the project-specific first name; the full
signatures were read directly from the upstream exact-functor source.

No new DAG node or dependency-module repair was needed. No `STATEMENT-DISPUTED` issue or
unit-statement correction was found. The only postponed theorem is `directImageComparison`.

## Second reading by Q113

I read the node statement, the blueprint section (order 730), Stacks Tag 09A6, every
statement dependency, and the complete Lean signature. The correspondence is as follows.

* The objects are a discrete commutative ring `Λ`, schemes `X`, `Y`, and a morphism
  `g : X ⟶ Y`; Lean renders these as `(Λ : Type u) [CommRing Λ]`,
  `{X Y : Scheme.{u}}`, and `g`. The module-category coefficients are the canonical
  `ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)` encoding used by the dependency modules.
* The topoi square and its inverse-image comparison are rendered by
  `comparisonUpperStarCompUpperStarIso`; its orientation is exactly
  `g_Proet^* ν_Y^* ≅ ν_X^* g_Et^*`. The identity and composition equations quantify
  over every scheme, composable pair, and sheaf and use the specified identity and
  composition isomorphisms.
* The four exact inverse images are the eight `PreservesFiniteLimits`/
  `PreservesFiniteColimits` conjuncts for comparison pullback at `X` and `Y`, and
  `Etale.upperStar g` and `ProEtale.upperStar g`. No finiteness or qcqs assumption is
  attached to these clauses.
* The unbounded derived comparison is the `IsIso` conjunct for the hom of the explicit
  localized composite `mapDerivedCategoryCompIso.symm ≪≫ mapDerivedCategoryNatIso ≪≫
  mapDerivedCategoryCompIso`, so it is the specified comparison and its inverse, rather
  than an arbitrary isomorphism.
* The qcqs clause is exactly `QuasiCompact g → QuasiSeparated g → IsIso` of the
  canonical `comparisonDirectImageCanonicalMate`; its source and target are the
  bounded-below derived categories, hence it quantifies over every `K` in `D+`.
* Unit and counit compatibility are the two displayed universal equations over every
  bounded-below object, with the units/counits of the recorded etale and pro-etale
  adjunctions and with the pullback comparison above. Derived direct-image identity and
  composition are the final two coherence conjuncts, quantified over every `U`, every
  composable `f,h`, and every bounded-below complex.
* The final “in particular” is under the same qcqs hypotheses and quantifies over every
  `M : Scheme.proEtaleDerivedCategory X Λ`; Lean includes both an arbitrary integer lower
  bound and `IsClassicalComplex` and concludes classicality after
  `Scheme.proEtaleConstantDerivedDirectImage g Λ`, matching the node's bounded-below
  classicality consequence.

Edge cases were checked explicitly: identity maps and composites containing identities,
zero rings and zero complexes, empty schemes, and lower bounds at any integer (including
`n = 0`). No clause introduces a nonemptiness, finiteness, properness, Noetherian, or
characteristic hypothesis; the qcqs assumptions occur only where Tag 09A6 requires them.
The coefficient and site universe lift is the one used by `proEtaleDerivedCategory` and
`IsClassicalComplex`, so no coefficient universe is silently identified with a different
site universe.

I searched the shared `lean/Sheaf` tree and `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`
with `rg` for the item id, `directImageComparison`,
`comparisonUpperStarCompUpperStarIso`, `mapDerivedCategoryPlusNatIso`, and
`mapDerivedCategoryCompIso`; I also reran the prescribed `msearch.py` LeanFinder/Loogle
queries and grepped Mathlib for pro-etale/direct-image comparison names. The hits were
generic comparison, mate, or underived direct-image infrastructure; no declaration states
this theorem or its full collection of clauses. The recorded dependency declarations were
opened and match their node signatures, so no dependency repair or new definition node is
needed.

No mismatch was found. I changed no Lean source and no node field. Compilation with
`scompile.py Q113 sk-thm-pe-direct-image-comparison` succeeds for the module (the only
postponed proof is the named theorem `directImageComparison`), and the existing dry run
passes the maintainer preflight apart from this required second-reading section.
