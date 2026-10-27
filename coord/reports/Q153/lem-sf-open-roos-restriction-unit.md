## Worker report

Delivered module: `Sheaf.Paper.SfOpenRoosRestrictionUnit`.
Main declaration: `WeilConjectures.SfOpenRoos.restriction_unit`.
Its only postponed proof is `restriction_unit`. The module includes a Prop-valued
expansion of its conclusion, two actual localization constructions for the adjunction,
and three instances reusing the published restriction exactness data. Definitions have
real data. No statement correction, new node, or dependency interface repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The finite-field datum is `D : FiniteFieldDatum.{t}`. Its fields supply the prime,
  positive exponent, finite field and algebraic closure. `l : ℕ`, `[Fact l.Prime]`,
  `_hl : l ≠ D.p`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` give exactly the coefficient datum in the node.
  The published completed-coefficient sheaves use the valuation ring and its maximal
  ideal powers, canonically the same quotients as any chosen uniformizer powers.
  Thus no additional arbitrary uniformizer or coefficient ring is substituted.
* `X : Scheme.{t}`, `aX : X ⟶ Spec (CommRingCat.of D.k)` and its
  `LocallyOfFiniteType` and `QuasiCompact` instances say that X is finite type over k.
  `U : X.ProEt` with `[IsOpenImmersion U.hom]` presents the open immersion. The same
  two instances for `U.hom ≫ aX` say U is finite type over k. This is the published
  dependency's slice presentation and includes every open immersion in the node.
* `modulesX l E X` and `modulesU l E X U` are the recorded `ringedSiteModules`
  over the actual completed coefficient sheaf and its slice restriction. They are
  ordinary unbounded module categories, with the same Mathlib Abelian structure.
  The module universe `max u (t+1)` contains both the site and the coefficients.
  Site objects and morphisms keep universes t+1 and t; there is no imposed equality.
* `HasDerivedCategory` binders provide ordinary derived localizations for modules and
  strict towers. Independent sizes `wA`, `wB` are retained. `LA`, `LB`, `etaA`,
  `etaB` and `_hLA`, `_hLB` specify total RIGHT derived inverse limits by their
  universal property, rather than an arbitrary functor assumed to have the answer.
* Strict towers are `ℕᵒᵖ ⥤ modulesU` and `ℕᵒᵖ ⥤ modulesX`; index n is positive
  exponent n+1. A tower complex is `CochainComplex (ℕᵒᵖ ⥤ A) ℤ`. Its `.asFunctor`
  evaluates at `op n` and its successor arrow is `(homOfLE (Nat.le_succ n)).op`.
* `extension`, `restriction` and `localizedSystemAdjunction` are the published actual
  ringed-slice functors and normalized adjunction. No variable functor is substituted
  in the main theorem. Exactness and additivity are inherited as instances, not added
  as hypotheses on X or U. The helpers descend this exact adjunction using
  `Adjunction.localization` with the canonical `mapDerivedCategoryFactors` squares;
  the tower helper descends `adj.whiskerRight ℕᵒᵖ` with pointwise exactness.
* The coefficient conclusion is `Nonempty (SfClopenCoefficientRestriction ...
  U.hom.opensRange)`. Despite its historical name this published structure accepts
  EVERY open. Its `finite`, `finite_constant`, `completion`, `projection` and
  `transition` fields express the canonical finite and completed ring identifications,
  identity on constant sections, every quotient projection and transition. Its
  exactness fields retain ordinary restriction. The slice presentation is identified
  with the open site's modules by the recorded weakly-etale localization, exactly as
  in the extension-comparison dependency. No clopen hypothesis is used here.
* `∀ M, IsIso (piComparison (restriction ...) M)` is invertibility of the canonical
  countable-product map. The next conjunct quantifies over every `V : Over U`, every
  section x of the restricted product and every n. It states explicitly that projecting
  the image of x gives `(Pi.π M n).val.app (op V.left) x`. Thus on all section tuples
  the comparison is the identity coordinate identification, not just some isomorphism.
* The next two conjuncts state invertibility of the actual ordinary and descended
  open-adjunction units on every module and every derived object, respectively.
  The ordinary unit is the prescribed summand-injection/sheafification unit of the
  published dependency, section-normalized over the open, not an existential unit.
* `RestrictionUnitAssertions` quantifies jointly over `HA`, `HB`, `chiA`, `chiB`,
  `thetaA`, `thetaB`, `psiJ`, `kappaJ`, `lambdaJ`, `psiG`, `kappaG`, and `rho`.
  The two directions use the SAME models and normalized derived-limit comparisons.
  The HA/HB object equalities specify the shifted cone of `towerTransitionEndomorphism`
  (one minus transition shift). The chi equations fix the actual shift/cone coordinates
  followed by `biprod.map (𝟙 _) (-𝟙 _)`. Thus in degree a=p+1 the coordinates are
  `(P^a,P^(a-1))`, with precisely differential `(dx,(1-s)x-dy)`.
  The two functor-map clauses specify product maps on both signed coordinates.
* The K-injective clauses fix thetaA/thetaB by the inclusion with first coordinate
  the ordinary-limit inclusion and second coordinate zero. These are conclusions
  for all termwise-injective K-injective complexes, not assumptions on an input tower.
  They prevent rescaling a derived comparison and ensure the recorded normalization.
* The psiJ and kappaJ projection formulas and lambdaJ conjugation square render the
  extension comparison of the statement dependency on these same signed models.
  Its strict-augmentation clause uses `(c,0)` on both sides. This does not define a
  second extension functor or a second notion of derived inverse limit; it exposes
  the normalized comparison witnesses whose compatibility is the present statement.
* `rho` is a NATURAL ISOMORPHISM `LB ⋙ G.mapDerivedCategory ≅ towerG ⋙ LA`.
  The psiG projection equation fixes its product comparison, the two kappaG equations
  prescribe restriction on each signed summand, and its conjugation square identifies
  rho with thetaA inverse after kappaG after G(thetaB), including localization factors.
  Thus rho is specified by its signed representative, rather than a bare isomorphism.
* The clause beginning `(restrictionUnitDerivedAdjunction adj).unit.app ...` is
  exactly `rho_(JM) ∘ j^*(lambda_M) ∘ u_(LA M) = LA(u_M)` in Lean's left-to-right
  composition order. The right side uses the actual descended TERMWISE tower unit.
* The following chain-map clause is the same equality before localization:
  `u_(HA M) ≫ G(kappaJ M) ≫ kappaG_(JM) = HA.map(u_M)`.
  Because HA.map is explicitly the product of the level maps on each signed
  coordinate, this is precisely the required product-of-units equality on both summands.
* For EVERY compatible strict augmentation c, the final clause supplies b and bG
  with coordinates `(c,0)` and `(Gc,0)`, asserts `G(b) ≫ kappaG = bG`, and states
  the corresponding actual derived-morphism equality using theta and rho. Together
  with the forward augmentation clause and the chain unit identity, this preserves
  all strict augmentations under the unit comparison. Naturality of rho and the
  coordinate formulas give augmentation-square naturality. The coefficient projection
  and constant-section normalizations retain the quotient-unit special case.
* All complex degrees are integers; no boundedness, tensor factor, constructibility,
  lisse, completeness, clopen, separatedness or connectedness restriction is present.

Dependency declarations read and reused:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the actual coefficient ring,
  valuation ring, maximal ideal, powers and quotient transitions.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`, `integralCoefficientSheafSystem`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`. The scheme-morphism
  convention node introduces no declaration: finite type uses LocallyOfFiniteType
  and QuasiCompact as in the recorded extension comparison.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the existing Mathlib `SheafOfModules` with inherited categorical structures.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory`; `Mathlib.CategoryTheory.Limits.HasLimits`: `Limits.limit`.
* `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: `localizedSystemExact`,
  the six exactness/additivity instances, `localizedSystemRestriction`,
  `localizedSystemExtension`, `localizedSystemAdjunction`. Restriction is literally
  `SheafOfModules.overFunctor` (the localized-ringed-site dependency).
* `Sheaf.Paper.SfOpenRoosExtensionComparison`: `SfOpenRoos.modulesX`, `modulesU`,
  `extension`, `restriction`, `comparison`, and the published normalized formulas.
* `Sheaf.Paper.ExactProductFunctorStrictLimit`: `exactProductFunctorStrictLimit`.
* `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`.
* `Sheaf.CategoryTheory.StrictRoosComparison`: `CategoryTheory.strictRoosComparison`.
* `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.weaklyEtale_localization`.
* `Sheaf.Paper.SfClopenCoefficientComparison`: `sf_clopen_coefficient_comparison`;
  public data module `SfClopenRestrictionData`: `SfClopenCoefficientRestriction`.
* Mathlib proof dependencies `SheafOfModules.hasLimitsOfSize`, `createsLimit`,
  `evaluationPreservesLimitsOfSize`, and
  `Functor.pushforwardContinuousSheafificationCompatibility` are read via the
  recorded matches and available in the imported dependency closures.

Proof docstring follows all six node proof steps: slice coefficient identification;
sectionwise products; exact-product comparison for G; augmentation coordinates;
product projection/unit naturality on both signed summands; conjugation by theta
and cancellation, retaining the augmentations.

Edge cases checked before finalizing: empty open (zero module category and unique
unit/comparison), identity open (actual normalized unit), zero towers, constant and
nonconstant transition towers, positive exponent one (n=0), arbitrary negative and
positive complex degrees, arbitrary augmentation source and zero augmentation,
nonseparated finite-type schemes, independent scheme/coefficient universes and
independent derived localization sizes. No extra hypothesis excludes any of these.

Searches (recorded search service results were present in the resumed sandbox):

* msearch leanfinder: “Restriction of the signed Roos derived inverse limit comparison
  commutes with extension by zero and its canonical adjunction unit”; eight unrelated
  comparison/condensed hits, no match.
* msearch leansearch: “The canonical restriction comparison for the derived inverse
  limit of a tower is compatible with an adjunction unit”; hits include
  `Adjunction.derived_unit`, `derivedη_fac_app_assoc`, no signed Roos/open comparison.
* msearch leanfinder: “Restriction of a normalized signed Roos derived limit comparison
  and compatibility with the open adjunction unit”; general derived adjunction and
  product-comparison hits, no exact statement.
* msearch loogle: `CategoryTheory.Adjunction.unit, CategoryTheory.Limits.piComparison`;
  zero hits (both recorded runs).
* msearch grep: `roos|Roos|restrictAdjunction_unit`; only Mathlib's Zariski module
  restriction-adjunction module, not this pro-etale signed Roos statement.
* rg of project `lean/Sheaf` and upstream `lean/WeilConjectures` for Roos, restriction
  unit and the proposed declaration names: existing general Roos models and the
  published extension comparison; no statement comparing these two normalized
  comparisons with this open unit. Grep of the item id in upstream gives no match.
  Existing related open derived-base-change unit calculations are different statements.
  `dag/lean_names_upstream.json` has no collision with the seven full declaration names.

Validation: scompile.py compiled the final module in sandbox and library mode,
39.0 s and 25.1 s respectively, with no errors or warnings. The statement record
is extracted verbatim from the theorem signature. Only the item's lean field changes.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q153

No second worker was started: the dispatch explicitly prohibits subagents and directs
self-delivery. The maintainer performs the independent review. During the worker's
own rereading against the node, the identity-on-sections clause of the product
comparison was made explicit as a projection equality for every slice object and
section, and the strict-Roos proof dependency was imported directly. Both derived
localization helpers were checked to retain independent universe levels and to use
exactly the published adjunction and canonical localization squares. The coefficient
structure was checked to require no clopen hypothesis despite its historical name.
