## Worker report

The delivery states `WeilConjectures.PurIntegralRepresentingPair.reconstructedRepresentingPair`
in `Sheaf.Paper.PurIntegralRepresentingPair`. Its proof remains `sorry`; the new comparison node has its own two named
normalization/uniqueness statements, each with a complete proof docstring and `sorry`.
The helpers have actual data; they only conjugate existing coefficient functors,
paste recorded natural isomorphisms, or bundle this node's hypotheses and clauses.
The conclusion is `Nonempty (PublishedFamily ... R M hD)`, which supplies a representing pair
for each supplied input, not a global integral exceptional functor.

Source read: current `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction.proof.md`, especially
the three Hom equivalences and the final unit/counit paragraph; the item's entire
seven-step refinement was also read. The inherited source field is unchanged.

Hypotheses and objects, in the order of the node:

* The two primes are `l`, `[Fact l.Prime]`, `p`, `[Fact p.Prime]`, and `_hpl : p ≠ l`.
  The field and characteristic are `k`, `[Field k]`, `[CharP k p]`. Scheme structure
  maps are `X.Over`, `Y.Over`; `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`
  give separated finite type schemes. `[f.IsOver ...]` is the k-morphism condition.
* `E`, `NormedField E`, `NormedAlgebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E` use the
  dependency's finite-extension coefficient setting. Its valuation ring and chosen
  uniformizer are reused as `integralExceptionalIntegers l E` and
  `integralExceptionalUniformizer l E`. The ULift only adjusts the coefficient-value
  universe; `integralExceptionalQuotient` is the identity on residue classes.
  Index `n : ℕ` denotes the positive exponent `n+1`, including the first quotient.
  The norm is the finite extension's compatible p-adic norm, not a new geometric
  hypothesis. All quotient and scalar maps are the dependency's ones.
* `c : Compactification f` supplies the open immersion and proper factor. `S` is
  `StrictEtaleCompactSupport` and `G` is its actual `EtaleTowerBrownAdjunction`.
  `H`, `D` and `hD : BrownTowerComparison.Transport ...` specify the finite/site
  transport supplied by the recorded Brown theorem. They include actual derived
  functors, counits, evaluation and proper/open comparison, not arbitrary endpoint maps.
* The system categories are the existing ordinary `DerivedCategory (ProSystem ...)`.
  `D.siteX.proEvaluation` and `D.siteY.proEvaluation` give exact evaluations and
  semilinear quotient transitions. The etale categories, componentwise exactness,
  finite functors and derived proper/open functors are retained in `S`, `G`, `H`, `D`.
* `CondensedERealization.Integral l E T` is the published full integral constructible
  category. `PurIntegralSupportComparison.coordinates` is
  `integralExceptionalCoordinates.mapDerivedCategory`
  viewed as an equivalence with the Brown API's standard localization.
  `reduction`, `totalLimit`, `adjunction` are the published coefficient model,
  reduction/total-limit adjunction, and exact quotient coordinates composed together.
  Their units and counits are the actual composite-adjunction maps.
* `support` is the reduction, `D.compact.functor`, total-limit composite, and `alpha`
  is exactly the corresponding counit. The uniquely normalized `PurIntegralSupportComparison.beta` and
  explicitly pasted `supportPresentation` identify this expression with the dependency's
  `CompactSupportCondensedRealization.rawSupport`. `Pair.support_integral` restricts
  it to the integral category. `Pair.alpha_iso` asserts invertibility of this actual
  alpha, never replacing it by an undetermined isomorphism.
* `L : Integral l E Y` is the fixed input; its levels are evaluation of `reduction L`.
  `brown` is literally `D.siteY.direct ⋙ G.right ⋙ D.siteX.inverse`, so N is the
  specified bounded-below transported Brown output.
* `Supplied.system` is the supplied ordinary derived system. `normalized` is the
  recorded derived normalization predicate, `bounds` is one finite interval for
  all n, and `constructible` uses intrinsic fixed-module pro-etale constructibility
  of every cohomology sheaf after the specified level realization.
* `Supplied.phi` gives each exceptional-image isomorphism. `exceptionalLevel` is the
  recorded finite right adjoint transported by the actual level site functors;
  `finiteCoordinates` pastes `inverseLevel`, `H.finiteRight` and `directLevel`, so
  these are the dependency's finite exceptional images in ring-sheaf coordinates.
  `transition` says exactly that the phi maps, after the canonical Brown evaluation
  comparison, commute with the actual semilinear quotient transitions.
* `Supplied.recognition` is a sum: either the actual system iso together with its
  evaluation equations, or an integer r and degree-r lower and upper bounds for
  every level. No system iso is assumed in the second summand.
* `Supplied.integral` says the actual total limit is integral constructible;
  `reductions` says its canonical counit reductions are isomorphisms. `Supplied.object`
  is precisely that total limit with this property, with no choice of another object.

Conclusions, clause by clause:

* `Pair.theta` and `theta_evaluation` give the actual system isomorphism and all phi
  identifications. `SingleDegreeNormalization` preserves the specified theta in
  the first summand. In the second, it expresses theta through the H^r-system iso
  and two single-degree identifications whose induced H^r maps are identities.
  This characterizes the functorial good-truncation identifications, without choosing
  an arbitrary quasi-isomorphism. `Family.single_degree_square` gives the actual
  system square from level squares for two systems concentrated in the same r.
  It also applies if a concentrated system used the first recognition summand.
* `Pair.origin`, `normalized`, `finiteTor`, `lowerBound`, `unit_iso` are conclusions
  checking the domains of the Brown and reconstruction formulas. They are not
  extra assumptions on a supplied input. In particular the exceptional common
  lower bound follows from `Supplied.bounds` and the phi isomorphisms.
* `Pair.hom` is an R-linear equivalence for every integral K, using `PbcIntegralRing`
  and the published Hom module structures. The target Hom is the ambient Hom of
  the same full integral category, with `support_integral` recording membership.
  `hom_natural` is contravariant naturality for every K' -> K.
* `Pair.hom_formula` expands the equivalence into the actual adjunction unit,
  total-limit map, alpha, reduction of h, the actual counit at the supplied system,
  theta and `D.counit`, followed by the inverse of the actual unit at L.
  `transpose` takes the proved-in-conclusion `IsIso` witness for this inverse;
  it does not posit another inverse or use an arbitrary map.
* The trace is `hom A.object (𝟙 A.object)`. `trace_reduction` asserts the full
  ordinary-system equality `R(t) = alpha ≫ F(e) ≫ F(theta) ≫ epsilon`.
* `trace_evaluation` says exactly `t_n = epsilon_n F_n(phi_n)` with all coordinate
  identifications displayed: evaluated alpha and reconstruction counit, the proper/
  open evaluation comparison, F_n of the phi map and `finiteCoordinates`, then
  `finiteCounit`. The latter is defined by compact-support site comparison, the
  actual ordinary finite-etale adjunction counit, and the site-adjunction counit.
  `finite_etale_bound` supplies the bounded-below condition for that specified
  comparison as a conclusion. Thus epsilon_n is not a name for an arbitrary map.
* `Family.hom_natural` and `trace_natural` quantify over an integral input map b and
  an actual supplied system map a commuting with theta and Brown(b), with the
  reconstructed map explicitly `totalLimit.map a`. These give the two last
  naturality claims. No assertion of levelwise faithfulness is used for general
  derived morphisms, and no global integral right adjoint is assumed.

Dependency declarations read and reused:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the coefficient integers/uniformizer.
* `WeilConjectures.Compactification.RefinementCategory`: `Compactification`.
* `Sheaf.Paper.CoefficientSystemDerivedComparison`:
  `SheafOfModules.coefficientSystemDerivedComparison`, and its system categories.
* `Sheaf.Paper.IntegralUniformCoefficient`: `Scheme.pbcBoundedConstructibleComplete`;
  `CondensedERealization.Integral` is the existing full-category presentation.
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.CoefficientDerivedSystemCalculus`, reduction, actual adjunction,
  `coefficientSequenceLimit` and the normalized system calculus.
* `Sheaf.Paper.CompactSupportCondensedRealization`: `rawSupport`, `IntegralModel`,
  `integralSupport`, `reconstructedSystem`, `alpha`, and `systemSupport`.
* `Sheaf.Paper.BrownTowerFiniteSiteComparison`: `brownTowerFiniteSiteComparison`,
  and its public `Site`, `FiniteEvaluation`, `TransportData`, `Transport` interfaces.
* `Sheaf.Paper.FiniteCoefficientAdjointComparisons`: `lower`, `upper`, `nu`, `rnu`,
  `AdjointDatum`, its actual finite counit normalization. `ordinaryFiniteRight` and
  `ordinaryFiniteAdjunction` use that same selected etale right adjoint without
  introducing unnecessary Noetherian typeclass binders in the clause helpers.
* `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
* `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` and
  `Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization`:
  `DerivedCategory.singleFunctor`, `homologyFunctor`, their canonical comparison,
  and the identity-on-cohomology good-truncation normalization.
* Added landed dependencies `def-pur-adic-exceptional-system-realization`:
  `Sheaf.Paper.IntegralExceptionalInverseImage`, `integralExceptionalCoordinates`,
  its quotient-ring equivalence and equivalence/additivity properties; and
  `def-pur-completed-coefficient-presentation-transport`:
  `Sheaf.Paper.CompletedCoefficientPresentationTransport`, with
  `WeilConjectures.purCoefficientModel` from
  `Sheaf.Paper.IntegralCoefficientCompletenessTransport`.
  These are added to stmt_deps; neither existing node is changed.
* Proof imports: `PurIntegralReductionUniformTor`,
  `PurNormalizedReconstructionAdjunctionCalculus`, `ExactDerivedCohomologyCoherence`,
  `RoosIntrinsicCompletenessEquivalence`, in the modules named by the proof nodes.

Edge checks: the zero supplied system and zero L cause no nonzero hypothesis;
empty schemes and identity compactifications are permitted; r is any integer,
including negative r; n=0 is exponent 1, not the zero coefficient stage; no smoothness
or relative dimension is introduced; a general degree interval does not imply
faithfulness of evaluations, and this is not assumed; both recognition alternatives
remain available. The exact category and localization universes were read before
changing instance priorities. The priority change selects the Brown derived API,
not a new derived category or an equality between independently given universes.

Searches: `msearch.py leanfinder` with "Integral representing pair reconstructed
from a supplied exceptional system reduction total limit adjunction" returned eight
abstract lifting/limit adjunction results, no match. `loogle` with
`Adjunction.homEquiv, LinearEquiv` reported unknown unqualified identifier; the
qualified `CategoryTheory.Adjunction.homEquiv` retry gives the generic adjunction
API, not this theorem. `leansearch` with "A supplied normalized exceptional
coefficient system reconstructs an integral representing pair by the reduction and
inverse limit adjunction" returned eight generic adjunction/limit results, including
`Adjunction.corepresentableBy`, no match. Mathlib grep
`representingPair|reconstructedRepresenting|integralRepresenting` returned no match.
The same project searches in `WeilConjectures` and `Sheaf` found only
`forgetful_representingPair_rightMate`, a different abstract mate assertion; searching
the item id in `WeilConjectures` found nothing. Existing coefficient coordinates and
reconstruction definitions were found and reused. The returned delivery revealed the missing canonical proper/open coordinate
comparison; the new definition node below now owns it.

Validation: all compiles used the prescribed `scompile.py`. The final full server
compile succeeded in 58.6 seconds, with only the expected sorry warning. The local
wrapper's library attempt timed out, and its automatic current-server-source
confirmation succeeded; no limit was raised. The `deliver2.py --no-push` dry run passed preflight and per-file compile,
printing OK for commit 9344e99fb3f; no push was made by that dry run. No node statement was corrected and no
STATEMENT-DISPUTED issue was found. The repair validation is recorded below.

## Second reading by NA

The dispatcher explicitly prohibits starting another agent and says the maintainer
independently reviews the delivery. This section is an author second reading,
not a claimed independent worker review. I reopened the entire node, current source
Hom display and final Lean module. I checked every supplied-data field and every
conclusion against the list above. This reading added the finite counit formula
rather than leaving only the system trace equality, added the actual-system
naturality and common-degree square, and tied the coordinate compact-support
composite to published `rawSupport` by `systemPresentation` and
`supportPresentation`. I also changed `transpose` to take the conclusion's
canonical-unit invertibility witness, so it cannot silently invert a nonisomorphism.
The degree-r normalization is identity on H^r, and the single-degree clause uses
the same integer for both systems. The two previously cited landed nodes are genuinely
used for quotient coordinates and completed coefficient presentation. The module
has no data-valued sorry, and its only theorem has the node's complete proof plan.


## Repair of immutable head d0fc69adc4a2 — H3

The return was correct: the old `Family.systemPresentation` was a free endpoint
isomorphism and did not normalize the trace on the dependency's functor. This repair
changes the construction, the public conclusion and the record; it is not an
unchanged re-push. I compared the retained node with current main: its statement
and every field outside lean/stmt_deps remain identical, and current main has no
superseding Lean record. The wrappers refresh/rebase the delivery worktree.

1. New canonical beta: `def-pur-integral-support-coordinate-comparison`, module
   `Sheaf.Paper.PurIntegralSupportComparison`, defines beta as a paste of the
   uniquely normalized ordinary and derived comparisons. `PushNormalized` is the
   actual identity on every section after `rightEvaluation` and `rightUnderlying`.
   `Ordinary.openPull_transpose` fixes the inverse comparison relative to the
   ordinary inverse/direct adjunction. `openExtension_transpose` is the actual
   Hom equation under the two extension/restriction adjunctions, through
   `integralExceptionalCoordinates`. The derived record's `openComplex_component`
   and `derivedOpen_factors` fix its exact localization on every representative.
   `properComplex_component` and `derivedProper_unit` fix the proper comparison
   by the actual universal right-derived unit `rightUnitApp`. The normalization
   package has exactly one inhabitant (`normalized_existsUnique`); `normalized`
   is chosen from this uniqueness theorem. Its theorem determines all data fields,
   including the complex maps componentwise. `beta` is their fixed proper/open
   paste; `beta_characterization` excludes independent automorphism twists.
   Thus this is not a choice from undetermined mere existence.
2. Removed `Family.systemPresentation`. There is no free isomorphism field in
   Family. The single `coordinates` helper moved to its new owning node, and
   the item imports it instead of defining another coordinate notion.
3. `PublishedFamily` states the R-linear Hom bijection directly with the exact
   `CompactSupportCondensedRealization.integralSupport l E c R M` from the
   dependency. `hom_formula` transports the coordinate Hom by the inverse of
   `supportPresentation beta`, using the fixed beta, never a package field.
   `PublishedFamily.hom_natural`, `input_natural` and `trace_natural` all use
   this same published integral functor. The theorem takes the dependency's
   `IntegralModel` because the node already fixes its P_R and actual comparison.
4. `PublishedFamily.alpha_transport` explicitly asserts equality of actual
   ordinary-system morphisms:

   `R_Y(supportPresentation beta) ≫ C_Y(alpha_dep) = alpha_coord ≫ beta`.

   Here alpha_dep is literally the dependency declaration, with its canonical
   coefficient-model counit and reduction/total-limit counit. This equation
   identifies the coordinate alpha with that declaration before any evaluation.
5. `PublishedFamily.trace_reduction` now has `R_Y(t_dep)` on the left and
   `C_Y(alpha_dep) ≫ beta.inv ≫ F(e) ≫ F(theta) ≫ epsilon` on the right.
   This is the node's reduction equation in the recorded Brown quotient
   coordinates, retaining the actual dependency alpha. `trace_evaluation` uses
   this exact prefix and the existing specified finite counit expression, so
   the trace on rawSupport/integralSupport has the finite counit formula too.
   `hom_formula` and alpha_transport connect both trace formulas to the actual
   coordinate Hom chain rather than to another unnormalized representation.

The node statement and proof are unchanged. Its stmt_deps gains exactly the new
comparison definition node. The new node cites the owners of the ordinary
coordinates, compactification, Brown data, sequence-site support and derived
systems; no recorded dependency interface is silently replaced. Both previously
added landed dependencies remain used. All previously accepted recognition,
concentration, intrinsic constructibility, linearity and naturality clauses remain.

## New nodes

`def-pur-integral-support-coordinate-comparison` defines the missing canonical
isomorphism between the Brown ProCompact proper/open functor and the published
ringed-sequence-site `systemSupport`, through the existing exact quotient
coordinates. Its source is the current blueprint integral Hom chain and final
unit/counit paragraph, with the open and proper characterizations from Zheng
4.1/4.10/5.15 and the existing `integralExceptionalComparison_characterization`
pattern. The Lean `Ordinary`, `Derived`, `Normalized` records spell out the
normalizations, with existence-uniqueness and beta-characterization theorems.

Searches before defining it: `blueprint_refs.py search 'compact support coordinates'`
returned zero matches. DAG, Sheaf and WeilConjectures searches of
`systemPresentation|supportPresentation|canonical.*compact.support.*coordinate`
found no comparison of these Brown and sequence-site functors; existing
supportPresentation declarations have other endpoints. LeanSearch with the full
canonical-comparison query returned generic sheaf adjunctions; LeanFinder with
"Uniqueness of a comparison of derived functors with exact coordinate equivalences
normalized by the right derived functor unit" returned `rightDerivedUnique`,
`rightDerived_ext` and generic localizer comparisons. Mathlib grep
`integralExceptional.*[Cc]omparison|[Cc]ompact.*[Cc]oordinates` returned two unrelated
compact-coordinate topological hits. These results and the project searches are
recorded in the new node's mathlib_searches. The existing site comparison fixes
site inverse/direct images but does not compare proper/open compact support,
so this is not another owner of an existing construction.

## Second reading by NA — repair

I reopened the returned item, both full final modules and the published
`systemSupport`, `rawSupport`, `integralSupport`, `limitPresentation`, `alpha`,
`ProCompact`, `CoefficientDerivedImage` and
`integralExceptionalComparison_characterization` declarations. I traced the
new beta from the section identity to the ordinary inverse-image transpose,
then the extension transpose, then exact localization and the proper universal
unit. The direction of properPush is sequence push then coordinates to coordinates
then strict push, so its inverse occurs in derivedProper_unit. The derived open
comparison has the complementary direction, giving beta from coordinate Brown
support to sequence support then coordinates. The alpha_transport square has
supportPresentation.hom and beta.hom in the same direction; consequently the
published trace formula uses beta.inv. The Hom map uses supportPresentation.inv,
as required for a morphism out of the published rawSupport object. Naturalities
use the published functor on the reconstructed system map. Every previously
accepted hypothesis and both recognition alternatives remain in the old Supplied
and Pair bundles; the public output adds the actual published functor and alpha
clauses. This is an author second reading; the dispatcher prohibits another
agent and the maintainer supplies the independent review.


Repair validation: both modules compiled together through scompile.py, each separately
in dependency order, with a private overlay for the new comparison module. The initial
successful pass reported only long-line warnings in that new module; every flagged
line was shortened. The final server confirmation compiled the comparison module in
36.4 seconds and the item in 56.4 seconds, with no warnings. Local unfolding was
restricted for the already typed beta/presentation helpers; no compiler limit or
linter was raised or disabled.
All changes are in the sandbox. Neither a global build nor a direct Git mutation of
the read-only clone was used.

The repaired packet passed `deliver2.py --no-push`: preflight and both per-file
compiles passed, with dry-run commit 02fd3cb1eb0; that command pushed nothing.
