## Worker report

Item: lem-pur-condensed-compositor-realization. Module:
`Sheaf.Paper.CondensedCompositorRealization`. This is statement-only: the main
comparison theorem and the three proof prerequisites have `by sorry`; definitions
contain actual maps. No purity orientation or trace is an input.

The source is the current `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-composition/sk-prop-sp-composition.proof.md`, its introductory passage
through total limit and coefficients, and its Towers paragraph. I also read the
item's nine-step explicit comparison supplement and the latest transport context.
The item is an agent supplement, not the blueprint unit's own statement.

Hypotheses and constructions, in statement order:

- Distinct primes and positive characteristic are `[Fact l.Prime]`,
  `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ l)]`. Thus p is `ringChar k`;
  characteristic zero is excluded, and no finite-field/algebraic-closure assumption
  is imposed on k.
- `X Y Z : CondensedERealization.Base k` bundles exactly separated finite-type
  k-schemes. The maps have the existing `IsOver (Spec (.of k))` instances.
  `df dg : ℕ` and `SmoothOfRelativeDimension df f`, respectively dg and g, give
  smoothness and pure relative dimensions. The composite h is always `f ≫ g`.
- E and k are in the same arbitrary universe u because the recorded coefficient
  APIs use that convention. `_e : E ≃ₐ[ℚ_[l]] ℚ_[l]` fixes E to a universe-sized
  presentation of Q_l, not an arbitrary finite coefficient extension. This allows
  arbitrarily large schemes without putting Q_l itself in the scheme universe.
  The algebraic-closure embedding is exactly the algebra map Q_l → Omega composed
  with `_e`; the valuation ring and positive finite quotients are thus presentations
  of Z_l and Z/l^(n+1). Index n means positive exponent n+1 throughout.
- `CondensedERealization.Integral l E T.scheme` is the recorded completed bounded
  constructible category, including compatible etale origins. No replacement
  category or independently chosen coefficient object is introduced.
- `A.reduction` is the actual `CoefficientDerivedSystemCalculus`; its reduction,
  `coefficientSequenceLimit`, unit and counit act in the ordinary derived category
  of the ringed sequence site. `systemSupport` is exactly J followed by R.
- `P` abbreviates `integralSupport`, including its actual total-limit definition
  and the specified `IntegralModel`. The prose beta is the parent's `alpha`.
  `delta` is the unit followed by L of that exact alpha. `delta_isIso` records
  its triangle-identity identification with `limitPresentation`.
- `Uniform` reuses `finiteTorConstructibleIntegral` on the image under the
  existing `purCoefficientModel` equivalence. Its `sfIntegralConstructible` part
  imposes the common finite cohomology window; its other part imposes one ordered
  Tor interval for every positive reduction, using `HasProEtaleTorAmplitude`.
  This tests every module sheaf in degree zero, not global sections or one free
  module. The completeness, constructibility and origin data are the same as the
  given integral object's data in these coefficient coordinates. For the pinned
  calculus, finite evaluation of actual reduction is canonically identified with
  the recorded finite derived scalar extension, so this is the node's normalized-reduction domain.
- `cf`, `cg`, `ch` are arbitrary supplied compactifications. `d` is a compatible
  tower compactification of `cf.g ≫ cg.i`; `c`, `r`, `s` are a common refinement
  of its literal `Compactification.overComp` with ch. This records the choice
  data used by the proper/open word; the standard existence dependencies supply
  such data. `systemTower` spells the proper/open word in the parent's simultaneous
  coefficient-system coordinates using the existing gamma, sComp and jComp.
  `systemCompositor` then inserts the actual system refinement transformations.
  These are whole derived-system maps, not arrows assembled from finite evaluations.
- `refinementIso_exists` is the named prerequisite allowing the inverse refinement
  factor on uniform inputs. Its RefinementIso witness has iso.hom explicitly equal
  to the actual systemRefinement component. `refinementInverse` extracts its
  uniquely determined inverse. Its proof plan uses the strict-tower etale-origin
  comparison and conservativity, not faithfulness of finite evaluations.
- `integralCompositor` is literally the displayed five-arrow composite: delta_g
  at P_f K; L F_g R(delta_f); L F_g of the actual reduction/limit counit;
  L of `systemCompositor`; inverse delta_h. It is transported back by the
  fully faithful published coefficient equivalence and the existing full
  subcategory hom constructor. It is not a separately supplied isomorphism.
- `U` is pbc rationalization, then the specified realization equivalence J, then
  the bounded inclusion and `omegaScalar`. `omegaMap` is the finite-extension-valued
  coefficient map to `Profinite.padicAlgClRingObj`; unrestricted continuous Omega
  functions are never substituted. `U_constructible` supplies the actual bounded
  constructible object needed to evaluate the archived compositor.
- `comparison` is exactly scalar extension of the parent's rational realization
  component followed by `condensedProjection (omegaMap ...) c`.
- The landed `CompactSupportRealizationFactorization.IsFactorized` pins that parent
  realization component to its ordered construction: inverse reconstruction q,
  proper scalar counit mate, and open scalar unit mate, with all lattice and
  section presentations. Its existence theorem supplies the canonical family.
  This is necessary: `ComparisonFamily` by itself records an isomorphism with
  insufficient normalization to rule out rescaling. `_hC` says that C is the
  specified family, rather than adding a geometric or boundedness assumption.
- `condensedCompositor` is the inverse of the literal archived
  `boundedConstructibleLowerShriekComp_padicAlgCl`, conjugated by the three
  archived compactification-independence isomorphisms. Its direction is
  F_f followed by F_g to F_h. No arbitrary compositor is a parameter.

Conclusion clauses:

- `Laws.integral_invertible` gives invertibility of the specified integral arrow
  on the uniform domain. `comparison_invertible` retains the prescribed comparison
  isomorphism, already asserted for integral objects by the parent.
- `Laws.square` is exactly U(alpha_R) followed by a_h equals a_g at P_f K,
  followed by F_g(a_f), followed by the transported archived alpha_Omega at U K.
  It is written in the ambient internal-module derived category. The full bounded
  constructible inclusion is fully faithful, so this is exactly the equality in
  the node's bounded constructible category.
- `Laws.naturality` is the naturality equation for the actual integral arrow;
  the a maps are components of natural transformations by their definitions.
- `tower_independence` compares every other compatible tower and common refinement
  for the same three compactifications.
- `refinement` states the horizontal composition equation for arbitrary proper
  refinements of cf,cg,ch. `comparison_refinement` gives the three accompanying
  U/a squares, using `fieldRefinement` over the finite-valued Omega coefficient.
  Along with `square` for each supplied triple, these give the requested transported
  equality for all compactifications and their common refinements.
- The open case is included by taking cg to be `Compactification.ofIsOpenImmersion g`.
  `openTrivial` is the specified identification with exact bounded open extension:
  whisker the archived adjunction-normalized `boundedConstructibleLowerStarId`
  and compose the functor right unitor. Its source is literally support for
  (g,id), so the general square transports to the asserted exact-extension square.
  No extra choice or trace enters this identification.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`,
  `boundedConstructibleLowerShriekOfCompactification` and the bounded categories.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`.
- `Sheaf.Paper.IntegralUniformCoefficient`: the recorded
  `pbcBoundedConstructibleComplete` notion underlying `CondensedERealization.Integral`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientDerivedSystemEvaluationCalculus`,
  the actual reduction/limit adjunction and finite evaluations.
- `Sheaf.Paper.CompactSupportCondensedRealization`: `IntegralModel`, `integralSupport`,
  `alpha`, `limitPresentation`, `ComparisonFamily`, `CoefficientData`,
  `integralReduction`, `integralRefinement`, `systemRefinement`, `omegaMap`,
  `omegaScalar`, and the original `condensedProjection` it imports.
- `Sheaf.Paper.TowerAdjointCompositorRealization`:
  `TowerAdjointCompositor.towerAdjointCompositorRealization`. Its normalized word
  is expressed in `systemTower` through the actual SemilinearProperOpen primitives,
  because the parent uses simultaneous ringed-sequence coordinates rather than
  the dependency's restricted SpTowerCalculus presentation. The normalization and
  finite b/c identities are used in the main proof plan; no evaluated equality
  is used to define a whole-system arrow.
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`:
  `CoefficientCompatibility.etaleProEtaleCoefficientCompatibility` and its
  composition equation (finite b normalization in the proof plan).
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`:
  `AlgebraicGeometry.Scheme.finiteRing_constructibleDerived_origin`.
- `Sheaf.Paper.FiniteAdjointCompositorTransposes`:
  `AlgebraicGeometry.ProEtale.finiteAdjointCompositorTransposes` (finite c identity).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`:
  `constructibleCocone_isFilteredTwoColimit` (finite-valued Omega descent).
- `Sheaf.Paper.CondensedERealization`: `Base`, `Data`, `Integral`, `At.realization`
  and `condensedE_realization`; no private realization construction is made.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition`:
  `CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`; and its imported
  CompactificationIndependence module's exact
  `boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl`.
- `Sheaf.Paper.CompactSupportRealizationFactorization`: `IsFactorized`,
  `realizedFactorization`, `q`, `rho`, and `atNormalized`, registered by the new
  definition owner `def-pur-compact-support-realization-factorization`. The main
  theorem assumes `C` and `IsFactorized C`; it does not use the conclusion of
  `compactSupport_realization_factorization`.
- `Sheaf.Paper.CompletedCoefficientPresentationTransport`:
  `purCoefficientModel_bounded_predicate` identifies the existing pbc predicate
  with `sfIntegralConstructible` on the coefficient-model image. Its Noetherian,
  finite-dimension and prime-invertibility hypotheses follow from the given Base
  objects by `base_noetherian`, `base_dimension`, and `base_primeUnit`. Thus the
  constructibility part of Uniform adds no condition to an integral input.
- `Sheaf.Paper.FiniteTorAmplitudeSites`, publicly reexporting
  `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructibleIntegral`, built from
  `sfIntegralConstructible` and `HasProEtaleTorAmplitude`. Its already landed
  definition node is added to statement dependencies.

Searches for an existing statement:

- msearch LeanFinder, "integral compact support condensed realization preserves
  composition": eight unrelated condensed limit/solidification results, no match.
- msearch Loogle, "boundedConstructibleLowerShriekComp_padicAlgCl,
  Functor.isoWhiskerLeft": zero hits (the project-specific first name is not indexed).
- msearch grep, `compactSupport.*[Cc]omp|[Cc]ompositor.*[Rr]ealization`,
  Mathlib/CategoryTheory: zero hits.
- msearch LeanSearch, "derived inverse limit condensed realization preserves compact
  support composition": eight generic limits/composition results, including
  `instHasLimitsOfShapeCondensed`, `Condensed.comp_val` and
  `CategoryTheory.preservesLimit_comp_of_createsLimit`; no comparison square.
- rg of upstream WeilConjectures, project Sheaf, and dag/lean_names_upstream.json
  for the item id, compact-support composition, compositor realization, and archived
  compositor names: no exact theorem. The archived compositor itself is reused.
  `IntegralCompositorLimitRealization` states a reconstruction formula in different
  sfIntegral coordinates and does not assert this condensed comparison.
- Subsequent rg for realization normalization found the landed
  `CompactSupportRealizationFactorization` interface, which is reused to fix a.
  Searches for Tor amplitude and cohomological support found the existing
  `HasProEtaleTorAmplitude`, `proEtaleCohomologicalSupport`, and the assembled
  `finiteTorConstructibleIntegral`. The last is reused directly through the
  published coefficient equivalence, avoiding repeated presentation comparisons.

Edge cases checked against the statement and map directions: f or g identity;
relative dimensions zero; g open with trivial compactification; empty schemes and
empty open immersion; zero K and zero test sheaves; lowest positive coefficient
level n=0 (exponent one); equal endpoints of either uniform interval; different
choices of common refinement, and identity refinements. No nonemptiness of schemes
or of supports is required. In particular empty cohomological support fits [0,0].
No characteristic, scheme universe, or arbitrary-lift case is discarded.

No mathematical statement correction is made and no statement is marked disputed.
The item adds the landed finite-Tor definition and the new definition owner for
the existing canonical factorization interface to its statement dependencies. The normalization gap was resolved by reuse, not by adding
an arbitrary comparison parameter or assuming the desired composition square.
The compositor elaboration uses an explicit target type, keeps large system maps
opaque during inference, and supplies delta invertibility locally at the inverse.
The refinement inverse is extracted from the recorded IsIso proof
using Classical.choice on the RefinementIso record, whose iso.hom field is explicitly equal to the
actual systemRefinement component. Fixing that hom determines the entire iso,
including its inverse, by Mathlib Iso.ext; this packaging avoids reducing the large map while
extracting an inverse.
The inverse is uniquely determined; this is not a choice of an unconstrained map.
This leaves the displayed maps unchanged and avoids an unnecessarily broad
IsIso instance while statements are elaborated.

Validation: the node signature and declaration inventory match the file verbatim;
all Lean lines are at most 100 characters. A read-only traversal of statement and
proof dependencies confirms that neither of the added definition prerequisites has
a path back to this item. Compilation and delivery preflight results follow below.

## Second reading by NB

The dispatcher explicitly prohibits starting other agents and specifies an
independent maintainer review of the delivery. No second worker was started and
no independent review is claimed here. I made a separate local reading with the
full node and Lean file open. The hypothesis and clause correspondence is listed
above for the maintainer's independent check.

The local reading found and repaired two issues before delivery: the parent
ComparisonFamily alone did not pin the ordered realization map (resolved by the
already landed IsFactorized interface), and the expanded uniform-domain test should reuse
the existing integral finite-Tor predicate (now finiteTorConstructibleIntegral). The main square uses
f-then-g order on both sides, the archived isomorphism is inverted, and the
refinement maps go from coarser support to finer support on both sides.

The RefinementIso record packages the existing canonical refinement iso and its
exact hom characterization. It introduces no extra map or hypothesis: the record
is unique by Iso.ext and proof irrelevance. This is implementation packaging of
the canonical inverse, used to keep Lean from unfolding a large subtype predicate.

## Validation results

The final source, with all diagnostic commands and profiling options removed,
compiled on the server with no errors or warnings: sandbox 18.7 s and actual
module 24.4 s, both within the 60 s limit. The declaration inventory contains
19 declarations and the main signature matches the node record verbatim. A fresh
read-only traversal confirms that neither added prerequisite reaches this item
through statement or proof dependencies. Delivery preflight is recorded next.

The prescribed deliver2.py --no-push dry run passed server preflight and per-file
compilation (dry-run commit 327331e9aa8). This was the validation of the returned head; repair validation follows below.

## Repair of returned delivery

The independent return of immutable head `31f6e277d759` accepted the Lean
statement and every mathematical clause, and requested one H2 repair. The item
now cites `def-pur-compact-support-realization-factorization` in place of
`lem-pur-compact-support-realization-factorization`. The theorem's existence
conclusion is not used: `C` and `_hC : IsFactorized C` are already hypotheses.
The accepted Lean module is byte-for-byte unchanged. No statement correction
or dependency theorem repair is required. The delivery wrapper rebases this
packet against current main; no direct Git operation was run in the read clone.

## New nodes

`def-pur-compact-support-realization-factorization` registers the existing plain
definitions `rho`, `q`, `realizedFactorization`, `atNormalized`, and `IsFactorized`
in `Sheaf.Paper.CompactSupportRealizationFactorization` with `existing: true`.
It owns the definition interface without asserting that a factorized family
exists. Its self-contained statement records the actual unit/limit map and
ordered realization composite, every quantifier of IsFactorized, and all five
clauses: invertibility of q; the whole-system alpha equation; invertibility of
the proper mate; invertibility of the inverse open mate; and equality to the
parent's realization component. These are exactly the definitions at lines
68–148 of the published source; no new data, theorem or sorry is introduced.
The new node cites the existing coordinate, integral-system and presentation
definition owners. Its `unreachable` import flag follows the read-only traversal
of current target and former-target roots, which do not reach this item.

New searches: LeanSearch and LeanFinder returned only unrelated generic
Mathlib results; the Mathlib grep had zero hits. Source rg found exactly the
existing factorization definitions in Sheaf and no WeilConjectures definition.
DAG search found the theorem record but no definition owner for this interface;
blueprint_refs search returned zero exact phrase matches and ancestor returned
None. The new node records the wrapper's exact search results. Identity maps,
zero integral objects, arbitrary base field, all integral objects without a Tor
window, and arbitrary choices of the pinned operation/model/bridge retain the
existing predicate and the accepted theorem statement unchanged.

## Repair validation

The prescribed scompile.py invocation for the unchanged item returned clean
results: sandbox 18.7 s, actual module 24.4 s. The main signature matches its
node verbatim, and the new definition node cites exactly its listed statement
dependencies. Compared with current main, the existing item changes only lean
and stmt_deps. The accepted Lean module is unchanged from the returned head;
the H2 repair adds definition ownership and replaces the theorem dependency.

The prescribed deliver2.py --no-push subsequently passed on the server:
commit `6a9d1e3b3c5` passes preflight and compiles. This validation includes
the delivered item module and the wrapper's existing-declaration checks for
all five definitions registered by the new node. The wrapper rebases the packet
on current main. Earlier retries had stopped at a server storage error while
compiling a published dependency; the successful dry run supersedes those
failures. No outstanding H2 repair or validation failure remains.

Validation recorded: 2026-10-26 22:07 UTC.
