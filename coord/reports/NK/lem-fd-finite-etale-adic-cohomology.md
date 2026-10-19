## Worker report

Item: `lem-fd-finite-etale-adic-cohomology`. Module:
`Sheaf.Paper.FiniteEtaleAdicCohomology`. Main declaration:
`AlgebraicGeometry.Scheme.FiniteEtaleAdic.finiteEtaleAdicCohomology`.
The result is the proposition-valued bundle `CohomologyComparisons`; its fields
spell out the coefficient-stage conclusions and the canonical maps. Every theorem
proof is `sorry`; definitions contain constructed data only. Each postponed theorem
has its own source and complete proof plan. No object is chosen from a bare
existence statement: the selected level and section comparisons have uniqueness
and explicit section/unit normalizations. `CommonStageComparisons` is only an
existence conclusion and is never used to choose a functor or object.

Hypotheses and coefficient objects:

- `l : ℕ`, `[Fact l.Prime]` give the coefficient prime. `X Y : Scheme.{u}`,
  `[IsNoetherian X]`, `[IsNoetherian Y]`, the `Fact` bounds on
  `topologicalKrullDim`, and the stalk-unit `Fact`s give exactly the two noetherian,
  finite-dimensional schemes and invertibility of l. No separatedness, base field,
  characteristic prime, connectedness, nonemptiness, or finite-type condition is added.
- `(f : Y ⟶ X) [IsFinite f] [Etale f]` uses the recorded Mathlib morphism classes.
- `E : Padic.FiniteCoefficientFields l Qbar` is a finite extension in a chosen
  algebraic closure. Any finite extension embeds in such a closure; this also
  supplies the common-stage datum required by the statement. The original
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing` are used. Index `n : ℕ` denotes the positive level
  `n + 1`. The uniformizer's principal ideal and all its powers are independent
  of which uniformizer is chosen.
- `F : AdicIntegralDiagram l E.val Y` retains the actual transition maps.
  `IsFiniteFreeSystem` uses the recorded `IsLisseIntegralDiagram` and asks that
  each geometric fibre be isomorphic to `(A_(n+1))^(Fin r)`. The former gives
  finite local constancy, quotient annihilation, and surjective transitions with
  precisely the quotient kernels. On the conservative exact geometric fibres,
  these are equivalent to the specified tensor-transition isomorphisms; those
  isomorphisms are uniquely induced by the given transition maps. Rank is allowed
  to vary by component. The fibre tests use all geometric points in the scheme's
  universe, including algebraic closures of residue fields, a conservative family.
- The full recorded lisse category has an additional separatedness convention.
  This delivery uses its raw diagram and raw predicate, which have no such
  hypothesis; it does not impose that convention on the present theorem.
- `completedSystem`, `realizationSheaf`, and `realization` give the actual
  inverse-limit completed coefficient sheaf and its degree-zero complex. They
  use the published comparison inverse image, coefficient-presentation map,
  associated-module functor, and completed scalar extension. No discrete
  non-torsion sheaf on the small etale site is used for integral/rational RΓ.

Conclusions and their Lean clauses:

- `system` states finite local constancy, finite freeness, and normalized quotient
  transitions for `systemPush`, the actual etale direct image of the whole diagram.
- `integral_mem`, `pushed_mem`, `detailed_mem`, and `detailed_pushed_mem` place both
  constructed objects in the actual complete constructible categories. The last
  two use the dependency's exact `WeilConjectures.sfIntegralConstructible` after
  the recorded coefficient-presentation equivalence `purCoefficientModel`.
- `quotients` is `HasCanonicalQuotients` on both systems: multiplication by the
  uniformizer power is mono, the actual limit projection is epi, and their
  short complex is exact. Thus the displayed levels are the ordinary and derived
  reductions, with no higher Tor, and the maps are the supplied limit projections.
  This is a sheaf statement, not an interchange of inverse limits and stalks.
- `levelComparison` is the uniquely normalized coefficient/site mate. Its formula
  sends the actual unit tensor of a section to the unit tensor of that section's
  image under `ProEtale.lowerStarComparisonUpperStarBaseChange`.
  `sheafComparison` takes the limit of these actual maps and the inverse of the
  standard limit-preservation isomorphism. `derivedComparison` composes this map
  in degree zero with the universal right-derived unit. `direct_iso` asserts its
  invertibility. Its source is literally a single sheaf in degree zero, so it
  identifies ordinary and derived direct image and proves the sheaf-degree-zero
  assertion. `direct_stages` asserts the same for the actual localized and
  common-stage arrows, with unchanged integral representatives; this also gives
  their degree-zero assertions in the standard localized t-structures.
- `sectionsComparison` is uniquely fixed by restriction along the inverse
  terminal-object comparison. `derivedSectionsIso` is derived composition from
  this map and the universal derived units. `globalComparison` is its composite
  with `derivedComparison`. `integral_global` asserts the precise integral arrow
  is invertible.
- `rationalScalar` includes the existing small-field/integer presentation
  transport. `scalarDerived` is exact termwise balanced tensor on all module
  complexes. `rationalGlobalComparison` and `algebraicGlobalComparison` are
  literally the images of the integral arrow under these functors.
  `rational_global` and `algebraic_global` assert invertibility. `cohomology`
  applies `DerivedCategory.homologyFunctor` in every degree `i : ℕ` to all three
  arrows; hence it states exactly the three nonnegative H^i comparisons.
- `finite_models` supplies each original level's actual A_n-module sheaf with
  the given integral restriction. The quotient ring action is uniquely determined
  by that restriction. `finite_global` applies the normalized finite-coefficient
  comparison to these very levels, including every nonnegative H^i. It does not
  substitute discrete integral or rational coefficients for these finite rings.
- `projections` is the explicit commuting equation with every limit projection.
  `naturality` is the global comparison's square for every map between the given
  coefficient systems. Their scalar-extended equations hold by the actual
  functor definitions. The quotient-transition naturality is retained in the
  strict diagrams used throughout, rather than asserted for unrelated chosen
  level objects.
- `CommonStageComparisons` supplies linear operations on the dependency's actual
  `pbcQbarCategory`, with natural isomorphisms to the actual integral operation
  and the specified ambient module-valued sections at every finite stage.
  Its `normalization` equation fixes the section-comparison arrow to the scalar
  extension of `derivedSectionsIso` on every integral object and morphism.
  Linearity fixes the formula on rational pure tensors and arbitrary common-stage
  scalar morphisms. `common_stage` asserts this normalized descent exists.
  The `push_mem` field supplies the finite-etale preservation needed to restrict
  the actual ambient pushforward when describing those category-level operations.
  Finite free coefficient extension commutes with sections without any output
  boundedness assumption; this is the source's finite-direct-sum argument.
- `pullAction` uses the actual derived adjunction unit for an automorphism and
  the normalized section-composition isomorphism. `pushAction` uses the same
  unit, the actual derived direct-image composition, and `h.hom ≫ f = f`.
  `automorphism` is their intertwining equation. Its action map
  `a : Lh^* K ⟶ K` is exactly the action data needed when the action is on the
  same coefficient object, as explained explicitly in Step 10 of the node's
  proof. An arbitrary automorphism of Y alone is not claimed to fix an arbitrary
  coefficient sheaf. Scalar extension and taking homology preserve this equation.
- `exchange` quantifies over every base change in the node. Only X' is assumed
  noetherian, finite-dimensional and l-invertible; Y' is supplied with a
  `ChosenCartesianSquare`, so no extra hypothesis is imposed on it. The first
  arrow is exactly `pbcActualCompletedExchange`, the recorded ambient adjunction
  mate followed by completion. Finite exchange is asserted both with integral
  restriction coefficients and at every A_n. The last equation is naturality for
  all coefficient endomorphisms, hence all defined character projectors.
- `exchange_stages` supplies the actual endpoint membership proofs and asserts
  invertibility of the rational and common-stage images of that same integral
  mate. `rationalStageMap` and `algebraicStageMap` use precisely the recorded
  localization and finite-stage inclusion. The recorded scalar/exchange
  coherence identifies these maps after further finite coefficient extension;
  no independent or arbitrary exchange arrow is introduced. Naturality of the
  ambient transformation and of the stage functors includes rational and
  common-stage endomorphisms, hence character idempotents wherever defined.

Universes and dependency declarations:

The small pro-etale site retains object universe u+1 and morphism universe u.
The completed module categories are the recorded ones, with coefficients and
module carriers in u+1. The generic derived-composition interface elaborates
with global module complexes in localization universe u+2. `globalSectionsDerived`
is the existing total right derived functor of `adicGlobalSections` in that
output localization; it does not define another underived notion of sections.
`moduleUniverseTransport` is induced by the identity on module complexes and
has its localization normalization `moduleUniverseFactors`. The named
`moduleUniverseTransport_isEquivalence` and the uniquely universal-unit-normalized
`sectionsUniverseComparison` identify this output with the recorded
`adicDerivedGlobalSections`. Thus this is an explicit equivalent transport, not
an equality imposed on the two site universes. The two localization instances are passed explicitly to the identity-derived
functor and its factorization: the large instance is the existing
`HasDerivedCategory.standard`, and the small instance is the published
`HasDerivedCategory.ofIsGrothendieckAbelian` construction. Passing them explicitly
avoids Lean shadowing the large local instance when the small one is installed.
No new localization or categorical structure is postulated.

The original five dependencies were read, including their full recorded signatures:
Mathlib `AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.Etale`;
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its integral/quotient
coefficient declarations; `Sheaf.Paper.SfIntegralConstructible` /
`WeilConjectures.sfIntegralConstructible`; `Sheaf.Paper.PbcQbarCategory` /
`AlgebraicGeometry.Scheme.pbcQbarCategory`.
Already recorded nodes added to `stmt_deps` supply the diagram/predicate in
`LisseIntegralSmallCoefficients` / `LisseAdicSheaves`, the `adicGlobalSections`
interface, `pbcActualCompletedExchange` and actual composition/adjunction maps,
`purCoefficientModel`, the actual bounded constructible tower categories, and
raw rationalization and finite-stage pair-category inclusion. Their modules are
imported rather than redefining those notions. Available recorded proof-dependency
modules are imported for the stated proof plan. No new dependency node or
lean-only dependency repair is required.

Searches for an existing statement:

- `msearch.py ... leanfinder` with “finite etale direct image l-adic compatible
  locally constant finite free systems cohomology base change”: eight unrelated
  profinite/condensed results; no exact result.
- `msearch.py ... loogle` with `AlgebraicGeometry.Etale, IsFinite, Sheaf.cohomology`:
  no exact result (unqualified `IsFinite` was not recognized by that search).
- `msearch.py ... leansearch` with “finite etale pushforward cohomology base change
  adic locally constant finite free system”: eight results, including ordinary
  finite-etale base change, without the completed-coefficient/common-stage result.
- `msearch.py ... grep` with `finite.*(adic|Adic)|[Aa]dic.*[Cc]ohomology`:
  24 hits; Mathlib ell-adic cohomology interfaces do not state this comparison.
- `rg` of the original project and `lean/Sheaf` for adic cohomology, completed
  realization, finite etale direct image, and the exact item identifier found
  the finite exactness/base-change theorems and the lisse realization interfaces,
  but no exact statement. The existing lisse cohomology calculus imposes
  separatedness and concerns tensor/dual/fibre calculations, so is not an
  existing match for the present theorem. The completed module operations and
  their canonical maps were reused. No competing independent notion was added.

Edge cases checked: the empty scheme and empty finite fibres give the zero-rank
system; rank zero is permitted by `Fin 0`; disconnected schemes permit varying
ranks; level zero of the natural-number index means the positive quotient A_1;
no A_0 or division by its uniformizer is used. Identity f and identity base change
retain their canonical composition/unit maps. Arbitrary base changes need not be
separated or finite type. No cohomological finiteness of a structure morphism is
assumed. No character denominator is inverted unless the projector itself is
defined. Ramified coefficient extensions use the recorded normalized scalar
system, not an equality of the two uniformizer filtrations. Finite freeness is
an explicit hypothesis, rather than a consequence of finite local constancy.

No `STATEMENT-DISPUTED` issue or statement correction is needed.
Compilation validation: the prescribed `scompile.py NK
lem-fd-finite-etale-adic-cohomology` passed for the delivered file under both
the sandbox and final library module names, with no errors or warnings.
The required `deliver2.py NK lem-fd-finite-etale-adic-cohomology --no-push`
passed preflight and compilation (dry-run commit `341f3900cf`); nothing was pushed
by that dry run.

## Second reading by NK

This dispatcher brief starts one worker and explicitly forbids starting other
agents; there was no independent worker available for this section. I performed
a separate clause-by-clause rereading with the source node and module open.
The changes from that rereading were: make finite freeness explicit; avoid the
recorded lisse category's separatedness assumption; retain actual A_n coefficient
actions; use all module complexes as the global-sections target; normalize the
coefficient/site map on unit tensors; retain the actual ambient exchange mate;
include the rational/common-stage endpoint membership proofs; and provide the
explicit identity-localization transport back to the recorded sections functor.
The maintainer's independent delivery review remains the independent reading
specified by this dispatcher's workflow. This section does not claim an
independent agent reviewed the delivery.

## Resume self-check, 2026-10-18

The saved packet was retained. The initial required dry run failed in
`moduleUniverseTransport` and `moduleUniverseFactors`: local instance search
could not simultaneously retain the two different localization universes for
the same module category. The missing-comparison errors were consequences of
those failures. The repair supplies both existing localization instances
explicitly in the helper signatures and the identity-derived construction.
The factorization also uses the fully qualified `Functor.isoWhiskerRight`.
Their source and target remain the large and small localizations of the same
module complexes. The universal-unit normalization in
`sectionsUniverseComparison_exists` is retained. No mathematical hypothesis,
conclusion, or dependency node is changed by this repair.

The self-check reread the main declaration and its bundled clauses against the
current DAG statement and the parent blueprint first display. It confirmed the
prime, finite-extension, noetherian, dimension, invertibility, finite-etale and
finite-free-system hypotheses; all integral, finite, rational and common-stage
comparison clauses; the specified quotient maps; naturality, automorphism action
data, and arbitrary permitted base change. It also checked the recorded
dependency interfaces and the explicit transport back to the published ordinary
derived sections. The prior searches and all original constructions are retained.
