## Worker report

The delivery states `WeilConjectures.PurityFiniteSetting.flag_pullback_split_injective`.
It postpones only that theorem. All helper definitions have real data and encode the
specified Chern components, zero projection, projection formula and supported Hom map.
`supportedProjectionSplitting` is the displayed collection of witnesses and
normalization equations; its `componentCondition` is supplied by the actual bounded
Chern components in the theorem. It assumes no splitting or decomposition.
The source is main-20261015 `sec-smooth-purity/sk-prop-an/
thm-pur-localized-top-chern.proof.md`, Step 1, which was read in full.

Hypothesis and clause correspondence:

- The finite-field and finite A_{E,n} datum is `P : PurityFiniteSetting`.
  Its coefficient is the published `P.Coefficient`, with the site's standard ULift.
  No divisibility of the coefficient level by the ramification index is assumed.
- Rank r >= 0 is `r : ℕ`. The bundle is `F : T.Modules` with
  `[F.IsFiniteLocallyFreeOfRank r]`, the recorded finite-local-freeness predicate.
- The separated finite-type k-scheme is the explicit structure map `bT` with
  `[IsSeparated bT] [LocallyOfFiniteType bT] [QuasiCompact bT]`.
  The explicit map is needed for the recorded Kummer and projective-bundle interfaces.
- The complete flag scheme and map are literally `(completeFlagBundle r T F).scheme`
  and `.projection`, never an abstract flag variety or arbitrary projective tower.
- Arbitrary closed support is `i : Z ⟶ T` with `[IsClosedImmersion i]`.
  The target support `i'` and `g` form the chosen Cartesian square `_sq`.
  Thus it is Z ×_T Fl_T(F), up to its specified unique pullback isomorphism.
  No regularity, smoothness, nonemptiness or pure dimension is imposed on Z.
- The degree and twist are `a b : ℤ`. `flagTwistPlus` uses the published
  `finiteEtaleTateSheaf` for the signed power and exact site comparison.
  These are the finite coefficient twists of def-coefficient-twists-detailed:
  lem-pur-kummer-additivity supplies the finite root-line identification for every
  killing exponent; tensor powers and dual evaluation give all integers.
- The source and target groups are the actual right-derived kernels of restriction:
  `SupportHomPair.group` unfolds to `ProEtale.supportHypercohomology`.
  The target coefficient is exact inverse image of A_T(a), hence A_T'(a) by the
  published finite twist pullback and site comparison. This keeps its canonical
  pullback identification rather than inserting an arbitrary coefficient isomorphism.
- Supported pullback is `supportedProjectionPullback`, homology of the published
  `e.derivedMap`, the actual derived kernel pullback. The recorded
  supported-Hom pullback theorem identifies this exact map with homology of
  `e.derivedMap` for the etale-origin signed Tate coefficient. Transport fixes its
  support unit by the kernel inclusion and inverse-image unit. No arbitrary map is used.
- The splitting is `s : target →+ source`, with `s (pullback x) = x` for every x.
  This states split injectivity as a homomorphism of abelian groups, not just injectivity.
- The prescribed degree-zero projection is `rho`. The equations for every bounded word
  fix its composites with the iterated decomposition components. A word has exponents
  `0 <= w j <= j` on Q_(j+1), for j < r. This is exactly the projective tower's basis:
  its final quotient Q_r has exponents 0,...,r-1; its predecessor has the earlier ones.
  `flagChernComponent` uses the actual quotient-line Kummer classes, their ordered
  cup powers, dual evaluation and adjunction. `flagZeroComponent` is zero except on
  the all-zero word, where it is the coefficient-unit evaluation.
- `supportedProjectionRetractionRaw` spells out the equation defining `rK`. It uses the existing counit-defined
  `ProEtale.rightDerivedLowerStarProjectionMap`, tensor of rho with identity, and
  canonical unit multiplication. Since the projection map is invertible here, this
  equation says exactly rK = (rho tensor 1) projection_inverse, with unit comparisons.
- Finally the equation for `chi (s x)` says that s is induced by rK under the
  normalized supported-Hom identifications and the actual derived adjunction.
  `supportedProjectionHomRetraction` spells out closed exchange and the canonical shift comparisons.
  Its left-derived shift comparison is transported through the published isomorphism
  with exact inverse image; no shift structure is assumed for a left-derived functor.
  Thus the result retains the node's prescribed splitting, rather than merely asserting
  an unspecified left inverse. The identifications and transport are the existing
  normalized structures, whose definitions force their canonical maps.

Recorded dependency interfaces used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `ProEtale.supportSections`,
  `derivedSupportSections`, `supportHypercohomology` (via SupportHomPair.group).
- `Sheaf.Paper.PbcCoefficientTwists` and its public finite signed twist interfaces;
  `Scheme.finiteEtaleTateSheaf` and `PurityFiniteSetting.diagonalTwistEtale` are
  the finite sheaf and ordered shifted tensor presentations used by the existing PBF.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, reexported by the flag dependency.
- `Sheaf.AlgebraicGeometry.CompleteFlagBundle`: `completeFlagBundle`,
  `completeFlagQuotient`, and the invertibility clause of `completeFlagBundle_properties`.
- `Sheaf.Paper.ProjectiveBundleFormula`: `projectiveBundleCupPower`,
  `projectiveBundleSummandPullback`, `projectiveBundleCupEvaluation`,
  `projectiveBundleUnit`, `projectiveBundleFormula`.
  The word is a list repeating quotient index j exactly w j times. Its length is
  the sum of the exponents. `flagOrderedCup` takes its cup product in the published
  ordered power presentation, so the summand, evaluation and pullback are exactly
  those of the recorded projective-bundle formula. The construction only iterates
  the same tensor, evaluation and adjunction maps;
  it introduces no new notion of a twist or projective bundle.
- `Sheaf.Paper.SupportedHomPullback`: `proEtaleSupportHomPair`,
  `proEtaleSupportHomTransport`, `SupportHomPair.Identification` and `Transport.derivedMap`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` supplies
  `Padic.finite_coefficientExtensionRing`. `supportedProjectionRetraction` specializes the
  raw equation with this published finite-quotient theorem and `Finite.of_equiv` for
  the size lift. Mathlib's finite-ring Noetherian instance and the published
  flat-module pullback instance then form the actual projection map. This adds no
  hypothesis or new finiteness assertion.
- All thirteen recorded proof-dependency modules are directly imported. The docstring
  carries each of the node's six proof steps and the normalization calculation.

Edge cases checked before writing: rank zero has an empty Chern word and identity
projection; rank one has only the zero exponent and identity projection; rank two has
the two P^1 components. Empty base, empty support and full support are admitted.
Negative degrees give zero for these degree-zero sheaves; negative twists use the
published dual lines and are not excluded. Singular or nonreduced Z is unrestricted.
The arbitrary closed subscheme structure affects no kernel-of-restriction argument.
The supported groups and site universes remain those of the dependencies.
The pullback is expressed through the existing `Transport.derivedMap`; the normalized
identifications relate it to `Transport.homMap` in the same derived-category universes.
The signed Tate coefficient has the etale origin required by the recorded comparison.

Searches for an existing statement:

- msearch leanfinder: "Pullback along a complete flag bundle is a split injection on
  cohomology with arbitrary closed support". Eight hits, including a Nobeling exactness
  result and group-cohomology maps; no flag-bundle supported-cohomology result.
- msearch loogle: `"IsSplitMono", "biproduct"`. One hit,
  `Functor.instIsSplitMonoBiproductComparison'`, not the geometric statement.
- msearch grep: `flag.*[Ii]nject|flag.*[Ss]plit|supported.*pullback`. One unrelated
  order-theoretic Flag action, no match.
- msearch leansearch: "Cohomology with support pullback along a complete flag bundle
  has a left inverse from the projective bundle formula". Eight unrelated bundle,
  Proj-chart, module-projectivity and pullback-functor hits; no match.
- rg over the slopmaster2 WeilConjectures sources and side lean/Sheaf:
  `flag.*(split|[Ii]nject)|[Ff]lag.*[Pp]ullback|lem-pur-flag-pullback-injective`.
  Only unrelated filtered-Hom material and the actual flag kernel local splitting.
- rg over dag/lean_names_upstream.json for flag/Flag finds only invariant flags in
  representations. None of the proposed declaration names is already present.

No statement correction, dependency repair or mathematical dispute.
The isolated stage-1 typing dispute was already resolved by the explicit rank in this
node and its reviewed flag dependency; it does not carry over to this statement.

## Second reading by Q67

The dispatcher explicitly prohibits starting another agent. This section records a
separate fresh reading by the same worker; the maintainer's independent review is the
review described in the dispatch brief. No independent worker review is claimed.

I reread the node and Lean together, checking each hypothesis and each conclusion as
listed above. Exact and left-derived inverse-image coordinates are connected by
the published comparison, and both shifted right-adjoint comparisons are explicit.
The normalization clause kills only
bounded nonzero Chern words. Killing every positive monomial would be false, since
powers above the projective relation can have a base-Chern-class component. The bounds
`w j <= j` are essential and agree with the recursively defined quotient-line tower.
The source and target use the published supported groups, and all auxiliary maps are
real constructions or canonically normalized structures. No additional assertion of
purity, descent, smooth support or a global splitting of the vector bundle appears.

## New nodes

`def-pur-supported-projection-splitting`, module
`Sheaf.Paper.SupportedProjectionSplitting`, defines
`WeilConjectures.PurityFiniteSetting.supportedProjectionSplitting`.
It supplies the missing notion of a supported splitting prescribed by a coefficient
projection and the actual projection formula. The existing SupportedHomPullback
interface supplies the normalized Hom identification and the canonical pullback, but
no predicate or map for a retraction prescribed by a coefficient projection. The new
node defines that predicate by the exact equation for rK, the shifted adjunction, the
additive left-inverse identity and the induced-Hom normalization. It asserts no
existence and adds no assumption to the flag theorem. All definitions have real data.
The flag theorem supplies its bounded-Chern component condition and the signed Tate
coefficient. The original node gains only this statement dependency and its lean record.

The definition's hypotheses are: finite coefficient datum P; arbitrary f, two closed
supports i,i'; bounded-below coefficient K; integer degree b; and a predicate on the
coefficient projection. Its clauses are exactly the witnesses chi, chi', e, rho, rK,
and s and their component, projection, left-inverse and supported-Hom equations,
as expanded in the hypothesis-and-clause correspondence above. No regularity,
constructibility or existence assumption is imposed by the definition.

Searches for this notion: leanfinder returned eight unrelated degreewise-splitting and
Lie-extension constructions; leansearch returned eight general presheaf adjunction,
group-cohomology and Kaehler-retraction results; loogle on
`"rightAdjointProjectionMap", "IsSplitMono"` returned zero hits; Mathlib grep on
`supported.*[Ss]plit|[Pp]rojection.*[Rr]etraction|[Rr]etraction.*[Pp]rojection`
returned two unrelated Finsupp comments. Source and side searches found no such
prescribed supported-splitting definition. `blueprint_refs.py search` returned zero
matches for `supported projection splitting`. The node stores the search responses.
Its blueprint ancestor is `thm-pur-localized-top-chern`, Step 1.

For the new definition, the identity map with its identity coefficient projection
reduces to the identity supported splitting. A false component predicate gives a
false splitting predicate, as expected for a definition rather than an existence
axiom. Empty supports and negative degrees do not force a spurious coefficient
projection: the rho condition remains present even when the cohomology groups vanish.

## Saved-packet repair

The initial dry run rejected `FlagHomProbe.lean`, an unregistered diagnostic module.
It is retained under `scratchpad/` and excluded from the delivery. The helper declaration
list was synchronized with the saved source (`supportedProjectionComposeUnitIso`).
The current node, source Step 1, published flag and projective-bundle interfaces, and
normalized supported-Hom transport were reread. The statement still includes all ranks,
all signed twists and degrees, and arbitrary closed support with the prescribed splitting.

The saved helper exposed expensive concrete instance comparisons during kernel checking.
Its shift, unit-action projection equation and additive splitting calculation are now
generic definitions specialized to the same published functors. Supported pullback is
expressed directly as homology of `Transport.derivedMap`, retaining the canonical map
even before the etale-origin supported-Hom compatibility is applied. The normalized
Hom equation still specifies the same retraction; no mathematical hypothesis changed.

The final same-worker reading also unfolds `supportedProjectionAdditiveSplitting`: its
`chi` arguments are the already normalized additive identifications used as functions;
no arbitrary functions or new identifications are quantified. It expands to the original
left-inverse and induced-Hom equations. The generic homology helper takes the published
`HasDerivedCategory.ofIsGrothendieckAbelian` instance explicitly and changes no site
or coefficient universe. The original item statement remains verbatim.
