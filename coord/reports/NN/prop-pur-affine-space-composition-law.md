## Worker report

This delivery states the affine-space composition law in
`Sheaf.Paper.AffineSpacePurityComposition`, using the published
`AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurityComparison`.
The original mathematical statement is unchanged. No theorem is proved.

Hypotheses and clauses, in order:

- The finite-field, coefficient prime, finite extension, and positive coefficient
  level are the fields of `P : WeilConjectures.PurityFiniteSetting`. `Ring P`
  means `AffineLinePurity.Ring P`, the existing lifted finite quotient at level
  `P.level - 1`, with its canonical identification with the positive-level ring.
  In particular no divisibility of the level by the ramification index is assumed.
- A separated finite-type k-scheme is `Y`, its structure map `aY`, and the instances
  `LocallyOfFiniteType aY`, `QuasiCompact aY`, `IsSeparated aY`.
- The finite-Tor bounded constructible input is represented exactly as in the
  dependency by `K : Plus (Ring P) Y`, `Ke`, `hKe : etaleFiniteTor ... Ke`, and
  `eK : (comparison ...).obj Ke ≅ K.obj`. The representative and its identification
  are witnesses of the original domain, not extra mathematical restrictions.
- The natural numbers `d,e` index positive dimensions `d+1,e+1`. Every pair of
  dimensions at least one occurs. The total dimension is `(e+1)+(d+1)`, equal to
  the source's `(d+1)+(e+1)` by addition commutativity.
- The projections are the existing `iteratedAffineLineProj`. `blockSchemeEq`
  constructs the parenthesis identification recursively by congruence of the
  affine-line construction. `blockProjection` supplies its projection equation.
- The first conjunct compares `transportedComparison` for that fixed identification
  with `blockComposite`. The latter literally composes `blockSourceIso.hom`,
  `projectionSource.map` of the e-dimensional comparison, the d-dimensional
  comparison at the exceptional image, and `compositionInverse`. Thus it renders
  every factor, including the inverse c and the canonical source reassociation,
  in the displayed formula. `stage_applicability` supplies the intermediate input's
  boundedness and finite-Tor constructibility; neither is assumed separately.
- The second conjunct is the Koszul scalar `(-1 : ℤ)^((2*(d+1))*(2*(e+1))) = 1`.
  Replacing both even degrees by their negatives gives the same exponent.
- The last conjunct says that the actual comparison equals its transport by
  `coordinateIso` for `blockPermutation`. `coordinateMap` is the polynomial map
  given by the existing coordinate universal property, rather than an arbitrary
  scheme automorphism. The permutation interchanges the outer d-block and inner
  e-block (coordinates of the iterated model are outermost first).
  This is the equality of the two coordinate orders, in addition to regrouping.

Canonical transports contain real data. `actionAddIso` rebrackets iterations;
`twistPullbackIso` iterates the published inverse-image tensor comparison and
`shiftedLinePullback`; `coordinateSourceIso` uses the pullback compositor.
`isoExceptional` uses the ordinary etale adjunction-normalized isomorphism for a
scheme isomorphism and the bounded-below comparison unit. `transportedComparison`
then uses `compositionInverse`, the actual transpose of the pasted counit, and
`rightDerivedUpperShriekCongr`. No arbitrary map, orientation or purity
isomorphism is supplied. `positiveComparison_existsUnique` fixes its hom by HEq
to the published comparison and only changes its endpoint coordinates.

The named postponed statements are `blockProjection`, `coordinateMap_isIso`,
`coordinateProjection`, `exceptionalPositive_obj_eq`, `positiveComparison_existsUnique`,
and `affineSpacePurityComposition`. Each has
this node's blueprint tag and a complete natural-language proof plan. The other
declarations are constructions or instance adapters from existing properties.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`, its
  projection and coordinate universal property. The existing iterated model is
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace.iteratedAffineLine` in
  module notation; its declaration namespace is `AlgebraicGeometry`.
- `Sheaf.Paper.AffineSpacePurityComparison`: `affineSpacePurityComparison`,
  `orderedSource`, `exceptional`, `twistAction`, `shiftedLinePullback`,
  `inverseImageComp`, `stageEtale`, `stageComparison`, `stage_applicability`,
  `tower_geometry`, `tower_noetherian`, and `compositionInverse` in
  `AlgebraicGeometry.ProEtale.AffineSpacePurity`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and its publicly imported
  finite twists: the existing finite coefficient line used by `shiftedLine`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System` and its publicly imported
  `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt`; the finite specialization
  is the dependency's `rightDerivedUpperShriek`, not a new adjoint assumption.

Edge cases checked: the smallest dimensions are both one; empty Y and zero K
are included; the finite coefficient level can be one or ramified; no odd
shift is moved across K; the coefficient and small-site universe u+1 is retained
with scheme universe u. The auxiliary coordinate construction also permits zero
coordinates. The total projection is never asserted to be an ambient pro-etale
right adjoint: only the published bounded-below etale-origin Hom bijection is used.
No disputed statement or statement correction.

Searches:

- `msearch.py leanfinder`: "Affine space purity comparison is compatible with
  composition and permutation of coordinates" returned eight results, all affine
  reindexing or simplex identities, not a purity-comparison composition theorem.
- `msearch.py loogle`: "AffineSpace, affineSpacePurityComparison" returned zero
  results and the diagnostic `unknown identifier AffineSpace`.
- `msearch.py grep`: `affineSpacePurity|[Pp]urity.*[Cc]omposition` in
  `AlgebraicGeometry` returned zero results.
- `rg` in both project roots for `affineSpacePurityComparison`, and the exact
  blueprint id in `WeilConjectures`, found only the recorded ordered-comparison
  definition and no existing theorem. Coordinate searches found the existing
  `toIteratedAffineLine` constructor and its projection/coordinate equations,
  which this delivery uses. No new independent notion is introduced.

## Second reading by NN

I made a separate pass over the node and the module, checking all three
conclusions rather than only regrouping. In particular the last conjunct uses
an actual block coordinate permutation; it is not merely the same iteration
with two parentheses. Both extraordinary target transport and ordinary source
transport are specified canonically. The intermediate exceptional input uses
the dependency's theorem, and the etale-origin witnesses are retained. The
positive-dimension indexing includes exactly every d,e >= 1. The independent
maintainer review requested by the dispatcher remains the external second reader.

The proof-only imports include every recorded proof-dependency module currently
stated. The following proof dependencies have no recorded declaration yet:
`prop-sf-pf-coherence`, `lem-pur-affine-space-product-domain`,
`lem-pur-affine-space-trace-factorization`, and `lem-sf-kunneth-coherence`.
The three other dependencies without a lean record are Mathlib leaves: finite-type
Noetherianity, composite adjunction, and mate pasting; their Mathlib modules are
imported. The affine-space statement requires no new dependency or correction.

Compiler repair: direct unfolding of normalized exceptional objects caused an
elaboration timeout. `exceptionalPositive_obj_eq` makes that definitional endpoint
identification explicit, and `positiveComparison_existsUnique` retains the exact
original morphism via HEq. `coordinateProjection` exposes the polynomial
permutation's projection equation without unfolding the entire scheme/derived
transport in the proposition. These are coordinate adapters for this node, not
new mathematical operations. Diagnostic prefix files are removed before delivery.

The two morphism equations use `HEq` on their displayed, canonically transported
arrows. Their source and target are the same fixed projection-source and
exceptional-image objects. Thus HEq is equivalent to homogeneous equality here;
no map, clause or identification is omitted. This prevents the elaborator from
normalizing the entire derived-functor construction while checking an equation.
The compactification instance arguments of `transportedComparison` are supplied
explicitly in the proposition and derived by the helper constructions, never
assumed as extra hypotheses.

Validation: the complete delivered module passed scompile.py in both sandbox and
library mode, with no warnings or errors (15.3 s and 14.1 s respectively, within
the unchanged 60 s limit). No diagnostic probes or #check commands remain.
