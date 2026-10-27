## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.smoothIntegralFibreVerticalDivisors`
in `Sheaf.AlgebraicGeometry.SmoothIntegralFibreVerticalDivisors`, with its proof `sorry`.
There is no change to the item's mathematical statement. Two new definition nodes supply
an arbitrary represented-target version of the existing structural geometric-fibre
condition and locally finite, rather than globally finite, divisor coefficients.
Definitions have concrete data. The three postponed subgroup-closure theorems are explicitly
part of the locally finite definition node's statement and have natural-language proofs.

Hypotheses and objects, clause by clause:

- An arbitrary scheme base is `T.left`, for `T : Over (Spec (.of (ULift.{u} ℤ)))`.
  Every scheme has its unique map to this terminal scheme; this encoding neither assumes
  a separated base nor restricts its characteristic. The space is an arbitrary
  `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))` and the given map is
  `p : X ⟶ schemeSpace T`. Working over Spec Z allows both arbitrary base changes and
  absolute separatedness to be expressed without changing the ambient presheaf category.
- Regularity and local Noetherianity are exactly `hT : IsRegularScheme T.left`.
  Its definition is `IsLocallyNoetherian T.left ∧ IsRegular T.left`.
- Separatedness, smoothness and finite presentation are `hp : SmoothIntegralSpaceMap p`:
  this unfolds to `MapIsLocally (@Smooth) p`, `MapIsSeparated p`,
  `MapIsLocallyOfFinitePresentation p`, `MapIsQuasiCompact p.hom.hom`, and
  quasi-compactness of the relative diagonal. These are the recorded scheme-chart
  and closed-diagonal predicates, including quasi-separatedness in finite presentation.
- The last clause of `SmoothIntegralSpaceMap` quantifies over every algebraically closed
  field in the scheme universe and every `Spec K ⟶ T.left`. The actual sheaf fibre
  product has `IrreducibleSpace` point space, which includes nonemptiness, and every
  representable étale scheme chart is reduced. This uses the existing geometric-fibre
  convention from `GroupSpaceIntegralFibres`, generalized to a specified map to `h_T`.
  It assumes no group structure or section. The fibres are separated of finite
  presentation over a field, so decency is automatic; thus reducedness and
  irreducibility express the usual integral-fibre condition (Stacks 0AD4).
- The dense open is `V : T.left.Opens`, `hV : Dense (V : Set T.left)`.
  `schemeOpenPointSet T V` is its actual image in represented point classes.
  Its inverse image under `mapPoint p.hom.hom` is precisely the point subset of X_V.

Conclusions, clause by clause:

- `VerticalDivisorIdentification` first says every étale scheme chart of X satisfies
  `IsRegularScheme`, hence X is regular and locally Noetherian. Its next conjunct is
  density of the actual inverse image of the open point subset.
- `VerticalDivisorAffineFiniteness p` quantifies over all affine opens U of T.left.
  Its actual sheaf base change has compact point space and a separated structural map
  to the terminal presheaf. The terminal base is Spec Z, so this is separatedness over
  Spec Z, not merely relative separatedness over an arbitrary nonseparated scheme.
  Together with chart regularity this is exactly Noetherianity and separatedness of X_U.
- `SupportedLocallyFiniteDivisors B W` is the additive subgroup of coefficient
  functions on the EXISTING `SpacePrimeDivisor B`. The family of prime closures with
  nonzero coefficient is locally finite and each such closure is disjoint from W.
  No quasi-compactness or finite-support condition is imposed globally.
- The displayed `e : ... ≃+ ...` identifies the two required supported divisor groups.
  The `MapIsFlat p` witness is a conclusion, not an extra hypothesis. Every D and e D
  satisfy `IsLocallyFiniteDivisorPullback`, which is characterized by the existing
  local-equation Cartier pullback and the existing normalized chart orders.
- The two `∃! C : SpaceCartierDivisor ...` clauses identify supported locally finite
  Weil divisors with actual sections of the sheafified K×/O× quotient. This reuses
  `SpaceCartierDivisor`, rather than replacing Cartier divisors by global equations.
- The equivalence `r` matches ALL prime divisors disjoint from the respective opens.
  Its closure equality is `|r z| = |p|⁻¹(|z|)`, so it says both existence and
  uniqueness of the base prime. Point codimension is the recorded chartwise one.
- For every base prime z there exists a reduced closed subspace Z with precisely
  that prime closure as image. `enlargedFibreProduct p Z.val.arrow` is the actual
  scheme-theoretic inverse image, is reduced and irreducible, and its image is the
  prime closure selected by r. The inherited separatedness gives decency, so this
  is integral with reduced structure, not just a statement about abstract point sets.
- The singleton coefficient formula says e sends coefficient 1 at z (zero elsewhere)
  to coefficient 1 at r z (zero elsewhere). Thus multiplicity is exactly one, and
  there are no other divisor components. Singleton coefficient families belong to
  the subgroup because a family with at most one nonempty term is locally finite;
  the displayed conditional singleton formula excludes no prime.
- Locality on the base is rendered by the `∀ U : T.left.Opens` clause: the actual
  open restriction again satisfies the smooth integral-fibre condition and has
  its own vertical-divisor identification, compatible with e through normalized
  Cartier pullback. This is not restricted to affine U.
- For EVERY `T'` and `a : T' ⟶ T` with `Etale a.left`, the final clause gives
  `IsRegularScheme T'.left`, density of `a.left ⁻¹' V`, the full smooth integral-fibre
  condition on the actual second projection, affine finiteness, and a divisor
  identification e'. There is no quasi-compactness or separatedness hypothesis on a.
- The final witnesses ha and hb give flatness of the actual two vertical arrows.
  For every D, its base pullback D' exists uniquely. Whenever D' is that pullback,
  e' D' is the normalized Cartier pullback of e D along the actual first projection.
  This is the commutative base-change square. It does not assume that étale pullback
  maps a prime to one prime, and covers splitting and the identity map.

Recorded dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`;
  its upstream regular class and Mathlib local-Noetherian class are reused.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `EtaleSite`, `etaleForget`, and `structureSheaf`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  scheme opens use their canonical inclusion and inverse-image opens.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsSeparated`, `MapIsLocallyOfFinitePresentation`, `MapIsFlat`.
- `Sheaf.AlgebraicGeometry.RegularGroupSpace`: `groupSchemeMap`, using the existing
  representable scheme embedding and its Yoneda morphisms. The specialized
  `GroupSpaceIntegralFibres` and `IsSmoothIntegralGroupSpace` were read; they only
  apply to the structural projection, not an arbitrary p after base change in this
  fixed ambient category. No group datum is imported into the theorem's assumptions.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`.
- `Sheaf.AlgebraicGeometry.SpaceDivisorDefinitions`: `SpacePrimeDivisor`,
  `SpaceCartierDivisor`, `SpaceCartierDivisor.HasEquation`. `SpaceWeilDivisor`
  is finite support and is therefore not substituted for the node's group.
- `Sheaf.AlgebraicGeometry.SpaceDivisorPullback`: `divisorChartOrder`,
  `divisorBasisChart`, `divisorFractionUnit`, `SpaceCartierDivisor.IsFlatPullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`: `ClosedSubspace`.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`: `IsReduced`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology` and `ProperCurveModuli`:
  `Point`, `schemePointMap`, `pointImage`, `mapPoint`, `MapIsQuasiCompact`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsSeparatedPresheafMap`.

The already recorded proof-dependency modules are imported privately, including
`RegularSpaceDivisorLineDictionary`, `ReducedClosedSubspaceSupport`,
`AlgebraicSpaceLocalDimensionChartInvariance`, and `RegularPrimeDivisorLocalEquations`.
Mathlib-matched proof dependencies without a lean record are also imported:
`Morphisms.Separated`, `Flat.FaithfullyFlat.Basic`, `Flat.FaithfullyFlat.Algebra`, and
`Ideal.KrullsHeightTheorem`. The remaining proof dependencies with no recorded module
are not invented or added as assumptions: their proof steps remain in the docstring.
There is no dependency-module repair.

Edge cases checked: the empty base and its empty spaces give trivial divisor groups;
V=T gives zero supported divisor groups; the empty restriction U is allowed; a
nonempty base excludes an empty X by the nonempty-fibre condition; relative dimension
zero and positive relative dimension are both included; there is no characteristic
restriction; infinite disjoint unions of regular affine bases allow genuinely infinite
locally finite families; a nonseparated base is allowed, with absolute separatedness
asserted only over affine opens; an arbitrary non-quasi-compact or nonseparated étale
a is allowed; split étale pullbacks use coefficient sums through the Cartier relation.
No counterexample or statement dispute was found.

Searches for the item and the new notions:

- `msearch.py ... leanfinder` with "Smooth morphism with geometrically integral fibres
  induces an isomorphism of vertical Weil divisor groups over a regular base" returned
  smooth affine/base-change results and scheme normalization, no divisor theorem.
- `msearch.py ... loogle` with "AlgebraicGeometry.WeilDivisor, AlgebraicGeometry.Smooth"
  returned 0 hits, unknown identifier AlgebraicGeometry.WeilDivisor.
- `msearch.py ... grep` with "vertical.*[Dd]ivisor|[Dd]ivisor.*vertical|CartierDivisor|WeilDivisor"
  in AlgebraicGeometry returned 0 Mathlib hits.
- `rg` of the item's id and the vertical-divisor patterns in both WeilConjectures and
  Sheaf found only references in AffineCellPicardProduct and RigidifiedLineExtension;
  NormalGroupVerticalCartierDescent is a different theorem: schemes, groups, a normal
  integral base and an identity section, not the present general space statement.
- `msearch.py ... leansearch` with "Locally finite Weil divisors on algebraic spaces"
  returned `LocallyFinite` and unrelated scheme finiteness notions. Loogle
  "LocallyFinite, ℤ" returned 0. LeanFinder on locally finite integer coefficients
  returned affine-fraction and coherent-ideal declarations, no divisor carrier.
- `msearch.py ... leansearch` on smooth separated finitely presented space maps with
  integral geometric fibres returned only scheme smoothness/properness notions.
  Loogle "AlgebraicGeometry.GeometricallyIntegral, AlgebraicGeometry.Smooth" returned 0.
- `rg` of LocallyFinite/divisor and the new names in Mathlib, WeilConjectures and Sheaf
  found no exact carrier or declaration. Source scheme `GeometricallyIntegral` applies
  to scheme morphisms. The existing group-space predicate was read and reused at the
  component level as described above.
- DAG searches and `tools/blueprint_refs.py search 'locally finite' 'divisor'` found
  0 blueprint nodes. `def-sfb-space-divisors` is the finite-support notion, while
  `def-sfb-smooth-integral-group-space` is the structural-projection specialization.
  `tools/blueprint_refs.py ancestor` returns null for this inherited blueprint chain;
  both new nodes retain that null ancestor and prefix the item's via chain.

Source reading: the complete eight-step item proof, all eight original statement
dependencies, the current blueprint unit and its direct-images proof (latest snapshot),
Stacks algebra.tex Tag 00ON, descent.tex Tag 036D, and the recorded divisor definitions
and dictionary. The official Stacks pages for 00ON and 036D were also checked.
The current blueprint unit's own statement is unchanged.

Validation: all three modules compiled separately through the prescribed scompile.py
wrapper against the published live library. No error or warning beyond expected sorry
warnings. Initial elaboration issues (parentheses and explicit classical decisions in
singleton coefficients) were repaired; there are no diagnostic commands or auto-bound
variables in the final modules. The dry run is recorded below when complete.

## New nodes

`def-sfb-smooth-integral-space-map`, module
`Sheaf.AlgebraicGeometry.SmoothIntegralSpaceMap`, states the chartwise properties and
nonempty integral geometric fibres for p:X→h_T, plus the actual base-change second
projection. Its source is Stacks 03ZE, 03KL, 042S and 0AD4. The existing group-space
node supplies only the structural map to the represented ambient base; changing
represented targets in the same ambient category needs this general interface.
It uses the existing property tests, scheme embedding and fibre products throughout.
The searches and their returned declarations are recorded in its mathlib_searches.

`def-sfb-locally-finite-space-divisors`, module
`Sheaf.AlgebraicGeometry.LocallyFiniteSpaceDivisors`, defines the exact supported
locally finite subgroup of integer coefficients on the existing prime classes,
the represented open point subset, and normalized Cartier/Weil coefficient and
flat-pullback relations. Its source is Stacks 0BE0, 0BE2, 0BE3, 0DMM, 0EN9 and 0EPQ.
The old `SpaceWeilDivisor` permits only finite support and cannot represent the
node's noncompact cases. The new carrier reuses every prime class, Cartier section,
local fraction and order map; it copies no existing geometric notion. Its three
named postponed proof obligations establish the explicit subgroup's closure laws,
which the new node states. Searches are recorded in its mathlib_searches.

## Second reading by Q37

The author reread the node and all three completed files side by side. The dispatcher
explicitly forbids starting other agents; the independent reading is the maintainer's
review, not falsely claimed here. This second pass checked every hypothesis and
conclusion against the map above. It specifically confirmed that the ambient category
is over Spec Z, the base is arbitrary, finite presentation includes quasi-compactness
of the diagonal, irreducibility includes nonemptiness, and no group law is assumed.
The support carrier allows infinite locally finite families. The r-equivalence,
reduced closed-space pullbacks and complete singleton-coefficient equality give both
uniqueness and multiplicity one. Both dictionaries are actual Cartier sections with
normalized equations. Every base-change projection is the actual sheaf projection.
The étale square includes existence and uniqueness of its base divisor pullback and
allows prime splitting. Open restrictions include all opens, and absolute finiteness
is asserted only for affine opens. No statement correction was needed. This pass also
added the Mathlib-matched proof imports and the complete dependency plan to the proof
docstring. The three closure theorems correspond exactly to the new definition node's
zero/addition/negation clause, and no definition data is postponed.

Dry run: `deliver2.py Q37 lem-sfb-smooth-integral-fibre-vertical-divisors --no-push`
reported `OK (dry run): commit 8d3a1795667 passes the preflight and compiles; nothing pushed`.
The first dry run found a truncated lean.statement record because its extractor stopped
at `:=` in an explicit named argument. The record was replaced by the exact complete
signature ending at the theorem's proof delimiter, and the second dry run passed.
The route-pivot private-import advisory names RegularPrimeDivisorLocalEquations; it
is an explicit proof dependency in this item's reviewed eight-step proof, needed for
the local prime equation and multiplicity-one computation in step 6.
