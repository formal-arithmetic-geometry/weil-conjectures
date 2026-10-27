## Worker report

The module `Sheaf.AlgebraicGeometry.TraitGenericEffectiveDenseAffine` states
`AlgebraicGeometry.trait_generic_effective_dense_affine`, with `sorry` as its entire proof.
There are no new definitions, dependency modules, or statement corrections. The item's
natural-language statement, dependency lists, and proof plan are unchanged.

Source read: Bosch--Lütkebohmert--Raynaud, Néron Models, §6.5 Theorem 1 proof,
printed pp.160--162 (scan pp.166--168), especially the general smooth-scheme reduction
on p.162 and the affine shrinking on p.160. The primary scan is
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
It explicitly removes the torsor/group hypotheses for the dense effective open argument.
The declaration docstring contains all eight proof steps and their source-node references.

Hypotheses and clauses, matched individually:

- The commutative DVRs are `B C : Type u` with `CommRing`, `IsDomain`, and
  `IsDiscreteValuationRing` instances. This excludes fields exactly as the recorded
  DVR definition does. `r : CommRingCat.of B ⟶ CommRingCat.of C` and
  `hr : r.hom.FaithfullyFlat` give the specified faithfully flat ring homomorphism.
- `K L : Type u`, `Field K`, `Field L`, `Algebra B K`, `IsFractionRing B K`,
  `Algebra C L`, and `IsFractionRing C L` specify arbitrary models of the fraction
  fields, not arbitrary larger field extensions. `s` and `hs` present the induced
  map between these models: it extends `r` on B. It is uniquely determined by this
  equation, and exists because a faithfully flat ring map is injective. These are
  presentation data for the node's field extension, not an additional restriction.
- `Spec (.of B)` and `Spec (.of C)` are S and S'. The over-category object `X`
  supplies X' and its structure morphism `X.hom`. Its `Smooth`, `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` instances are exactly smooth, separated,
  and finite type; `IsSeparated` is the Mathlib closed-diagonal predicate.
- `D : Over.DescentDatum (Spec.map r) X` is the recorded transport-form descent
  datum, including naturality, identity, and cocycle, without group data.
- `X₀ : Over (Spec (.of K))` is the specified descended generic scheme. `e₀` is an
  actual isomorphism from its L-base change to `X'_L`, with `he₀` expressing that
  it is over Spec L.
- `hgeneric` says that the X₀-coordinate `e₀.inv ≫ pullback.fst` is unchanged by
  D on the generic fibre: `D.transport ... a = b` and the two projection equations
  specify the related points and their generic lifts `aL`, `bL`. A generic lift
  exists whenever the point is generic, and it is unique because localization
  gives a monomorphism Spec L → Spec C. For related generic points the Spec K
  coordinates also agree, since Spec K → Spec B is a monomorphism. Thus this is
  precisely compatibility of e₀ with the restricted datum, not merely generic
  isomorphism of the schemes. Yoneda on all `T : Scheme.{u}` detects this equality.
- The existential `U : Over (Spec (.of B))` supplies an S-scheme, and
  `IsAffine U.left` makes it affine. `W : X.left.Opens` is U'; `IsAffine W.toScheme`
  makes the open subscheme affine, and its inclusion is the standard open immersion
  `W.ι`, without a separately assumed open-immersion hypothesis.
- The equality `(pullback.fst ...) ⁻¹ᵁ W = D.toHom ⁻¹ᵁ W` is invariance. Its domain
  is X' ×_S S'. The two arrows are the source projection and the target of universal
  transport. Via the usual pullback identifications this is exactly
  α(p₀*W) = p₁*W over S' ×_S S'. It imposes equality of actual opens, not merely
  equality on rational points.
- For every algebraically closed `Ω : Type u` and `g : Spec (.of Ω) ⟶ Spec (.of C)`,
  `Dense ((pullback.fst X.hom g) ⁻¹' (W : Set X.left))` says W is dense in that
  geometric fibre. The subset is precisely the inverse image open in the actual
  fibre-product scheme. Every geometric fibre has an algebraic-closure model in
  this universe; density for all such models is invariant under larger extensions.
- `q : W.toScheme ⟶ U.left` and `IsPullback q (W.ι ≫ X.hom) U.hom (Spec.map r)`
  supply the actual cartesian realization. `IsPullback.isoPullback` yields
  W ≅ U ×_S S', whose inverse is the requested isomorphism. The following universal
  equation `aW ≫ q = bW ≫ q` whenever a,b are D-related and aW,bW lift them through
  W.ι says that q is invariant under the restricted datum. The lifts exist by
  invariance and are unique since W.ι is monic. This is exactly the invariance
  clause in `DescentDatum.IsEffective`, for this specified U and q, so the
  cartesian realization realizes the datum as well as the underlying scheme.
- `i : pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap B K))) ⟶ X₀.left`,
  `IsOpenImmersion i`, and the equation with X₀.hom give the requested K-open
  immersion U_K → X₀. In the last clause, the first equation identifies aL with
  the inclusion of aW in X'_L; the next two equations constrain b to its uniquely
  determined corresponding point of U_K, through q and the field map s. The
  conclusion `b ≫ i = aL ≫ e₀.inv ≫ pullback.fst ...` says its X₀-coordinate is
  the prescribed one. Such b exists by the cartesian square, the generic lift,
  and hs. Testing all schemes is equivalent by Yoneda to the base-change square
  commuting. No arbitrary unconstrained comparison map replaces base change.

Dependency declarations read and used:

- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat` in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, and `RingHom.FaithfullyFlat` in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat` (the latter is the bare-map form used).
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, together with `IsDomain`.
- `def-weil-affine-spectrum`, `def-pc-scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme`, `Scheme.Hom` in `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-closed-immersion`: `IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, used through
  `IsSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-pd-descent-datum`: `CategoryTheory.Over.DescentDatum`, its `transport`,
  `toHom`, and `IsEffective` interface in
  `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`. Invariance of a
  specified realization is stated by expanding the recorded IsEffective clause,
  so no second descent-data definition is introduced.
- `def-pc-base-change`: recorded module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` imported publicly;
  actual scheme base changes are its documented `Limits.pullback`, with fst/snd,
  not its unrelated module-sheaf base-change functor.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` from
  `Mathlib.AlgebraicGeometry.OpenImmersion`, and standard `Scheme.Opens.ι`.

All recorded modules of stated proof dependencies are imported as proof imports.
Proof dependencies with no recorded Lean module remain unstated in this delivery;
the module's proof docstring records their roles. No import cycle was introduced.

Edge cases checked: X' empty, X₀ empty, and empty special fibres require no
nonempty type or fibre hypothesis. The empty affine open is allowed. For a nonempty
geometric fibre density prevents the empty open from qualifying. Geometrically
reducible and disconnected fibres are tested in full, rather than at a single
chosen component. No finite/algebraic/separable restriction is imposed on L/K,
no completeness or unramifiedness is assumed, and no group law is present.
The test scheme/field universe is the scheme's universe, so these universal
conditions do not become vacuous by selecting an independently smaller universe.

Searches made (no exact theorem found):

- `msearch.py ... leanfinder`: "A smooth separated finite type scheme over a
  discrete valuation ring with generically effective descent datum admits an
  invariant affine open dense in every geometric fibre". Eight hits, including
  `IsSeparated.hasAffineProperty` and affine-cover/affine-transition lemmas;
  none states this result.
- `msearch.py ... loogle`: "DescentDatum, IsEffective, IsAffine". Zero hits;
  Mathlib's index does not contain the project's DescentDatum identifier.
- `msearch.py ... leansearch`: "A generically effective descent datum on a smooth
  separated scheme of finite type over a discrete valuation ring admits a
  fibrewise dense invariant affine open". Eight hits, including
  `HasAffineProperty.descendsAlong_of_affineAnd`, small-affine-site density, and
  `IsSeparated.hasAffineProperty`; none states this result.
- `msearch.py ... grep`: `generic.*effective|effective.*generic|DescentDatum`,
  restricted to AlgebraicGeometry in Mathlib: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `generic.{0,30}effectiv|effectiv.{0,30}generic`: only unrelated generic Cartier
  divisors and formal-blowup text. The required `grep -rn` for the item's ID in
  `lean/WeilConjectures` found no occurrence. A declaration-name search for
  `trait_generic_effective_dense_affine` across Mathlib, WeilConjectures, Sheaf,
  and `dag/lean_names_upstream.json` found none.
- Broader descent searches located the existing `DescentDatum.toHom` interface
  and the invariant-open modules; their transport descriptions agree with the
  statement above. No invariant-open definition is reimplemented.

Validation: scompile.py compiled this module against the live published library
in sandbox mode and at its actual module path, both clean (2.1 s each) after the
line-width repair. An initial bundled CommRingCat presentation with independent
Field instances caused a definitional-equality heartbeat failure; replacing the
rings by Type u with coherent CommRing/Field instances removed it without any
mathematical change. No limit was raised. Only the designated theorem has sorry.

## Second reading by Q157

Author's second pass, not an independent worker review: the dispatcher forbids
starting other agents; the maintainer supplies the independent review. I reopened
the node and the final signature and checked every hypothesis and conclusion
against the mapping above. In particular, generic effectivity includes the actual
e₀ and its transport compatibility; the realized affine open includes both the
cartesian square and invariance of q; and the final K-open immersion includes its
structure map and compatibility with e₀. I checked that all quantified auxiliary
maps are fixed by projection/transport equations and have actual lifts, so no
vacuous compatibility clause weakens the claim. The ring-instance mismatch and
one line-width issue found during compilation were repaired. The node's own
statement requires no correction, and no statement is marked disputed.
