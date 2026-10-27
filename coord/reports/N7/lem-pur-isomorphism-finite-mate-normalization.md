## Worker report

The module `Sheaf.Paper.IsomorphismFiniteMateNormalization` states
`WeilConjectures.PurityFiniteSetting.isomorphismFiniteMateNormalization` with one
`sorry`. Its three construction helpers have real data and no postponed proof:
`finiteMateCartesian` applies the existing Cartesian-square theorem;
`finiteMateOpenReindexing` takes the uniquely adjunction-compatible left-adjoint
isomorphism of the canonical sectionwise right-adjoint square;
`finiteMateDerivedOpenReindexing` descends that exact comparison termwise.
No node statement, dependency interface, or definition is corrected.

Hypotheses and objects, clause by clause:

- `P : PurityFiniteSetting` supplies the finite-field datum, prime ell different
  from the characteristic, finite coefficient extension, valuation ring,
  uniformizer, and positive integer level. `P.Ring` is exactly O_E/(varpi_E^n).
  The existing `PurityFiniteSetting.ringFinite` instance supplies its finiteness,
  without a new assumption. No divisibility of n by a ramification index is imposed.
- `X.Over (Spec (.of P.field.k))` and the corresponding Y instance, with
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on both structure maps,
  give the separated finite-type k-schemes. The analogous properties of f and
  `f.IsOver` give the separated finite-type k-morphism.
- `g : Y' ≅ Y`, `g' : X' ≅ X`, and `b : c'.Z ≅ c.Z` are isomorphisms of
  underlying schemes. There is no `IsOver k` assumption on any of them, and no
  independently required k-structure on X' or Y'.
- `c : Compactification f`, `c' : Compactification f'`, and the two
  `ChosenCartesianSquare` arguments `sqP` and `sqJ` specify the proper and open
  Cartesian squares. This is the base-changed compactification represented with
  arbitrary chosen fibre-product models. Pasting gives the original Cartesian
  square; no extra choice of a compatible map is left implicit.
- All derived objects use `proEtaleDerivedCategory T P.Ring`, the ordinary
  uncompleted unbounded category of constant-ring module sheaves on the small
  pro-etale site (object universe u+1, morphism universe u). The recorded
  `sfIntrinsicDerivedPullback`, `proEtaleConstantDerivedDirectImage`, and
  `exceptionalOpenAdjunction` supply the actual functors and units/counits.

Conclusions, in the order of the six conjuncts:

1. The `mateEquiv` of `sfIntrinsicDerivedSquarePullback` under the actual
   `sfCartesianOpenPullPushAdjunction` adjunctions equals the hom of
   `sfProperOpenDerivedRestriction`. This identifies Ex_* with r as a natural
   transformation, rather than asserting that an unspecified map is invertible.
   The latter comparison is already a natural isomorphism.
2. For every unbounded M, pullback of r followed by the actual p'-counit equals
   theta followed by pullback of the actual p-counit. This is exactly the
   transpose `G_b(epsilon_p) ∘ theta` in the node.
3. The inverse of `finiteMateDerivedOpenReindexing` is the specified
   `sfIntrinsicDerivedOpenMate`. This identifies the canonical beta with the
   constructed reindexing isomorphism; beta is not supplied as an extra hypothesis.
4. For every unbounded K its inverse component is the inverse Hom-equivalence of
   `exceptionalOpenAdjunction c'.i P.Ring` applied to `G_g'` of the open unit,
   followed by `sfIntrinsicDerivedSquarePullback` at j_!K. This is the stated
   inverse-adjunction normalization, including the actual unit.
5. `SuppliedExchangeProjection.compactificationExchangeFromData` is specialized
   to the actual finite proper/open operations and the beta identified in (3).
   Its component equals r at j_!K followed by `Rp'_*` of beta_K, in that order.
   Both factors are homs of isomorphisms, so this also asserts the specified
   compact-support exchange is the ordered reindexing isomorphism. Naturality is
   built into the natural transformations and natural isomorphisms throughout.
6. For every fixed-scalar module sheaf F and site object V, the ordinary proper
   comparison is precisely `F.obj.map` of the opposite of the canonical
   `pullbackMapComparison` component. This is the explicit section identification
   in the node, including its direction and its projections. The already-defined
   `sfProperOpenPullbackRestriction` transports this same comparison to intrinsic
   modules; `sfProperOpenDerivedRestriction` derives it on K-injectives. Thus the
   underived formula is tied to the r in (1), not a separate arbitrary section map.

Why these are reindexing maps: the published
`ProEtale.openImmersionRestriction` precomposes with
`MorphismProperty.Over.map`. For an isomorphism this is the same site functor as
`proEtaleIsoPostcompose`, hence the sectionwise inverse-image model of
`isoSectionwiseInverseImage`. The proper ordinary comparison is the canonical
fibre-product section map. For the open comparison, take the sectionwise square
for direct image along b and restriction along j. Its left-adjoint comparison
is `finiteMateOpenReindexing`. On an object factoring through the open it keeps
the same section, and on a nonfactoring object it keeps zero. The sheafification
universal property identifies this construction with reindexing the
extension-by-zero presheaf. Exact termwise descent gives the displayed derived
comparison. No arbitrary natural isomorphism or existence choice is used.

Dependency declarations read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`.
  The existing finiteness instance is imported from
  `Sheaf.Paper.ConstructibleExceptionalInverseImage`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including the chosen isomorphism and
  its two projection equations.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, `.category`, and the underlying
  existing `Compactification` with its proper/open factors.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the published
  intrinsic finite operations; their specified module adjunction is
  `sfIntrinsicConstantModuleAdjunction` from
  `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData`.
  Its actual finite specialization is used, avoiding the legacy duplicate imports
  in `Sheaf.Paper.ExchangeProjection`; no replacement finite formula is defined.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `proEtaleIsoPostcompose`, and the canonical
  identification with inverse image reexported from
  `Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage`.
- The Mathlib dependency `def-weil-pbc-adjunction-mate` has status `mathlib`,
  and its `mathlib_match` is `CategoryTheory.mateEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Mates`. Its full signature, toFun,
  inverse, and counit formula were read. No missing Lean record is required.
- `Sheaf.SixFunctors.CartesianOpenAdjunctionRestriction`:
  `sfCartesianOpenPullPushAdjunction` and its actual unit/counit; the reexported
  `sfProperOpenDerivedRestriction`, `sfProperOpenPullbackRestriction`, and
  `sfProperOpenFixedRestrictionIso` are the existing section-normalized maps.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`:
  `sfIntrinsicOpenAdjunction`, `sfIntrinsicDerivedOpenMate`,
  `sfIntrinsicDerivedSquarePullback`, `sfIntrinsicDerivedOpen`.
  `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`:
  `exceptionalOpenAdjunction`.
- Proof dependencies are imported: open immersion, finite extension by zero,
  module-presheaf sheafification, integral/finite pullback composition, and
  `Sheaf.SixFunctors.OpenTensorNormalization`. The existing Cartesian open
  normalization theorem is also imported; no proof dependency closes a new cycle.

Edge cases checked before and after writing: empty schemes and empty opens are
allowed by `Compactification` and the two Cartesian squares; the section comparison
is still the canonical fibre-product map. Zero sheaves and zero unbounded complexes
are unrestricted. Identity isomorphisms and the whole open are allowed. Every
positive n, including n=1 and ramified coefficient extensions, is allowed. There
is no boundedness, constructibility, etale-origin, or finite-Tor hypothesis on M
or K. The horizontal maps may be semilinear. All universe parameters are explicit
and `autoImplicit false` is set; the small site's two universes are preserved.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder "Under scheme isomorphism derived proper base change
  mate equals section reindexing and open extension by zero comparison is normalized
  by the unit"`: eight hits, including scheme restriction and structure-sheaf
  component identities; none states the finite pro-etale proper/open normalization.
- `msearch.py ... leansearch "Base change along an isomorphism commutes with derived
  direct image and extension by zero with specified adjunction mates"`: eight hits,
  including `Adjunction.ofNatIsoRight`, `SheafOfModules.pullbackIso`, and generic
  Kan-extension base change; infrastructure only, no exact statement.
- `msearch.py ... loogle "CategoryTheory.mateEquiv,
  CategoryTheory.Adjunction.homEquiv"`: zero hits for this combined query. Direct
  source reading located `mateEquiv` and `Adjunction.leftAdjointUniq` and reused them.
- `msearch.py ... grep "mateEquiv|baseChangeMap" CategoryTheory/Adjunction`:
  five hits in `Mates.lean`, confirming the existing mate construction/counit equation.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node ID, reindexing,
  proper exchange, and the proposed declaration names: no existing exact theorem.
  Existing ordinary sectionwise restriction, derived open restriction, and open
  mate definitions were found and reused. `grep -rn` for this node ID in
  `lean/WeilConjectures` found no declaration. `dag/lean_names_upstream.json`
  contains none of the newly introduced names.
- Read the current `literature/blueprint/latest/` compatibility proof, not the
  historical path recorded in the node. Its constituent-compatibility assembly
  is unchanged in intent. The detailed six-step argument is retained in the
  theorem docstring from the reviewed DAG proof.

Validation: compilation is exclusively through the prescribed `scompile.py`,
checking the sandbox module and its library module separately against the live
published server build. Expected `sorry` warnings are the only permitted warnings.

## Second reading by N7

The dispatcher explicitly prohibits starting other agents and specifies that the
maintainer independently reviews the delivery. This section records my final
source-to-signature reread, not a claim of an independent worker review.
I checked the actual mate orientation, the inverse orientation of beta, the
open-unit transpose, and the order r then Rp'_*(beta). I added the explicit
underived section-map conjunct after the initial successful compile so that this
clause is visible in the Lean signature. I also verified that arbitrary chosen
Cartesian models of c' are covered and that no k-linearity slipped into the
horizontal maps. No statement discrepancy or disputed mathematical clause remains.
