## Worker report

The module `Sheaf.Paper.ZlWeilHeartLocalizationExact` states the node in two named
sorry theorems: `WeilConjectures.zlWeilLocalizationSchemes` gives the scheme
properties, and `WeilConjectures.zlWeilHeartLocalizationExact` gives the heart,
restriction, localization, and empty-scheme clauses. The three structures/helpers
only package the clauses and the literal forgetful/inclusion functors. Their data
are fully written; no operation is chosen from this theorem or a mere existence.
Both postponed theorems belong to this same DAG node and have its source and
step-by-step proof in their docstrings.

Hypotheses and clauses, read against the node:

- The fixed `D : FiniteFieldDatum.{u}` contains prime p, positive a, q=p^a,
  a field k0 of cardinality q, and its fixed algebraic closure k. `l`,
  `[Fact l.Prime]`, `hl : l ≠ D.p`, and `Ω` with its field, Padic algebra,
  and algebraic-closure instances are precisely the coefficient hypotheses.
  `_iota : Ω ≃+* ℂ` retains the specified coefficient isomorphism. The maps
  and exactness do not otherwise depend on it. The coefficient universe v
  is independent of scheme universe u, as in the recorded common-stage category.
- A separated finite-type model is `X₀ : Over (Spec (.of D.k₀))` with
  `LocallyOfFiniteType X₀.hom`, `QuasiCompact X₀.hom`, `IsSeparated X₀.hom`.
  No nonempty, smooth, reduced, or connected hypothesis is imposed.
- Every open/closed subscheme is quantified by `W₀`, `f₀ : W₀ ⟶ X₀`, and
  `IsOpenImmersion f₀.left ∨ IsClosedImmersion f₀.left` in
  `zlWeilLocalizationSchemes`. Its conclusion gives both components of finite
  type, separatedness, and Noetherianity of W0, and the corresponding properties
  of its geometric base change. The model and its geometric fiber have the same
  properties in the initial conjunction. For W0 the actual scheme pullback and
  second projection are written explicitly: `D.geometricFiber W₀` has finite-type
  class parameters, which cannot be demanded before concluding finite type.
  This is the identical base-change scheme, with no additional structure chosen.
- Constructible Weil sheaves are exactly `sfCommonStageWeilSheaf`, the recorded
  full heart-carrier subcategory of fixed pairs, and the underlying constructible
  heart is exactly `sfCommonStageHeart`. The already published
  `zlWeilHeartAbelian` supplies abelianity; it is not assumed as an additional
  theorem hypothesis or restated with a different category.
- `zlLocalizationForget` sends H to `⟨H.obj.carrier, H.property⟩` and an arrow
  to the identical underlying arrow. `ZlLocalizationHeart.underlying_abelian`
  supplies the underlying heart's abelian structure as conclusion data, and
  `forget_additive` specifies compatibility with the additive Hom groups.
- Creation of kernels and cokernels is `CreatesLimit (parallelPair f 0)` and
  `CreatesColimit (parallelPair f 0)` for every actual Weil arrow. These are
  Mathlib's defining kernel/cokernel diagrams. Creation lifts their universal
  properties and thus their induced invertible Weil structures.
- `images` gives the actual image comparison together with its inclusion
  equation. In an abelian category an image is the kernel of the cokernel;
  the preceding creation clauses give creation of this image with its induced
  Weil map, and the equation specifies its canonical comparison.
- `inverse_images` is creation of `cospan f m` for every mono m, namely the
  pullback representing inverse image of a Weil subobject. Its source is the
  same constructible Weil category, so this includes constructibility.
- `short_exact` is the equivalence between `ShortComplex.ShortExact` of the
  Weil arrows and that of their actual forgotten arrows. The existential w'
  supplies only the proof that their composite is zero; proof irrelevance makes
  this exactly detection of short exactness, rather than a choice of maps.
- Locally closed immersion restriction is the second conjunction of
  `zlWeilHeartLocalizationExact`: `IsImmersion h₀.left` and both
  `PreservesFiniteLimits (zlWeilPull ... h₀)` and `PreservesFiniteColimits`.
  This is Mathlib's locally closed immersion, with the prescribed common-stage
  pullback and induced normalized Frobenius comparison.
- In the third conjunction j0 and i0 are actual model morphisms with the open
  and closed immersion instances and complementary underlying ranges.
  `ZlWeilHeartLocalization.open_fac` and `closed_fac` identify their heart
  restrictions, through the literal full inclusion, with respectively
  `IsoAlgebra.mapOfNatIso (zlOpenFrobenius ... j₀)` and
  `sfModelWeilDerivedPush ... i₀`. Thus they are the already existing operations
  on both objects and morphisms, not arbitrary exact functors or substitute maps.
  The finite-type parameters on U0 and Z0 permit their recorded categories to
  elaborate; the first theorem establishes them for every such subscheme.
- `open_additive`, `open_limits`, `open_colimits`, and the corresponding three
  `closed_*` fields express exactly additive exact j! and i* on the hearts.
- `open_adjunction` and `closed_adjunction` are their heart adjunctions to the
  existing `zlWeilPull`. `counit_normalization` identifies the open counit's
  underlying arrow with the actual `zlCommonStageOpenAdjunction.counit`.
  `unit_normalization` identifies the closed unit already as an arrow of fixed
  pairs with the actual `sfModelWeilDerivedAdjunction.unit`. HEq only handles
  source/target equalities from the full-subcategory factorization equations;
  it is not a hypothesis permitting a different arrow.
- `localization` requires the composite of these very two maps to vanish and
  their short complex to be `ShortExact`, i.e. the displayed sequence with
  mono counit, exact middle, and epi unit. All its arrows are Weil morphisms.
- The final conjunction says `IsEmpty X₀.left → ∀ H, IsZero H`. No nonempty
  assumption is used anywhere: empty U0, empty Z0, empty X0, and the zero sheaf
  are all included in the same quantifiers and same canonical sequence.

Dependency declarations read and used:

- `Sheaf.Paper.AdicPunctualWeights`: `SfIsPunctuallyPureOfWeight` (coefficient
  convention); it uses the same arbitrary-universe algebraic closure and heart.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilFrobeniusPullback`,
  `sfCommonStageWeilForget`, `sfCommonStageWeilSheaf`, fixed pairs, full heart
  inclusion, and the prime-invertibility construction.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`,
  `sfCommonStageHeart`, `sfCommonStageHeart_properties`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`, with
  its prescribed finite-stage object and morphism formulas.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`,
  the recorded projection-normalized integral compact-support realization.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, the actual
  finite-reduction Roos tower presentation. The already published
  `Sheaf.Paper.SfCommonStageDirectImage.sfModelWeilDerivedPush` extends that
  direct image and supplies its induced Weil structure and normalized adjunction.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlWeilHeartAbelian`, `zlWeilPull`,
  `zlFrobeniusSquare`; the actual constructible hearts and pullbacks, not the
  ind-category, are used here.
- `Sheaf.Paper.CommonStageWeilShriek`: `zlCommonStageOpenShriek`,
  `zlCommonStageOpenAdjunction`, `zlOpenFrobenius`, and
  `zlCommonStageShriek_recorded`. Their adjunction characterization and its
  recorded compact-support comparison identify the intended open extension.
- Mathlib `AlgebraicGeometry.IsOpenImmersion`, `IsClosedImmersion`,
  `IsImmersion`, `IsNoetherian`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`; the scheme-properties node is a convention with no declaration.
- Mathlib `CategoryTheory.Abelian`, `Functor.Additive`,
  `Limits.PreservesFiniteLimits`, `PreservesFiniteColimits`,
  `CreatesLimit`, `CreatesColimit`, `ShortComplex.ShortExact`, `image`, and
  the full-subcategory `ObjectProperty.homMk`/inclusion API.

Two already landed definition nodes were added to stmt_deps under brief §5's
permission for landed notions: `def-zl-common-stage-weil-shriek` and
`def-zl-weil-ind-sheaf-category`. They carry precisely the canonical interfaces
used above. No new notion or dependency module is introduced, and no statement
correction is needed. The stated proof dependencies are imported. The generic
`lem-zl-texact-fixed-pair-heart-cohomology` has no Lean attachment on this read
base; no import is invented for it. Its fixed-pair kernel argument is documented
in the theorem's proof, while the already published abelian instance is reused.

Edge cases checked before and after drafting: zero Weil sheaf; no sections on the
empty scheme; empty open (left term zero); empty closed (right term zero); both
empty; locally closed immersion with nonreduced image; no restriction to smooth,
connected, geometrically connected, or nonempty models; arbitrary coefficient
universe independent of scheme universe. For a nonempty model the empty-scheme
implication adds no claim; for an empty model it states all objects are zero.
The finite-field and distinct-prime hypotheses ensure coefficient invertibility
without an extra input. No extra Frobenius linearity over k is assumed.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: `Constructible Weil heart abelian forgetful creates kernels cokernels
  canonical open closed short exact sequence`. Eight unrelated condensed-category
  and concrete-exactness hits; no match for this statement.
- Loogle: `CategoryTheory.Limits.CreatesLimitsOfShape,
  CategoryTheory.ShortComplex.ShortExact`. Zero hits, service reports unknown
  first identifier; direct Mathlib source search supplies the existing API.
- grep (Mathlib CategoryTheory): `WeilHeartLocalization|weilHeartLocalization|
  Creates.*IsoAlgebra`. Zero hits.
- LeanSearch: `Constructible Weil sheaves open closed localization short exact
  sequence`. Eight hits concerning module localization, Mayer--Vietoris squares,
  and topology; none this constructible Weil-heart assertion.
- rg of both `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
  `WeilHeartLocalization|weilHeartLocalization|Creates.*(IsoAlgebra|Weil)|
  IsoAlgebra.*(Abelian|Preadditive)` and the new declaration names. Existing
  general IsoAlgebra limits and abelian constructions, and the existing
  `zlWeilHeartAbelian`, were found and reused. No existing complete statement.
- Further source searches located and read the canonical common-stage pullback,
  direct-image and open-shriek adjunctions and their exact normalization formulas.

No STATEMENT-DISPUTED issue or node mathematical fault was found.

## Second reading by Q58

A separate clause-by-clause pass in this worker session compared the unchanged
node, current blueprint final paragraph, and generated module. No other agent
was started, as the dispatch brief forbids it; the maintainer's independent
review remains the independent reading. This pass found and repaired two
elaboration defects: `open` was a Lean keyword rather than an admissible field
name, and `geometricFiber W₀` demanded finite-type instances before the theorem
could conclude them. The field is now `openExtension`, and the scheme theorem
uses the literal base-change pullback and projection for W0. It also retained
the otherwise unused iota isomorphism explicitly, matching the fixed datum.

The pass checked each of the correspondences listed above against the actual
field signatures. In particular it checked the directions of the adjunctions,
that localization uses the open counit and closed unit themselves, that the
normalization is not merely existence of arbitrary arrows, that the final
empty-scheme clause is present, and that image creation and Weil inverse images
are included. The two existential heart restrictions are determined by their
full-inclusion factorization equations and do not define new data by choice.
All theorem proofs remain exactly `by sorry`; all definition data are explicit.

Validation: the complete module compiled through the prescribed scompile.py wrapper
as both an isolated sandbox module and its library module, with no errors or
warnings. All remaining proofs are the two expected named sorry theorems.

## Maintainer review fix (2026-10-25)

The delivered statement used `sfModelWeilDerivedPush` and `sfModelWeilDerivedAdjunction`.
Their recorded owner is def-weil-common-stage-derived-direct-image, which is not in the
item's stmt_deps, and a review fix cannot add stmt_deps. The fix inlines them.
`sfModelWeilDerivedPush` is by definition the right adjoint of
`IsoAlgebra.mapOfNatIso (zlFrobeniusSquare i₀)`, so `ZlWeilHeartLocalization` now carries
`closedDerived` with `closedDerivedAdjunction :
IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω i₀) ⊣ closedDerived`. `closed_fac` and
`unit_normalization` refer to that pair. Right adjoints are unique up to the unique
isomorphism compatible with the units, and the heart property is closed under
isomorphism. So the existential statement is equivalent to the delivered one.
`public import Sheaf.Paper.SfCommonStageDirectImage` is replaced by the module of the
cited def-zl-weil-ind-sheaf-category, `Sheaf.Paper.WeilIndSheafCategory`. The theorem
signatures and the lean record are unchanged. Clean compile: nt_compile --json, 11.3 s.
