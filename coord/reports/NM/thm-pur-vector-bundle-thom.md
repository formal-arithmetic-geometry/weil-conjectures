## Worker report

The module `Sheaf.Paper.VectorBundleThom` states the specified compact-support Thom
isomorphism and both compatibility laws, and constructs its inverse trace. All theorem
proofs are `sorry`; definitions contain actual canonical maps or selections uniquely
determined by their full canonical normalization. The item's statement is unchanged; its dependencies gain the two definition nodes below.

Clause and hypothesis correspondence:

- The fixed purity setting is `P : PurityFiniteSetting.{u}`. Its finite-field datum,
  distinct coefficient prime, finite coefficient extension, and positive quotient level
  are the recorded setting, with coefficient ring `P.Coefficient`. This is the finite
  coefficient theorem; integral and rational transports belong to the chapter's later
  transport section, as `def-pur-conventions` specifies.
- The separated finite-type base is `B`, its structure morphism `hB`, and the instances
  `[IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB]`. These are precisely
  separatedness and finite type over the fixed algebraically closed field.
- The constant rank is the arbitrary natural number `r`. The bundle and its zero section
  are the existing `V : PurityVectorBundle P B hB r` and `V.zeroSection`, including the
  chosen identification with the relative spectrum of its symmetric algebra. The
  definition is used unchanged, including its generator/dual convention.
- The morphism in the node is literally `vectorBundleThomTau V`, whose dependency
  constructs it from the localized tautological class, closed direct image, and the
  inverse normalized zero-section/projection compositor. It is not replaced by another
  map with the same endpoints.
- The conclusion “is an isomorphism” is `isIso_vectorBundleThomTau`. Its target is
  `Rpi_! (vectorBundleThomInput P V.E r)`, where the latter abbreviation is the recorded
  signed twist in degree zero shifted by `2 * (r : ℤ)`. This is an assertion about the
  actual map in the unbounded derived category, not only its cohomology groups.
- Base change is `vectorBundleThomTau_baseChange`, for arbitrary `g : B' ⟶ B` whose
  source remains in the fixed setting. The structure map there is `g ≫ hB`.
  `sq : IsPullback v V'.p V.p g` is the bundle Cartesian square. The predicate
  `VectorBundleThomBaseChange` says that this is the pullback *as a vector bundle*:
  there is an isomorphism from the tensor pullback of the generator module to the
  new generator module, and the actual map of total spaces sends every degree-one
  symmetric-algebra generator to the corresponding pulled-back section. This is the
  usual identification of the base-changed bundle, not an additional restriction on
  `g`. A bare Cartesian square would also admit translations, which do not describe
  that bundle identification. Identity changes and every nonflat change are allowed.
  The map `vectorBundleThomBaseChangeMap` is literally the proper/open compact-support
  exchange, twist-and-shift pullback, and normalized compactification comparison.
  Its source identification `vectorBundleThomUnitPullback` is the canonical pullback
  of the coefficient unit. The theorem equates the two maps of that square.
- Direct sums are `vectorBundleThomTau_directSum`. The arbitrary ranks `r,s`, bundles
  `V₁,V₂,V`, and generator-module isomorphism `e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔` specify
  the direct-sum identification. Finite products and direct sums agree for these
  module sheaves. The two total-space maps are the dependency's generator-normalized
  `vectorBundleThomProjection₁` and `vectorBundleThomProjection₂`.
  `vectorBundleThomSum_geometry` identifies the resulting Cartesian square.
  `vectorBundleThomSumProduct` is uniquely normalized by the concrete forward
  six-arrow relative compact product `finiteForwardProduct`, followed by the structure-map identity and the
  root-normalized signed twist product `vectorBundleThomSumCoefficient`.
  All these tensor domains and their morphism maps use `ProEtale.derivedTensor`
  literally, the same functor as the prescribed forward product.
  `VectorBundleThomTensorEquation` spells out the equation
  `(tau₁ tensor tau₂) ; T = multiplication ; tau_sum`, exactly the
  forward form of `kappa_B ; tau_sum = tau₁ tensor tau₂`, where `T=kappa_B^{-1}`.
  `vectorBundleThomUnitMultiply` supplies the canonical coefficient-unit identification.
  Its `VectorBundleThomUnitMultiplySpec` fixes the ordinary twist-zero multiplication
  and the native single-complex localization map; the existence-and-uniqueness theorem
  determines the map completely.
- The inverse is the definition `vectorBundleTrace V := inv (vectorBundleThomTau V)`.
  `vectorBundleTrace_inverse` gives both inverse identities. The base-change and
  direct-sum squares for this very inverse are also stated, in
  `vectorBundleTrace_baseChange` and `vectorBundleTrace_directSum`. The latter uses
  `VectorBundleTraceTensorEquation`, the reverse square for the same product.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its quotient
  coefficient ring, constant objects, and field/coefficient data. The finite sheaf and
  derived interfaces used by the Thom class are publicly reexported by that dependency.
- `Sheaf.Paper.PurityVectorBundleZeroSection`: `AlgebraicGeometry.PurityVectorBundle`
  and `PurityVectorBundle.zeroSection`.
- `Sheaf.Paper.VectorBundleThomClass`:
  `WeilConjectures.PurityFiniteSetting.vectorBundleThomClass`, `vectorBundleThomTau`,
  `vectorBundleGenerator`, `vectorBundleThomProjection₁`, `vectorBundleThomProjection₂`,
  and the existing finite-type, compactifiability and rank-zero normalization facts.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`:
  `WeilConjectures.sfQbarTwistingFunctor` reexports the recorded signed-twist construction.
  At this finite coefficient level the exact interfaces already used by the recorded
  Thom-class construction are `functorialCupTwist`, `functorialCupTwistProduct`, and
  `functorialCupTwistPullback` from `Sheaf.Paper.SupportedCupFunctoriality`; no second
  twist definition is introduced. The Qbar functor itself is outside the finite theorem.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport` is the recorded intrinsic
  realization of compact support. The Thom-class dependency explicitly uses its
  fixed-module realization `AlgebraicGeometry.ProEtale.rightDerivedLowerShriek`;
  this theorem keeps those endpoints and imports the recorded realization module.
- `Sheaf.Paper.FiniteForwardProductSymmetry`:
  `AlgebraicGeometry.ProEtale.finiteForwardProduct` and
  `finiteForwardCompactificationComparison`. These are the prescribed projection,
  proper/open exchange, and origin-compositor arrows, with their normalized
  compactification transport; neither is selected from a mere existence statement.
- `Sheaf.Paper.SupportedCup`: `ProEtale.cupSingleTensorMap`, the canonical localization
  comparison followed by the ordinary single-complex tensor comparison.
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`:
  `DerivedCategory.shiftTensorShiftIso`, the native K-flat tensor/shift comparison.
  `vectorBundleThomInputProductGeneric` constructs the shifted localization/root
  composite in a general abelian monoidal category. The two heterogeneous equalities
  in `VectorBundleThomInputProductSpec` fix its ordinary root multiplication
  and its entire derived composite in the published cup presentation.
  `existsUnique_vectorBundleThomInputProduct` proves this normalization uniquely
  characterizes the map; it supplies no free choice of an isomorphism. Both degrees
  are even, so the two Koszul orderings coincide. The bridge uses the same native
  sheaf/derived structures, without changing the site or tensor.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`:
  `ProEtale.leftDerivedUpperStarIsoMapDerivedCategory` and
  `singleFunctorCompLeftDerivedUpperStarIso`, including their full exact-pullback
  signatures. Its exact realization supplies the shift comparison.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange`:
  `ProEtale.rightDerivedLowerShriekBaseChangeMap`, the actual proper-mate/open-exchange
  map on the chosen compactification. It is followed by the recorded normalized
  compactification comparison, not an unspecified equivalence.

Every already-stated proof dependency is imported (or publicly reexported from a directly
imported statement dependency). `lem-weil-pbc-symmetric-algebra-free-module-polynomial`
has its Mathlib match, `SymmetricAlgebra.equivMvPolynomial` and
`equivMvPolynomial_ι_apply` in `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`; their full
basis signatures and generator formula were read. `sk-thm-sf-kunneth-relative` currently
has no Lean record or Mathlib match and hence has no proof module to import. The concrete
forward product needed to *state* this theorem is already published in the cited
finite-product modules, so no replacement of that independent theorem is necessary.

Edge cases checked against the source and formulas:

- Rank zero is retained throughout; no hypothesis `0 < r` occurs. The dependency's
  `vectorBundleThomTau_rankZero` fixes its identity normalization. No negative-rank
  projective bundle is used. The trace is then the normalized inverse identity.
- Either summand may have rank zero, including both; the degree shifts, zero twist
  product and coefficient-unit multiplication become the empty tensor-unit product.
- The empty base is allowed; no `Nonempty B` or nonempty chart family is assumed.
- Nonreduced bases and nonflat base changes remain allowed. Regularity is universal
  coordinate regularity of the tautological section, not regularity of an arbitrary
  pulled-back regular section.
- `P.level_pos` includes level one and every positive ramified coefficient level;
  there is no divisibility-by-ramification hypothesis.
- The same universe `u` as the setting is used for arbitrary schemes, with the actual
  small pro-etale site's object universe `u+1` and fixed module size `u+1` unchanged.
- In direct sums the coefficient shifts use `2r+2s=2(r+s)` and the normalized signed
  tensor map. In particular the even-degree classes introduce no permutation sign.

Searches made:

1. `msearch.py ... leanfinder` with query “The Thom class of an algebraic vector bundle
   induces an isomorphism to compactly supported derived pushforward and is compatible
   with base change and direct sums”: eight hits, beginning with
   `Scheme.Modules.pushforwardComp_inv_app_app` and ordinary sheaf pullback/unit facts;
   none states the compact-support Thom theorem.
2. `msearch.py ... loogle "vectorBundleThomTau, Thom, IsIso"`: zero hits, unknown
   identifier `vectorBundleThomTau` in the search service's Mathlib environment.
3. `msearch.py ... grep "[Tt]hom|thomClass" AlgebraicGeometry`: twelve substring hits
   (ordinary sheaf restriction names, author Thomas Browning); no match.
4. `rg` in the project's `lean/WeilConjectures`, `lean/Sheaf`, and upstream name index
   for `Thom`, `thom`, `vectorBundleThom` and the node id. Read the matching upstream
   `EtaleCohomology/Purity/Smooth/ThomClass.lean` and
   `WeilSheaf/FourierInversion/OtherSections.lean` signatures. The former concerns
   exceptional-inverse-image purity for the affine-space zero section; the latter
   concerns rational Weil complexes and a trivial line bundle. Neither concerns the
   specified finite-coefficient compact-support map for arbitrary vector bundles or
   both of its compatibility laws. The existing project's `VectorBundleThomClass`
   constructs precisely the needed map but explicitly defers its invertibility to
   this theorem, so that map is reused.

No statement correction, disputed statement, or dependency repair is needed.
The normalized comparison maps and sum product are the two new definitions below.
The remaining trace and coefficient-unit helpers belong to the theorem node.
Each module lists its declarations in its owning node record.
The maintainer supplies the independent review; this report is the author's clause check.


## New nodes

`def-pur-vector-bundle-thom-comparisons`, module `Sheaf.Paper.VectorBundleThomMaps`,
defines the normalized pullback and coefficient comparisons of the blueprint proof,
Steps 1, 2 and 5. It uses the recorded Thom class, root products, exact pullback and
proper/open compact-support exchange. Its geometric helper statements specify the
Cartesian square and compactifiability of the canonical linear projections. Its
normalization theorem for the coefficient product fixes the whole derived arrow.
The generic forward construction is a literal composite of the published product,
the structure-map comparison and direct image of the specified coefficient arrow.
This module introduces no second tensor, twist or compact-support functor.

`def-pur-vector-bundle-thom-sum-product`, module `Sheaf.Paper.VectorBundleThomProduct`,
defines the prescribed relative product of Steps 5--7 on the bundle Thom inputs.
`VectorBundleThomSumProductSpec.normalized` requires heterogeneous equality to the
entire native forward construction and requires its coefficient arrow to be the
preceding canonical coefficient map. The only other quantified value is an origin
proof. Thus the existence-and-uniqueness theorem determines the complete arrow;
its selection is neither a bare existence choice nor an arbitrary isomorphism.
The shared Hom presentation avoids repeated elaboration of the native localization.

Searches for both nodes: `blueprint_refs.py search Thom` returned five Thom-related
nodes (the existing Thom-class node, two older purity nodes, rank-one Thom and this
item); none defines these comparisons or this sum-product specialization. The
repository grep returned this item and unrelated occurrences, while the existing
`FiniteForwardProductSymmetry` supplies the generic forward map which is reused.
The real `leansearch` query “Canonical compact support Thom base change and vector
bundle direct sum comparison morphisms” returned eight ordinary module/base-change
or topological compact-support hits, beginning with `IsBaseChange.directSum`.
Loogle on “finiteForwardProduct, vectorBundleThomInputPullback,
vectorBundleThomSumProduct” returned no hits (unknown `finiteForwardProduct`).
Mathlib grep “Thom|forwardProduct|ForwardProduct” in AlgebraicGeometry returned
12 substring occurrences, not these maps. Exact returned hit records are retained
in each new node's `mathlib_searches`.


The two generic equation predicates are definitions in `VectorBundleThom.lean`.
They require an ordinary equality of the two composites in one shared category,
and heterogeneous equalities identifying **all five arrows** with the specified
Thom maps (or inverse traces), the prescribed sum product, and the normalized unit
multiplication. Their six corner objects are the actual coefficient units and compact
images printed in each theorem. These are exact presentation equalities, with no free
replacement map, extra hypothesis or weakened compatibility clause. This form prevents
the kernel from repeatedly expanding the complete native localization presentation
while checking two identical Hom types. No universe equality is imposed.

## Validation

The prescribed server compiler accepted each of the three delivered modules separately
in dependency order. The comparison module and product module compile against the live
published library; the theorem module compiles against those private delivery modules.
The final theorem source also passed the independent per-file sandbox and library
checks (7.3 and 8.6 seconds). No warnings other than the permitted postponed-proof
warning were emitted. All theorem bodies are `sorry`; no definition contains `sorry`.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
