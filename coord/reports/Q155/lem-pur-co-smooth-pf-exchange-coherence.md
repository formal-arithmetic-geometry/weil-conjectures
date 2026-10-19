## Worker report

The published `newtargets-dag` already contains the stage-2 declaration
`AlgebraicGeometry.ProEtale.compactification_projection_exchange_coherence` in
`Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence`. I read the
module and the node in full and retained the node statement verbatim. This packet
records the same declaration under Q155's delivery metadata; it introduces no second
notion or duplicate Lean declaration. The theorem has the one expected `sorry` proof.
The module compiled cleanly with `scompile.py` in both sandbox and library modes.

### Hypotheses and clauses

The coefficient hypothesis is rendered by `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
The four schemes and arrows are `{T' T U' U : Scheme.{u}}`,
`{w : T' ⟶ T}`, `{u' : T' ⟶ U'}`, `{u : T ⟶ U}`, and `{v : U' ⟶ U}`.
Separated finite type for `u` is exactly `[IsSeparated u] [LocallyOfFiniteType u]
[QuasiCompact u]`; no property is added for `v` or for the schemes over a field.
The Cartesian-square clause is `sq : IsPullback w u' u v`, and the compactification
clause is `c : Compactification u` with `[QuasiCompact c.i]`. The base-changed
compactification is the canonical `c.ofIsPullback sq` used in the displayed maps.

The objects `N` and `P` are arbitrary objects of the ordinary unbounded fixed-scalar
categories `DerivedCategory (Sheaf (Scheme.ProEt.topology T)
(ModuleCat.{u + 1} Λ))` and the corresponding category for `U`; no boundedness,
constructibility, Tor-amplitude, perfection, or field assumption is present.
`Rf_!(c)` is the chosen-compactification composite `Rp_*j_!`; its exchange map is
`rightDerivedLowerShriekOfCompactificationBaseChangeMap ... sq c`, and its projection
map is `projectionMapOfCompactification ... c`. The left side pulls back projection along `v`, then applies exchange, the
tensor comparison for `w`, and the
inverse of `leftDerivedUpperStarSquareIso ... sq.toCommSq`. The right side applies
the tensor comparison for `v`, tensors exchange with the identity, and applies the
projection map for `c.ofIsPullback sq`. Thus the equality is stated for every `N,P`,
which is the required naturality, and contains no invertibility assertion.

### Dependency declarations

I used the recorded declarations from `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
(`AlgebraicGeometry.ChosenCartesianSquare`),
`WeilConjectures.Compactification.Refinement`
(`AlgebraicGeometry.Compactification.Refinement`),
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
(`AlgebraicGeometry.ProEtale.FiniteCoefficientModules`),
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
(`AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback`),
`Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses`
(`SheafOfModules.ringedSiteDerivedTensorOfUniverses`),
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
(`AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`), and
`Sheaf.Paper.ExchangeProjection`
(`AlgebraicGeometry.ProEtale.finiteExchangeProjection`). The theorem's proof docstring
also records the stated proof dependencies `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-proetale-derived-pullback-composition`,
`lem-sf-open-tensor-normalization`,
`lem-weil-pbc-ringed-exchange-tensor-coherence`, and
`lem-weil-pbc-ringed-projection-mate-exact`.

### Searches and edge cases

`msearch.py leanfinder` for “compactification projection exchange coherence for derived
pro-etale sheaves” returned only generic pullback/gluing declarations. `msearch.py loogle`
for `compactification_projection_exchange_coherence, projectionMapOfCompactification`
returned no hit. `msearch.py grep` for `projection.*exchange|compactification.*coherence`
in `Mathlib/CategoryTheory` returned no hit. `rg` over the upstream source and side
`lean/Sheaf` found the published module and the underlying projection/base-change maps,
but no second theorem of this item. A DAG search found this item and its downstream
composition node only.

Checked edge cases are the zero coefficient ring, zero `N` or `P`, empty schemes,
identity `v`, identity open immersion, identity proper factor, and arbitrary (including
non-separated) `v`; none is excluded by the signature. No statement correction,
new definition node, dependency repair, or `STATEMENT-DISPUTED` issue is present.

## Second reading by Q155

The original delivery recorded an independent comparison of the node and theorem.
The following detailed audit was added by the independent maintainer second reader
on 2026-10-18 against immutable delivery 59efbdebf766b0d3c6d0c3ec63c00ccf632b5e72.
No Lean declaration or mathematical node statement was changed.

- Finite commutative coefficients: `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`.
  This includes the zero ring and imposes no characteristic, field, or invertibility
  condition. The flat-pullback instance's Noetherian requirement follows from finiteness;
  it is not an additional assumption of the theorem.
- Schemes and arrows: the four `Scheme.{u}` binders and arrows `w,u',u,v` have exactly
  the node's directions. `IsSeparated u`, `LocallyOfFiniteType u`, `QuasiCompact u`
  express separated finite type. There is no base field, separatedness of the schemes,
  or restriction on `v`.
- Square and compactification: `sq : IsPullback w u' u v` specifies the Cartesian
  diagram. Its universal property gives the canonical identification with the fibre
  product; no independent choice affects the inverse-image comparison. `c` supplies
  the open immersion, proper factor, and factorization equation. `[QuasiCompact c.i]`
  is precisely the stated open hypothesis (also follows from quasi-compactness of `u`).
  `c.ofIsPullback sq` is the specified base-changed compactification, not an unrelated
  compactification chosen by an existence instance.
- Objects: `N` and `P` range over all objects of the ordinary unbounded derived
  categories of fixed-scalar module sheaves on the actual small pro-etale sites of
  `T` and `U`. The recorded finite-coefficient realization extends scalar actions to
  locally constant sections and identifies this presentation with modules over the
  constant ring sheaf. These are not condensed coefficients or an etale-origin
  subcategory. Site object and morphism universes have not been equated.
- Operations: `finiteExchangeProjection` in `Sheaf.Paper.ExchangeProjection` is
  definitionally the tuple of `derivedBaseChangeMap`,
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, and
  `projectionMapOfCompactification`. The theorem uses those exact components.
  Reading the owning upstream definitions confirms that `Rf_!(c)` is open extension
  followed by proper derived pushforward; exchange is the proper mate followed by
  open base change; projection is the counit/tensor mate followed by the inverse
  open projection isomorphism and the pullback-composition comparison.
- Left composite: first `v*` of projection, then exchange at `N tensor u*P`, then
  pushforward of the tensor comparison for `w`, then pushforward of tensor with the
  inverse square comparison. The last arrow takes `w*u*P` to `u'*v*P`.
- Right composite: the tensor comparison for `v` is followed by exchange on the
  first tensor factor and identity on `v*P`, then projection for `c.ofIsPullback sq`.
  Both sides therefore start at `v*(F_c N tensor P)` and end at
  `F_c'(w*N tensor u'*v*P)`. This is the node's equality with its specified inserted
  comparisons. All factors are natural transformations, so equality at arbitrary
  `N,P` is the asserted naturality. No exchange or projection inverse is asserted.

Sources read: the final arbitrary-base-change sentence in main-20261015
`sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-composition.proof.md`;
Stacks `sites-cohomology.tex`, `remark-compatible-with-diagram` (0E48),
`equation-projection-formula-map` (0B56), `lemma-j-shriek-and-tensor` (0GL1);
and `sites-modules.tex`, `lemma-j-shriek-and-tensor` (0E8I).
The proper compatibility is for arbitrary unbounded inputs, with no perfection
hypothesis; perfection is required only for the separate projection isomorphism theorem.
The open identity is the ordinary derived extension-by-zero tensor identity.

The five proof steps are preserved in the declaration docstring. Step 1 fixes the
canonical comparisons and open normalization. Step 2 uses ringed exchange/tensor
coherence for the proper factor. Step 3 reduces the open identity by full
faithfulness to the termwise tensor calculation, with the same bidegrees and no
new sign. Step 4 uses exchange naturality at gamma and pastes those identities.
Step 5 uses projection naturality in its first argument. These prove coherence,
not invertibility. The strict-system assertion of the open-normalization dependency
is not needed. None of the item's direct statement or proof dependencies is on the
current route-pivot dropped list; no item repair note exists at the specified path.

Edge cases checked: zero ring, zero inputs, empty schemes, disconnected schemes,
identity horizontal map, identity open factor, identity proper factor, and arbitrary
non-separated horizontal map. The signature excludes none of them. There is no
positive-level parameter or implicit nonemptiness assumption to check.

Maintainer searches: LeanFinder for “proper pushforward projection formula square
commutes with inverse image tensor comparison” returned generic pushforward-composition
results, not this theorem. Loogle for the exact side declaration name reported an
unknown identifier (the service does not index it); this was not treated as evidence
of absence. Direct `rg` in Mathlib CategoryTheory/AlgebraicGeometry and upstream
pro-etale files found no matching pro-etale coherence theorem; the etale analogues
have different sites. Side-project search found the existing owning module under
this same node and no new duplicate notion in this delivery.

Reproduction: from the immutable snapshot root, ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q155 lem-pur-co-smooth-pf-exchange-coherence lean/Sheaf/AlgebraicGeometry/CompactificationProjectionExchangeCoherence.lean`.
Exit status 0; sandbox compilation 8.6 s, library compilation 9.8 s, no diagnostics.
The wrapper used its private side overlay/server confirmation pathway, with the
standard 60-second per-file limit. Exact current owning source modules unavailable
in the older local checkout were read using the authorized `scompile.py --source`
interface. No global build or live Lean write was performed.

The recorded signature equals the file's signature after whitespace normalization;
all lines are at most 100 characters, `autoImplicit` is false, and `u` is bound.
The module and theorem docstrings have the source place and blueprint identifier.
The only local proof is `sorry`; there are no local definitions or arbitrary-map
parameters. All eight statement dependency nodes and their exact relevant interfaces
were read. No new node, dependency repair, or statement correction is needed.

Findings repaired in this replacement report: H11, the original two-sentence second
reading did not document the hypothesis/clause comparison; also corrected the worker
paragraph's misplaced `v` tensor comparison and the module path for the recorded
universe-general tensor declaration. The mathematical delivery is accepted.
