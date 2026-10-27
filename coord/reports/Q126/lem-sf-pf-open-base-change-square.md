## Worker report

Q126 states `lem-sf-pf-open-base-change-square` in
`Sheaf.SixFunctors.OpenBaseChangeSquare`, namespace
`WeilConjectures.OpenProjectionBaseChange`. The main theorem is
`openBaseChangeSquare`. Its only proof is `sorry`. All helper definitions have real
terms. The node's natural-language statement, dependencies, proof and proof dependencies
are unchanged; only its `lean` record is set. No new nodes or dependency repairs.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors/`
`sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`, base-change paragraph.
The displayed equality is the open-factor calculation there, with the node's domain
assertions and explicit pullback monoidality. The six proof steps are in the theorem's
docstring. This is stage 2, not a claim to have proved them.

### Hypotheses and objects

- `D : FiniteFieldDatum.{u}` supplies the prime p, q, finite field and fixed algebraic
  closure k. `c : D.CoefficientDatum` supplies the prime ell and `c.different`.
  `E : Type u`, `Field E`, `Algebra ℚ_[c.l] E`, and `FiniteDimensional ℚ_[c.l] E`
  give the finite coefficient extension. The recorded coefficient rings use its
  valuation ring and fixed uniformizer; no second ring or coefficient construction.
- `n : ℕ` denotes exponent `n+1`. Thus `Nat.succ_pos n` covers every positive exponent,
  including 1, and excludes exponent zero exactly as the node does.
  `_operations : SixFunctorDatum D c E (n+1) (Nat.succ_pos n)` is the operation datum.
- `Q : SixFunctorCompactifiedSquare D` supplies X,Y,X',Y',Z,Z', all finite type over k,
  where Z and Z' denote bar X and bar X'. Its i,i' are j,j'; its g' is a; its p,p',h,g
  are the node's maps. The fields `open_i`, `proper_p`, `properSquare` and `openSquare`
  record precisely the geometry. The additional composite f and pasted square in this
  existing bundle are determined by these data. There is no separatedness requirement
  on g or on schemes over k. Base-change schemes may be any specified Cartesian models.
- `units` derives residue-field invertibility from `c.different`, by the existing
  `PurCompactSupport.coefficientPrimeUnit` and the scheme's residue algebra map.
  This adds no hypothesis. The explicit instances are passed to canonical tensor maps.
- Finite K is an object of `proEtaleDerivedCategory` with
  `intrinsicFiniteTorsionConstructible`; finite L has `finiteTorConstructible`.
  Integral K is an ambient completed-coefficient derived object with
  `sfIntegralConstructible`; integral L has `finiteTorConstructibleIntegral`.
  There is deliberately no finite-Tor hypothesis on K in either clause.

### Each conclusion and map

1. The first conjunct is `Monoidality` for the four actual
   `finiteIntrinsicDerivedTensor` bifunctors and the four `finiteDerivedPullback`
   functors p,p',g,h. Its B,C range over the entire unbounded category.
   `finiteTheta` is the inverse of the recorded proper-square pullback comparison;
   `finiteMu` specializes `canonicalFinitePullbackTensor`. Expanding `Monoidality`
   gives theta at B tensor C, H(mu_F), mu_H on the left and F'(mu_G), mu_F',
   theta_B tensor theta_C on the right, in Lean's left-to-right composition.
2. The second conjunct is exactly the same equation on the full integral constructible
   categories. `integralPull` and `integralTensor` use the recorded restricted functors,
   so all tensor and pullback objects in this equation remain on those domains.
   `integralMu` is `canonicalIntegralPullbackTensor`. `integralTheta` composes the inverse
   comparison for p' followed by g with the comparison for h followed by p, using the
   actual equality of composites. This is the node's theta orientation.
3. The third conjunct gives the finite normalized open maps, all finite domains, and
   `FiniteEquation` for every qualifying K,L. `FiniteMaps.gamma` and `.gamma'` are
   natural isomorphisms; their inverse transposes are fixed by the actual open units
   and canonical inverse tensor comparison. These adjunction bijections determine the
   maps uniquely. `beta.inv` is fixed to `sfIntrinsicDerivedOpenMate`. This presents the
   supplied canonical maps rather than replacing them by arbitrary arrows.
4. The fourth conjunct gives the integral normalized data, all integral domains, and
   `IntegralEquation`. `IntegralMaps` is the existing `OpenFactorCoherence.Assertion`
   plus the normalized tensor models on X' and Z'. Its `Open`, `Pull` and `Tensor`
   fields retain strict quotient towers, augmentation coordinates, units and comparison
   normalization. `integralBeta`, `integralGamma`, and `integralGamma'` are direct calls
   to the existing completed maps. `integralSigma` is the inverse of `completedSquare`;
   its direction is A J to J' H. Ordinary restriction `integralJ` is the open-factor
   theorem's identification of completed restriction on complete objects.
5. `OpenIdentityAt` spells out both arrows without omitting any comparison. Its left
   route is H(gamma), beta at V, then j' shriek applied to mu_A followed by identity
   tensor sigma. Thus its last two factors are precisely z. Its right route is mu_H,
   beta_K tensor identity, then gamma'. Both instantiations have source H Q and target
   j' shriek W. The integral comparison arrows are the underlying `.hom.hom` of the
   specified full-subcategory isomorphisms, not comparisons chosen anew. The integral
   equality is an equality of ambient completed arrows, without evaluation or rationalization.
6. `IntegralDomains` concludes `sfIntegralConstructible` for M,P,Q,JP,V,AK,HP,HM,HQ,
   AJP,AV,J'HP,W,j!V,j'!AV,j'!AK,j'!W,H(j!V), and the intermediate tensor
   j'!AK tensor HP. It also concludes this for SM,SQ,S'HM,S'HQ, using the actual
   `sfCompletedDerivedDirectImage` along p and p'. This predicate includes derived
   completeness and one bounded constructible interval for all reductions. These are
   conclusions, never hypotheses. `FiniteDomains` gives the corresponding finite
   open-equation constructibility, including every displayed tensor involving L.
7. Naturality in K,L is retained: finite maps are natural transformations; integral maps
   are composites of the published natural comparisons. Pullback, tensor and extension
   are the actual functors. The equations hold for every qualifying pair, equivalently
   componentwise equality of those natural composites on the full permitted domains.

### Dependency declarations used

The seven recorded statement dependencies were read with their signatures/docstrings:

- `def-sf-datum`: `Sheaf.Paper.SixFunctorDatum`, `WeilConjectures.SixFunctorDatum`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `lem-pur-derived-pullback-tensor-iso`: `Sheaf.Paper.DerivedPullbackTensorIso`, `WeilConjectures.derivedPullbackTensorIso`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage`, `WeilConjectures.SfIntegralDirectImage`.

More specifically, `DerivedPullbackTensorHom` supplies `finiteDerivedPullback`,
`finiteIntrinsicDerivedTensor`, `constructibleIntegralPullback` and
`constructibleIntegralTensor`; `DerivedPullbackTensorIso` supplies
`canonicalFinitePullbackTensor`, `canonicalIntegralPullbackTensor` and
`pullbackTensorIntegralComposition`. `SfIntegralConstructible` supplies the full
subcategory and predicate. `FiniteTorAmplitudeSites` imports the recorded
`finiteTorConstructible` and `finiteTorConstructibleIntegral`.
`ExchangeProjectionSuppliedDomains.ExchangeProjectionStage` records the supplied
operations and their domain convention; its concrete normalized open maps are expressed
through the existing exact open adjunction/mate at finite level, and through
`OpenFactorCoherence.Assertion`, `gamma`, `beta` and `completedSquare` integrally.
`SfDerivedDirectImage.sfCompletedDerivedDirectImage` is the ordinary completed-ring
realization of S,S', identified with the recorded strict-limit images by the imported
completed pushforward comparison. All recorded proof-dependency modules with Lean records
are imported for the later proof; the Mathlib leaves are already in their import closure.

### Searches and edge cases

Genuine searches run with `msearch.py` for Q126/item:

- LeanFinder: "Extension by zero projection tensor comparison commutes with open base
  change in derived module categories". Eight hits, principally internally projective
  condensed tensor criteria and ModuleCat extension-of-scalars formulas; no exact statement.
- Loogle: "CategoryTheory.NatTrans.IsMonoidal, CategoryTheory.Adjunction". The monoidal
  unit and counit instances were returned, not this geometric completed/finite statement.
- Mathlib grep: "(extensionByZero|shriek).*(tensor|baseChange)". Zero hits.
- LeanSearch: "Canonical tensor projection for extension by zero and inverse image
  compatibility in a Cartesian open immersion square". Eight hits, including open
  immersion lift and base-change instances and Cartesian tensor projections; no match.
- `rg` in `lean/Sheaf` and `lean/WeilConjectures` for the item id, open/base-change/tensor
  and proposed declaration names. The upstream item-id search and proposed namespace
  search gave no declaration. Relevant nearby results were OpenFactorCoherence,
  OpenTensorNormalization, ProperOpenProjectionMate, and
  CompactificationProjectionExchangeCoherence. The latter is a fixed-coefficient
  compactification projection/exchange theorem; it does not state the intrinsic plus
  completed equations and constructible-domain assertions here. The existing normalized
  open constructions were reused. No exact duplicate found.

Checked empty X, identity j, identity g, zero K or L, positive exponent 1, and K with
infinite Tor amplitude. The formulas keep all identity/composition comparisons, accept
empty schemes, and place Tor only on L. Universe u is the recorded common scheme/field
universe; the intrinsic and completed sheaf universes are inherited without forcing
object and morphism site universes equal. No extra universe equality or smallness premise.
No statement dispute or source correction was needed.

Validation: scompile.py compiled the complete 626-line module, both sandbox and library
names, cleanly. One named theorem uses sorry as required; no other proof is postponed.

## Second reading by Q126

Separate author rereading of the node and complete file (no additional agent was started,
as the dispatch forbids that). The independent maintainer review remains the delivery
review. I matched finite/integral coefficients and all geometry to the existing bundles,
checked the two theta orientations, and expanded OpenIdentityAt term by term. In particular
sigma has direction A J to J' H, beta at V occurs before the j'! map, and gamma' occurs
last on the right. I checked that K has only constructibility, L alone has finite Tor,
and B,C are unrestricted at finite coefficients and full constructible objects integrally.
The first compile exposed argument ordering for the finite open functor and explicit
open instances for projections of integral data; both were repaired. The domain audit
added H(j!V) and the intermediate beta tensor, to cover every displayed object. The four
proper images are explicit fields of IntegralDomains. The node's statement was not changed.
