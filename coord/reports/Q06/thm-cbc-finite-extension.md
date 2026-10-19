## Worker report

The module `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange` states the specified
completed compact-support exchange after raw rationalization. Its primary declaration
is `AlgebraicGeometry.Scheme.finiteExtension_compactSupportBaseChange`; the identity,
horizontal-pasting and vertical-pasting declarations in the same module supply the last
clause. All theorem proofs remain `sorry`. Definitions have explicit data: full-subcategory
lifts, scalar transport, or images of actual integral arrows. No statement correction is made.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type (u + 1))
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The valuation ring,
  uniformizer and principal ideal are those in `pbcPadicCoefficientDatum l E`, using
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`.
- The four schemes and four arrows are explicit binders. `c`, `c'`, `gbar`,
  `properSquare : ChosenCartesianSquare ...`, and `openSquare : OpenImmersionSquare ...`
  give a compactification and its base-changed compactification; the outer square is
  therefore Cartesian. They allow any isomorphic presentation, rather than requiring
  a literal chosen pullback term. `Compactification.baseChange` is the recorded
  dependency construction, and the two Cartesian squares express its universal property.
- Separatedness is `[IsSeparated f]`; finite type is `[LocallyOfFiniteType f]
  [QuasiCompact f]`. No condition on `g` or `g'` is added. The four `[IsNoetherian ...]`
  binders give noetherianity, the four `_dim...` bounds give finite dimension, and the
  four `_hl...` stalkwise unit conditions express invertibility of `l`.
- The integral category is exactly `PbcBoundedConstructibleComplete T
  (pbcPadicCoefficientDatum l E)`. Its existing completion, uniform reduction bounds,
  and compatible etale-origin witnesses are retained. The existential `hSource` and
  `hTarget` conclusions assert that the two completed composites land in this full
  subcategory; they are conclusions, not additional hypotheses.
- `cbcCompactSupportSource` is `j_! ⋙ Rp_* ⋙ completedPull g` and
  `cbcCompactSupportTarget` is `completedPull g' ⋙ j'_! ⋙ Rp'_*`. Their lifts use
  `ObjectProperty.liftFullSubcategory`. The two `...Transport` abbreviations apply
  `ScalarLocalization.transport` to those lifts. This uses the actual constant-section
  scalar action, with additivity and linearity recorded by the named helper theorems.
- The raw rational category is the existing `PbcRationalCategory`: same integral
  objects, scalar-localized Hom modules, no Karoubi envelope. `⟨K⟩` ranges over all its
  objects. Localization away from the recorded uniformizer is canonically `E` by
  the coefficient-extension interface; the higher-universe actual valuation ring is
  used, as in the recorded integral specialization, rather than a second category.
- `finiteExtensionCompactSupportExchangeComponent` is the image under
  `pbcRationalization` of `completedCompactSupportExchange`, made a full-subcategory
  morphism by `ObjectProperty.homMk`. The main theorem's component equation fixes
  `η` to this specified map, for every generating tuple. `finiteExtension_cbcComplete`
  supplies the intrinsic completeness predicate from category membership, so the
  component equality has no additional completeness assumption on the theorem input.
- The conclusion `∃ η : ... ≅ ...` and the explicit component `IsIso` assertion give
  invertibility for every rational object. Since `η.hom` is a natural transformation
  on the raw rational categories, its naturality quantifies over all rational maps.
  In particular, for a rational isomorphism `h : ⟨M⟩ ≅ ⟨N⟩`, its naturality equation
  identifies the two components under precisely `F.mapIso h` and `G.mapIso h`.
  This is lattice independence and requires no integral lift of `h`.
- `finiteExtension_compactSupportBaseChange_identity` equates the localized identity
  paths using `completedPullId`. `..._horizontal` equates the direct exchange with
  successive exchanges and the canonical `completedPullComp` maps. `..._vertical`
  equates the two paths using `cbcTowerCompositionMap` on compatible compactification
  towers. These are the specified proper/open composition comparisons; no arbitrary
  endpoint isomorphism replaces them. The domain hypotheses are collected in the
  transparent `CbcFiniteExtensionDomain`. The supplied compactification towers are
  compatible presentations of pasted squares, with the existing integral refinement
  coherence providing their common-refinement interpretation.

Dependency declarations read and used (all are existing; none is redefined):

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, `completedReductionTower`.
- `WeilConjectures.Compactification.BaseChange`: `Compactification.baseChange` and
  `Compactification.ofIsPullback`.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcPadicCoefficientDatum` and its
  specialization of `PbcBoundedConstructibleComplete` from
  `Sheaf.Paper.BoundedConstructibleComplete`.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization` and
  the constant-section scalar action. Its smaller-universe convenience wrapper
  `PbcRationalDerivedCategory` is not a different rationalization.
- `Sheaf.Paper.PbcActualStrictPullback`: `pbcActualStrictCompletedPull` and
  `pbcActualCompletedPullback_tower`; `d.completedPull` in the specified exchange is
  the published, unit-normalized completed operation used throughout its dependency chain.
- `Sheaf.Paper.ProjectionCompactification`: `proEtaleRingCompactSupportImage`, the
  existing `Rp_* j_!` construction on completed-ring modules.
- `Sheaf.Paper.PbcRationalTransport`: `ScalarLocalization.transport` and its
  component formula and linearity interface.
- `Sheaf.Paper.CompletedCompactSupportExchange`: `completedCompactSupportExchange`.
- `Sheaf.Paper.CompleteCompactSupportProetale`: `cbcExchange`, `cbcSupport`,
  `cbcTowerCompositionMap`, the canonical completed identity/composition maps, and
  the integral coherence theorem signatures. The item cites this landed node and
  `lemma-weil-pbc-completed-exchange-coherence` as additional statement dependencies.

Edge cases checked in the statement: the zero complex and empty schemes are allowed;
there is no nonemptiness assumption, no dimension lower bound, no exclusion of `l = 2`,
and no restriction on the horizontal base change. Identity squares are explicit, and
pasting covers successive horizontal and vertical squares with the stated domains.
Every finite generating tuple is allowed, including an empty tuple if it generates the
ideal. No arbitrary replacement of the canonical exchange or its comparisons is used.

Searches: `msearch.py leanfinder` queried compact-support base change over a finite
p-adic extension on raw rationalized constructible complexes (2026-10-16 UTC); its eight
hits concerned p-adic fields and algebraic scalar base change, with no matching theorem.
`msearch.py loogle '\"baseChange\", CategoryTheory.IsIso'` gave six Kan-extension
base-change declarations, none in these coefficient categories. `msearch.py grep
'compact.support|Rationalization' CategoryTheory` gave zero hits. Direct `rg` in
`WeilConjectures` for the item id and compact-support theorem names found no existing
finite-extension theorem. The same search in `lean/Sheaf` found the integral support
restriction and separate unbounded etale comparisons, not the rational completed theorem.
The sandbox's `searches.jsonl` retains the wrapper search results, including earlier runs.
The current blueprint statement at main-20261015/order 1991 and the compact-support unit
were opened. No false statement of the item was identified.

## Repair of the prior attempt

The earlier speculative `def-pur-acyclic-tensor-kflat` and the modified projection-mate
module have been removed from the delivery set and archived under `scratchpad`.
Their conjunction `K.IsKFlat ∧ K.Acyclic` cannot replace the flat K-flat representative
predicate: it would exclude the degree-zero tensor unit over a nonzero coefficient ring
and cannot represent arbitrary objects. The published `RingedTensorModel` and
`RingedTensorCorner.mateFlat` use `P.IsKFlat ∧ ∀ n, (P.X n).IsFlat` instead.
`scompile.py --source Sheaf.Paper.ProjectionMateExact` confirms that correct source.
No unnecessary definition node or dependency-record change remains in the delivery.
The item's signature is synchronized verbatim and all lines are at most 100 characters.

## Verification

On 2026-10-17 UTC the prescribed `scompile.py Q06 thm-cbc-finite-extension
lean/Sheaf/Paper/FiniteExtensionCompactSupportBaseChange.lean` completed cleanly.
The wrapper compiled the module in both sandbox and library contexts, in 6.0 and
7.0 seconds respectively, after checking the current side dependencies. No Lean
errors or unexpected warnings were reported. The complete output is retained in
`scratchpad/current-compile.log`. Earlier attempts had encountered stale overlay
sources and missing artifacts; this successful run supersedes those failures.

The primary signature was checked verbatim against the JSON record; every variable
and universe is explicitly bound, and every Lean line is at most 100 characters.
The duplicate searches were repeated through LeanFinder, Loogle and Mathlib grep.
LeanFinder returned eight unrelated p-adic, condensed and base-change declarations;
Loogle returned six Kan-extension base-change results; Mathlib CategoryTheory grep
returned no compact-support or rationalization match. Direct source and side-library
searches found no statement of this finite-extension rational exchange.

The required `deliver2.py Q06 thm-cbc-finite-extension --no-push` printed
`OK (dry run)`: compilation and preflight passed except for the expected independent
second-reading section. Its output is in `scratchpad/current-dry-run.log`. Nothing
was pushed. The final rerun after refreshing this report and the UTC date is retained
in `scratchpad/final-ready-dry-run.log`.

LeanSearch was also renewed: its eight results concern algebraic module localization
and base change, with no theorem on these completed compact-support categories
(`scratchpad/current-leansearch.log`).

## Second reading by Q06

I independently read the base node and the sandbox Lean module, then the recorded
statement dependencies and their declaration signatures. The source of this item is
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/` followed by
`thm-cbc-finite-extension.md`, order 1644, including its proof paragraph. I also read
the identical statement at main-20261015 order 1991. The node makes the coefficient
and scheme domains explicit; these are the domains of its integral-category dependency.
This item has no Stacks tag of its own. I checked the cited background definition in
`proetale.tex`, `section-suitable-derived`, `definition-Dbc` (09C0/09C1): its constant
coefficient category is not silently substituted for the node's completed-ring category.
There is no `statement_change` in this delivery and no unit statement is changed.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Prime and finite coefficient extension: `(l : ℕ) [Fact l.Prime]`, `(E : Type
   (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
   Verdict: the required finite extension, without a characteristic or ramification
   restriction. The valuation ring and uniformizer are the existing
   `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`.
   I opened `pbcPadicCoefficientDatum`: its ideal is literally the span of this
   uniformizer, with actual data and named coefficient-facts proofs.
2. Objects and square: `{X' X Y' Y : Scheme.{u}}` and the four named morphisms.
   `c : Compactification f`, `c' : Compactification f'`, and `gbar`, together with
   `properSquare : ChosenCartesianSquare gbar c'.g c.g g` and
   `openSquare : OpenImmersionSquare g' c'.i c.i gbar`, render the chosen
   compactification and its pullback. Verdict: exact. I opened both square
   structures: each retains an actual fibre-product isomorphism and both projection
   equations. Pasting these two Cartesian squares gives the outer square. I opened
   upstream `Compactification` and `baseChange`/`ofIsPullback`: neither imposes
   density. The supplied squares allow arbitrary isomorphic presentations of the
   canonical base change. A background S-structure in the square definition imposes
   no additional condition on this absolute assertion or its conclusion.
3. Geometric hypotheses: `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`
   render separated finite type; the four `[IsNoetherian ...]` and `_dim...`
   binders render noetherianity and finite dimension of every corner. The four
   `_hl... : ∀ x, IsUnit (l : ...presheaf.stalk x)` render invertibility of l.
   Verdict: exact, including the empty scheme. There is no property instance on g
   or g', and no smoothness or properness condition on either horizontal map.
4. Integral category: `PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum
   l E)`. I read the underlying predicate in `BoundedConstructibleComplete`:
   `PbcIsIntrinsicallyComplete ∧ PbcHasUniformConstructibleReductions ∧
   PbcHasCompatibleEtaleOrigins`. The last predicate includes the actual quotient
   normalization equation, not merely independent finite-level origins. Verdict:
   the dependency's exact three-clause full subcategory is used. Its convenience
   specialization is an abbreviation for this same category, not another notion.
5. Integral operations: `cbcCompactSupportSource` is `j_! ⋙ Rp_* ⋙ completedPull g`;
   `cbcCompactSupportTarget` is `completedPull g' ⋙ j'_! ⋙ Rp'_*`.
   Verdict: correct direction and order. I read `AdicCoefficientDatum.completedPull`,
   the recorded `pbcActualStrictCompletedPull` interface, `cbcSupport`, and
   `proEtaleRingCompactSupportImage`: they use the reduction tower, tower pullback,
   derived limit, and the existing open/proper operations. The completion interface
   retains the quotient unit. No arbitrary functor replaces completed pullback.
   The existential `hSource`/`hTarget` establish category landing, rather than
   assuming it of the input. Their full-subcategory lifts have explicit data.
6. Rational objects and functors: `cbcCompactSupportSourceTransport` and
   `cbcCompactSupportTargetTransport` use `ScalarLocalization.transport` of these
   lifts. I read `PbcRationalCategory`, `pbcRationalization`, `transport` and its
   linearity and pure-tensor interfaces: objects are unchanged, Hom modules are
   localized, and integral arrows map to tensor with one. Verdict: the raw rational
   category of the node, with the existing canonical identification of the localized
   coefficient ring with E; no Karoubi envelope or extra lattice-existence premise.
7. Specified exchange and invertibility: the main theorem concludes `∃ η : F ≅ G`
   and fixes every component by equality with
   `finiteExtensionCompactSupportExchangeComponent`. That definition is precisely
   `pbcRationalization.map (ObjectProperty.homMk
   (completedCompactSupportExchange ...))`. I opened the latter declaration: it is
   the proper strict-tower exchange followed by direct image of the canonical open
   comparison, in that order. Verdict: every component is the specified exchange
   and is invertible. The auxiliary `finiteExtension_cbcComplete` supplies
   `cbcCompleteProperty` for every selected integral object and generating tuple,
   so the component equation's proof binder does not restrict the theorem to a
   smaller class of inputs. Its proof docstring explains representative and tuple
   transport through the canonical quotient-tower unit.
8. Naturality and lattice independence: `η` is a natural isomorphism between the
   scalar-localized functors, hence its naturality equation holds for every rational
   Hom element. Verdict: this also covers any rational isomorphism between two
   integral representatives; the induced endpoint maps are exactly `F.mapIso` and
   `G.mapIso` of that isomorphism. No integral lift or chosen integral map is assumed.
9. Identity: `_identity` localizes the equality between the exchange followed by
   `cbcSupport.map completedPullId` and `completedPullId` on the image. Verdict:
   precisely the unit-normalized identity diagram; its completeness and category
   witnesses are conclusions. I compared its arrow order with
   `completeCompactSupportProetale_identity`.
10. Pasting: `_horizontal` equates the direct exchange to successive exchanges
    conjugated by the actual `completedPullComp` maps. `_vertical` uses
    `cbcTowerCompositionMap` on supplied compatible compactification towers, with
    the proper/open pullback and commutation equations written out. Verdict: these
    are the canonical comparison paths, not freely chosen endpoint isomorphisms.
    I compared both signatures with the integral horizontal/vertical statements,
    and read the integral compactification/refinement and composition-refinement
    interfaces: compatible towers and common refinements cover arbitrary pasted
    squares. Every corner of the pasted square is required to satisfy
    `CbcFiniteExtensionDomain`, exactly the three original scheme conditions.

Edge cases: zero complexes and empty schemes are admitted; no `Nonempty` or
positive dimension assumption occurs. Dimension zero is included by the existential
natural-number bound, and the empty space's bottom dimension is included. The empty
finite generating tuple is quantified over; its span condition is retained (for this
nonzero DVR ideal it cannot generate, correctly). The positive quotient stages are
indexed by n+1 in the inherited coefficient construction; no spurious quotient stage
n=0 is assumed. All primes, including 2, are covered; a point of residue characteristic
l is excluded exactly by the stated invertibility condition. The scheme universe is
arbitrary u and coefficients are in the existing small-site coefficient universe u+1;
there is no new equality of site object and morphism universes or independent smaller
universe for quantified tests. All variables are explicitly bound (`autoImplicit false`).

Independent duplicate searches: LeanFinder queried “Scalar extension of compactly
supported cohomology base change is a natural isomorphism on rationalized adic
complexes” and returned eight group representation/cohomology results, none matching.
LeanSearch queried compactly supported derived direct image and adic base change after
inverting a uniformizer; its eight results concern algebraic module base change and
stability of scheme morphism properties, not this assertion. Loogle's valid query
`"baseChange", CategoryTheory.IsIso` returned six Kan-extension declarations. An earlier
query using `CategoryTheory.NatIso` reported an unknown identifier and is not negative
search evidence. The wrapper grep query `LowerShriek|compact.support|ScalarLocalization`
in Mathlib AlgebraicGeometry returned zero hits. Direct `rg` searches in Mathlib
AlgebraicGeometry/CategoryTheory, upstream WeilConjectures, the project's lean/Sheaf,
and `dag/lean_names_upstream.json` found no existing declaration of the delivered
finite-extension compact-support theorem or collision for the helper names. I opened
the near matches `isBoundedConstructible_compactSupport_and_baseChange` (prime-field
finite torsion coefficients), `etale_compactSupport_baseChange_qcqs` (finite coefficients,
bounded-below etale category), and `pbcRationalExchange` (transport of supplied proper
operations): none states this completed compact-support assertion. No new definition
nodes or dependency modules are in the delivery; there are no such extra interfaces
requiring an H12/H13 review. The two extra statement dependencies supply the actual
coherence maps whose signatures the displayed paths use.

Mismatch repaired: the original main theorem redundantly conjoined
`∀ K, IsIso (η.hom.app ⟨K⟩)` after already quantifying `η : F ≅ G`. I removed that
logically automatic conjunct, retaining the natural isomorphism and its canonical
component equation. The worker report's earlier description of an “explicit component
IsIso assertion” is superseded by this repair. The JSON `lean.statement` was refreshed
verbatim from the resulting signature. This changes no mathematical statement and
requires no source-based `statement_change`. Every definition still has explicit data;
all 13 theorem proofs remain `sorry`, with source/blueprint and proof docstrings.
No proof was filled and no correct construction was rewritten.

Verification of the repaired module and final server preflight is recorded below.

The repaired module passed `scompile.py Q06 thm-cbc-finite-extension
lean/Sheaf/Paper/FiniteExtensionCompactSupportBaseChange.lean` with exit status 0.
After rebuilding current side overlays, its sandbox check took 4.6 seconds and its
library check 6.0 seconds. There were no errors or unexpected warnings. The complete
output is `scratchpad/second-reading-compile.log`. The exact primary-signature equality
and the 100-character bound were also rechecked after the repair.

The required repaired-delivery dry run printed `OK (dry run): commit 8fac0b16b5
passes the preflight and compiles; nothing pushed`. It staged exactly the report,
item node and one module. Its complete output is
`scratchpad/second-reading-dry-run.log`.
