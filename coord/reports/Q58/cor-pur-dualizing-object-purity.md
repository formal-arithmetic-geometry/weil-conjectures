## Worker report

`Sheaf.Paper.DualizingObjectPurity` states
`WeilConjectures.PurityFiniteSetting.dualizingObjectPurity` with `sorry`.
The mathematical item statement is unchanged. This repairs return R1 against
immutable head 4bf811de5ff8 and the currently published ND exchange module.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `P : PurityFiniteSetting.{u}` fixes the finite-field datum, distinct coefficient
  prime, finite extension E in the fixed algebraic closure, and positive level n.
  `P.Ring` is O_E/(varpi_E^n); no ramification divisibility is imposed.
- `X Y : Scheme.{u}`, their `Over (Spec (.of P.field.k))` instances, and
  `LocallyOfFiniteType` plus `QuasiCompact` structure maps give exactly finite-type
  k-schemes. Neither scheme is required to be absolutely separated.
- `f`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, and
  `SmoothOfRelativeDimension d f` give the smooth separated finite-type
  k-morphism of pure relative dimension `d : ℕ`, including d=0. Compactification
  is supplied by the published construction rather than assumed.
- `K : Scheme.proEtaleDerivedCategory Y P.Ring` with `hK : finiteTorConstructible
  ... Y K` is the bounded constructible finite-Tor input on the small pro-etale
  site, retaining the original coefficient object.
- `∃ hγ : IsIso (P.smoothPurityMap f d K hK), ...` asserts invertibility of the
  specified reassociation / inverse diagonal orientation / tensor counit mate
  composite. Its Tate exponent is d and shift is 2d. The Kummer-normalized
  diagonal orientation and `diagonalTwist` are the recorded ones, not choices
  of endpoint isomorphisms. `coefficientValuedSmoothTrace` is compact-support
  image of this same map followed by the recorded exceptional counit; the
  corollary introduces no second normalization or additional trace equation.
- The first conjunct quantifies every Cartesian square `sq : IsPullback ...`
  of finite-type k-schemes, without a smoothness, flatness or properness
  restriction on v. The instances on f' are precisely the consequences of
  base change of f, so exclude no square. `∃ hK'` asserts finite-Tor
  constructibility of `(P.finiteReductionPullback v).obj K`; `∃ hγ'` asserts
  invertibility of the corresponding original purity map. Neither is an input
  hypothesis. The equation is pulled-back gamma, then
  `finiteReductionSmoothExchange`, equal to
  `finiteReductionBaseChangeSource`, then gamma'. The exchange uses its
  published canonical proof witnesses; proof irrelevance identifies hK' with
  `finiteReductionBaseChangeInput`. Inverses of a fixed arrow are unique.
- The second conjunct quantifies a finite-type k-scheme Z, every smooth
  separated finite-type g:Y→Z of pure dimension `e : ℕ`, and every intrinsic
  finite-Tor constructible L on Z. It states the exact equation for gamma_fg
  in dimension d+e: `compositionSourceIdentification.hom`, shifted pullback
  of gamma_g, gamma_f at `compositionExceptional g`, then
  `compositionExceptionalIso.inv`. `compositionExceptional_ctf` supplies the
  second purity map's domain. The comparator is the standing counit mate,
  transported through the original realization equivalences.

Dependency declarations used/read:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Ring`, `Coefficient`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded
  exceptional system; the actual finite functor is `ProEtale.sfFiniteExceptionalAt`
  through `smoothPurityExceptionalOver` in `Sheaf.Paper.SmoothPurityMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  the Mathlib pro-etale site is `Scheme.ProEt` with `ProEt.topology`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: recorded derived operations. Their
  finite intrinsic realization coordinates are used by the purity modules.
- `Sheaf.Paper.FixedFinitePositiveCoefficientTwist` (reexported by the recorded
  `PbcCoefficientTwists` module): `diagonalTwist`, `diagonalTwistEtale`.
- `Sheaf.Paper.PurityDiagonalDualizingObject`: `diagonalDualizingObject`,
  its unique Kummer normalization and full-domain theorem.
- `Sheaf.Paper.SmoothPurityMap`: `smoothPurityReassociation`,
  `smoothPurityTensorMapInPresentation`, `smoothPurityTensorMap`, `smoothPurityMap`.
- `Sheaf.Paper.SmoothTrace`: `smoothCompactSupport`, `smoothExceptionalCounit`,
  `coefficientValuedSmoothTrace`, `smoothTrace`.
- `Sheaf.Paper.FiniteReductionRootCharts`: `finiteReductionPullback`, the exact
  same realization pullback previously duplicated as smoothExchangePullback.
- `Sheaf.Paper.FiniteSmoothPullbackExchange`: all eight ND declaration names
  retained, especially `finiteReductionBaseChangeSource`,
  `finiteReductionBaseChangeInput`, `finiteReductionSmoothExchange`.
- `Sheaf.Paper.PurityCompositionCoherence`: all 39 recorded declarations retained,
  especially `compositionSourceIdentification`, `compositionShiftedPullback`,
  `compositionExceptional`, `compositionExceptional_ctf`,
  `compositionExceptionalIso`, `smoothPurityCompositionCoherence`.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`: recorded cohomological smoothness
  supplies the tensor invertibility proof route. Its direct proof import remains
  omitted because the retired ProEtale.Derived.Tensor chain collides with the
  required FiniteCoefficient.Derived.Tensor chain; the proof docstring cites it.
- `def-weil-scheme-morphism-properties` is a convention node; the actual Mathlib
  instances above implement its separated/finite-type conventions.
- The current `def-pur-section-invariant` binding is
  `Sheaf.Paper.PuritySectionInvariantIntrinsic.sectionInvariantFinite` (namespace
  `WeilConjectures.PurityFiniteSetting`). It was read; it is not used in this
  corollary's type. Its earlier retired-module binding is not reused.

The unchanged proof docstring lists all six DAG steps. The unstated proof
prerequisites projection-purity-agreement, vector-integration-site-comparison,
and smooth-base-change-coherence are cited in that plan without being added as
hypotheses. Unused broad common-stage imports remain omitted.

Searches performed:

- msearch.py leansearch, query `Smooth purity for finite coefficient sheaves:
  the canonical exceptional pullback is derived pullback with Tate twist and
  shift, compatible with base change and composition`: eight ordinary sheaf
  and module pullback, adjunction, and composition hits; none concerns
  exceptional image, Tate twists or smooth purity.

- msearch.py leanfinder, query `canonical smooth purity exceptional inverse
  image Tate twist shift pro etale base change composition`: eight ordinary
  module-pullback/pseudofunctor/adjunction hits; no smooth purity statement.
- msearch.py loogle, query `AlgebraicGeometry.Smooth, CategoryTheory.IsIso`:
  one normalization-pullback isomorphism for schemes, unrelated to exceptional
  inverse image, Tate twists, or the specified purity map.
- msearch.py grep, query `smoothPurity|dualizingComplex|TateTwist` under
  Mathlib/AlgebraicGeometry: zero hits.
- rg on the upstream `WeilConjectures` source for the item id and purity names:
  `EtaleCohomology/Purity/Smooth/Basic.lean` has
  `nonempty_iso_rightDerivedUpperShriek_twistShift` and `smoothPurityIso`.
  Their full signatures and docstrings were read: ordinary etale site,
  absolute separatedness, and freely supplied constituent isomorphisms do not
  state this full-domain canonical pro-etale result or all its coherence clauses.
- rg on `lean/Sheaf/Paper`: `FiniteCoefficientSmoothPurity.isIso_smoothPurityMap`
  assumes absolute separatedness and asserts only invertibility; it is not
  this node. The canonical diagonal and composition interfaces were reused.
- `scompile.py --source Sheaf.Paper.SmoothPurityMap` confirmed the live
  restricted interface equals the source read locally. A guessed upstream
  `...Derived.Intrinsic` module was unavailable; reading the actual owning
  `SfIntrinsicRealizationTransport` and `ProEtaleIntrinsicFiniteOperations`
  sources resolved the pullback and realization names without inventing a notion.


Repair searches/readings on 2026-10-18:

- `rg` in shared `lean/Sheaf/Paper` located ND's live
  `FiniteSmoothPullbackExchange` and its `FiniteReductionOfPurity` consumers.
  Their complete sources were opened. ND's `finiteReductionPullback` is the
  same expression as the removed smoothExchangePullback; the published root-chart
  source identification already gives the needed middle arrow.
- `rg` and a full reading of `PurityCompositionCoherence` locate all existing
  exceptional/composition helpers. Its three absolute-separatedness variables
  are the only obstacle to using those names on the full domain; no new notion
  or new definition node is required.
- Reopened upstream EtaleCohomology/Purity/Smooth/Basic.lean and searched the
  item id and smoothPurityIso; its supplied orientation/tensor isomorphisms and
  ordinary-etale category still do not state the present corollary.

Edge cases checked: d=0, e=0, identity base change and composition, K=0, empty
schemes, arbitrary nonflat base change, nonseparated finite-type bases such as
the doubled-origin line, n=1, ramified E and levels not divisible by ramification.
The common scheme universe u remains arbitrary and no new universe equality is
introduced. No counterexample or statement fault was found; no statement correction.

## Dependency modules

`def-pur-smooth-purity-map`: retained repair of the existing owning module removes
absolute separatedness of X,Y from its final three interfaces. The constituent
maps, canonical normalization, names and full finite-type hypotheses are unchanged.

`def-pur-smooth-trace`: retained repair removes absolute-separatedness binders from
the support functor and counit/trace interfaces. It retains their concrete maps,
compactification construction and counit normalization on bounded-below inputs.

`def-pur-smooth-pullback-exchange`: R1 repaired by generalizing ND's actual
`Sheaf.Paper.FiniteSmoothPullbackExchange`, removing exactly the four absolute
`IsSeparated` scheme variables. Its eight declaration names, root-chart
normalization, concrete composites and main declaration are retained. The dependency
record is based on ND's current record, with only its `lean` repaired as required by
§1(B); the main declaration and declarations list are preserved. It targets the
now generalized `compositionExceptional` in its owning module. The separated
specialization remains definitionally the same, so existing finite-reduction
callers need no new names. No `SmoothPurityExchange.lean` is delivered.

`thm-pur-composition-coherence`: generalize the existing owning
`Sheaf.Paper.PurityCompositionCoherence` under §1(B) by removing only its three
absolute `IsSeparated` scheme variables. All 39 declaration names and every
construction term are retained. This repairs the six exceptional interfaces in
place, rather than placing six `...All` aliases under the exchange node. The
corollary now cites this already-landed node explicitly in stmt_deps, and uses
its existing `compositionSourceIdentification` and exceptional maps directly.
The former proposed def-pur-composition-comparisons record is not delivered:
the published composition node already owns the canonical comparisons.

## Second reading by Q58

This is the author's second reading; the brief forbids starting another agent and
assigns independent review to the maintainer. I opened the unchanged item node,
current main-20261015 source, all five delivered modules and ND's published consumer.
R1's every request is addressed: keep ND names and primary record; generalize
four exchange variables; target the full-domain exceptional functor; state the
base-change equation with finiteReductionPullback/BaseChangeSource/SmoothExchange;
remove the six exceptional aliases from the exchange node; validate the existing
FiniteReductionOfPurity consumer against these modules.

The composition module changes only three absolute-separatedness variable lines;
the exchange module changes only four such lines. Existing separated callers
retain the same canonical constructions. The main theorem still asserts the
original gamma's invertibility and both hK'/hγ' consequences, arbitrary base
change and the exact composition equation with d+e. It uses ND's root-chart
normalized source comparison and the existing standing counit mate, with no new
orientation choice, arbitrary map, strengthened hypothesis or weakened conclusion.
Definitions have real data and postponed theorems have their existing proof
docstrings and matching nodes. All universes and variables are explicitly bound.
The node comparison confirms only lean changes for the four dependencies and
only lean/stmt_deps for the item; maintainer review metadata is untouched.

## Validation

The first action after reading the retained report was the prescribed saved-packet
dry run. Its output is recorded below, followed by the repaired packet checks.

The initial saved-packet run reached its compiler checks, but packet assembly
then failed because I renamed the obsolete SmoothPurityExchange.lean while that
run was still active. This was a sequencing mistake. The repaired packet is kept
stable for the subsequent full dry run and push.

The required scompile.py run of all five delivered files plus the unchanged
read-only FiniteReductionOfPurity consumer completed with exit 0 after automatic
server confirmation. Individual delivered-file times: SmoothPurityMap 9.7 s,
SmoothTrace 5.4 s, PurityCompositionCoherence 9.0 s,
FiniteSmoothPullbackExchange 6.5 s and DualizingObjectPurity 6.1 s.
The unchanged FiniteReductionOfPurity consumer compiled in 8.3 s against these
repaired modules. Thus ND's separated finite-reduction specialization still
elaborates with its original names and no caller edit. The initial missing-cache
artifact was resolved by the wrapper's server confirmation.

Static self-check: all recorded declaration lists match their modules; each
lean.statement matches from its declaration keyword to :=; every Lean line is
at most 100 columns. All four dependency node copies differ from current main
only in lean. The item differs only in lean and in adding the landed
thm-pur-composition-coherence to stmt_deps. All eight ND exchange names and all
39 composition names are retained. The duplicate exchange module and proposed
comparison definition node are outside the delivery.

Repeated repair searches with msearch.py: Loogle on AlgebraicGeometry.Smooth,
CategoryTheory.IsIso returned only normalizationPullback; LeanFinder on canonical
smooth purity/exceptional inverse image/Tate twist/shift/pro-etale/base change/
composition returned eight ordinary module pullback/pseudofunctor hits; Mathlib
grep for smoothPurity|dualizingComplex|TateTwist under AlgebraicGeometry had zero
hits. These confirm the previously recorded no-match results.

Final repaired deliver2.py --no-push completed with exit 0:
OK (dry run): commit bc75f1ca18 passes the preflight and compiles; nothing pushed.
It staged exactly the corollary, the four owning dependency module/node repairs
and this report. The source files and node records are unchanged for the push.

## New nodes

Return H2 against immutable head a2a66f78e371 restores
`def-pur-composition-comparisons` from the saved 36be74cc90e0 record, byte for byte,
with `existing: true` on
`WeilConjectures.PurityFiniteSetting.compositionSourceIdentification` in
`Sheaf.Paper.PurityCompositionCoherence`. Its source is the main-20261015
composition statement and proof Step 2, as recorded in the node. The existing
`compositionShiftedPullback`, `compositionExceptional`,
`compositionExceptionalIso` and helper `compositionExceptional_ctf` from that
same module supply the other terms used in the corollary's type. No Lean
declaration or module is added for this node.

The saved node retains its recorded LeanSearch and LeanFinder searches (eight
ordinary pullback-composition hits each), Mathlib grep (zero purity-comparison
hits), upstream/project grep (the existing owning module), and DAG/blueprint
search (no definition node for these canonical comparisons). The node records
the existing notion rather than introducing another definition. Its full
normalization and exceptional comparison are precisely those already read and
used in the worker report above; zero dimensions, identities and zero objects
retain the same constructions.

This return supersedes the earlier report sentences saying this definition
node is not delivered and the theorem belongs in stmt_deps. The item now cites
`def-pur-composition-comparisons` in stmt_deps; `thm-pur-composition-coherence`
remains in proof_deps. Only the item stmt_deps field and this required report
addendum differ from the retained packet, besides restoring the definition
node. The five Lean modules and all four existing dependency node records
remain byte-identical. Every recorded signature was checked verbatim and all
recorded declarations were found in their owning modules (8 ND exchange names
and 39 composition names retained). The repaired packet passed compilation,
including the existing-declaration probe; its first preflight requested only
this nonempty New nodes section. No statement or proof was changed.
