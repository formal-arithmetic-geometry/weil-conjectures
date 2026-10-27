## Worker report

Q31, stage 2, item lem-zl-curve-restriction-filtration-spectrum.
The module Sheaf.Paper.CurveRestrictionFiltrationSpectrum states the node in
`WeilConjectures.zl_curve_restriction_filtration_spectrum`, through the completely
written proposition `ZlCurveRestrictionFiltrationSpectrum`. The only `sorry` in this
delivery is that named theorem, with the node's nine-step natural-language proof.
All helper data, maps and isomorphisms are real constructions or fields of explicitly
specified comparison records; no data definition has `sorry`.

The latest source read is
literature/blueprint/latest/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md,
paragraphs 1–2. The node's source, statement, proof and proof dependencies are unchanged.

### Hypotheses and clauses

* The finite field and its closure are `D : FiniteFieldDatum.{u}`. The prime,
  characteristic exclusion, coefficient closure and chosen complex realization are
  `[Fact l.Prime]`, `hl : l ≠ D.p`, `Ω : Type (u+1)` with its field, Q_l algebra and
  algebraic-closure instances, and `iota : Ω ≃+* ℂ`. These are the recorded classical
  adic coefficient universes, not an extra equality of universes.
* The separated finite-type scheme is `X₀ : Over (Spec (.of D.k₀))` with
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` on `X₀.hom`.
* The extension is `m : ℕ`, `hm : 1 ≤ m`, the recorded `D.extensionSubfield m hm`
  and `constantExtensionDatum`/`constantExtensionModel`. The curve is `C₀` over that
  field with `LocallyOfFiniteType C₀.hom` and `QuasiCompact C₀.hom`; the immersion
  is `h₀` with `[IsClosedImmersion h₀.left]`. No dimension, smoothness, nonemptiness
  or connectedness assumption is added. Its separatedness is inherited by the real
  class-valued constructions `zlCurveModelSeparated` and `zlCurveSeparated`.
* `F : ZlClassicalFiltration D l Ω X₀ r` is the prescribed classical lisse Weil
  filtration, with actual inclusions, quotients, zero initial term and fibrewise
  short exactness. `G` and the supplied top isomorphism `e` retain its specified
  realization. `RX` and `RC` are arbitrary recorded normalized realizations. The
  prime-unit instances they need are constructed from `zlClassicalStalkInvertible`,
  not assumed independently.
* `R` is any constant-restriction functor satisfying the recorded
  `ConstantExtensionRestrictionSpec`. `zlCurveRestriction` is literally
  `R ⋙ zlWeilPull ... h₀`. The specification fixes the m-fold Weil map, including
  its normalized return/composition comparison; it is not an arbitrary Weil action.
* `ZlCurveClassicalPullback.classical` and `.geometric` give the classical Weil
  and geometric inverse images. `.models` identifies the latter, at every finite
  coefficient field, with the `CompletedLisse.System.operation` of the actual
  composite geometric morphism and identity coefficient map. This operation is
  ordinary finite-level inverse image and inverse-limit completion, with its
  reduction, rational-map and identity/composition normalizations.
* `.forget`, `.geometric_realization`, `.realization` and
  `.realization_underlying` identify the actual functors and maps. They are natural
  isomorphisms, hence include all arrows and their composites, and the Weil-category
  isomorphism includes descent and its inverse. `.constant_comparison` and
  `.constant_weil` specify the given constant restriction. The equation
  `.underlying_normalization` pins the geometric comparison to pullback of that
  comparison followed by the inverse of the integral-normalized `zlPullComp`.
* The output `F' : ZlClassicalFiltration ... r` is a classical lisse filtration.
  Its term and quotient equalities, and the two `HEq` map equations, retain exactly
  the inverse images of the prescribed diagram. They do not replace it by an
  unrelated filtration. The target top isomorphism `e'` is explicitly the inverse
  realization comparison followed by `R_m.mapIso e`.
* The source and target `ZlFiltrationTransport` records give finite-stage
  realizations of the entire diagram, with both arrows, Weil maps and inverse maps,
  exactness, natural fibre comparisons and local operators for every positive
  return period. Their `ZlClassicalFibreComparison.local_operator` uses the specified
  point-Frobenius action on every finite etale cover for every n, including the
  iterated point transports, rather than an arbitrary return path.
* `IsZero` for the restricted initial term and the displayed `ShortComplex.ShortExact`
  for each `j : Fin r` express exactness with the actual restricted quotient maps.
  Thus the quotients are canonically the restricted prescribed quotients.
* For every filtration term or quotient `H`, `IsCommonStageLisse` states lissity of
  its restricted realization. Classical lissity is also part of `F'` and the
  classical pullback functor above. `ZlCurveLocalConclusions` applies to exactly
  these terms and quotients.
* The arithmetic image is the actual composite `zlCurveArithmeticMap`; `hx` says
  its image of each closed `z` is closed. Its `Scheme.Hom.residueDegree` is the
  actual residue-field degree, with `1 ≤ ...`. The next equation is exactly
  `q_z = q_x ^ f`, using `Nat.card` of the two residue fields.
* The normalized stalk comparison is the real construction `zlCurveFiniteStalkIso`:
  pull back the finite carrier comparison, invert the normalized pullback compositor,
  use equality of the geometric lifts, apply normalized point sections and H^0,
  raise the module universe with `ULift`, and extend coefficients to Ω. The
  point-base identification is itself constructed from the same recorded
  `pointRationalNormalization` on both sides. It is not a chosen linear equivalence.
* `ZlCurveFiniteModel.normalization` pins each finite carrier presentation to
  `.underlying`. Such a presentation is asserted to exist; the operator equality
  is required for every such presentation and every compatible geometric lift.
  `zlCurveFiniteFrobenius` is precisely the recorded finite-stage local operator
  after the same ULift/scalar extension. The equality is `F_z ≫ c = c ≫ F_x^f`,
  i.e. c conjugates the target operator to the residue-degree power.
* The spectrum equation uses `.reverse.roots` of `sfLocalCharacteristicFactor`,
  whose reverse is the characteristic polynomial of the invertible local operator.
  It is a `Multiset.map (fun a => a^f)` equality, retaining algebraic multiplicities
  and adding the multiplicities of coincident powers, not a set equality.
* The final implication is the recorded `SfIsReal` predicate on `G` and `R_m G`
  for `iota.toRingHom`. No distinctness, semisimplicity or diagonalizability premise
  is present.

### Dependency declarations used

All names below are in namespace WeilConjectures unless another namespace is given.
The original dependency records and their source declarations were read.

* Sheaf.Paper.AdicPunctualWeights: `SfPunctualEigenvalue`,
  `SfIsPunctuallyPureOfWeight`, used by the recorded filtration transport.
* Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  `AlgebraicGeometry.IsClosedImmersion`; the finite-type convention is Mathlib's
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
* WeilConjectures.AlgebraicGeometry.BaseChangeConventions: the recorded scheme
  pullback/Over base-change convention, with `Limits.pullback` and its projections.
* Sheaf.Paper.LisseIntegralSmallCoefficients, publicly importing LisseAdicSheaves:
  the actual `AlgebraicGeometry.Scheme.LisseAlgebraicSheaf` and finite lisse models.
* Sheaf.Paper.EtaleWeilFundamentalRepresentation: `EtaleLisseWeilSheaf`, behind
  `ZlClassicalWeil`; actual Weil isomorphisms in the fixed-pair category.
* Sheaf.Paper.SfWeilSheafComplex and the recorded constructible-heart interface:
  `sfWeilComplex`, `sfCommonStageWeilSheaf`, `sfWeilStageObject`.
* Sheaf.Paper.CommonStageLocallyFree: `IsCommonStageLisse`.
* Sheaf.Paper.ConstantExtensionWeilHeartEquivalence: `constantExtensionDatum`,
  `constantExtensionModel`, `constantExtensionProjection`, `constantExtensionFiberIso`,
  `constantExtensionHeartForget`, `constantExtensionWeilIterate`,
  `constantExtensionFiberPull`, `constantExtensionRestrictionComparison`,
  `ConstantExtensionRestrictionSpec`.
* Sheaf.Paper.DerivedPullbackTensorHom: `rationalDerivedPullback`,
  `commonStageDerivedPullback`, `commonStageDerivedPullback_existsUnique`.
* Sheaf.Paper.LocalFrobeniusTrace: `localDerivedStalk`, `localPullbackComposition`,
  `localClosedPoint`, `localClosedFrobeniusCohomology`, with their specified point
  transports, Weil iterates and return compositor.
* Sheaf.Paper.AdicLocalCharacteristicFactor: `sfLocalCharacteristicFactor`, `SfIsReal`.
* Sheaf.Paper.ClassicalWeilFiltrationHeartTransport: `ZlClassicalFiltration`,
  `ZlFiltrationTransport`, `ZlClassicalFibreComparison`, `zlExtendedFiniteFibre`.
* Sheaf.Paper.NormalizedClassicalWeilRealization: `ZlClassicalRealization`,
  `ZlClassicalRealization.weil`, `zlClassicalModel`, `zlClassicalStalkInvertible`.
* Sheaf.Paper.LisseCompletedSystemData:
  `AlgebraicGeometry.ProEtale.CompletedLisse.System`, `.Arrow`, normalized operations.
* Sheaf.Paper.WeilIndSheafCategory, through the public dependencies:
  `zlFiberMap`, `zlWeilPull`, `zlPullComp`.
* Proof imports retain the available node declarations in ZlImmersionWeilLocalBehavior,
  LisseCompletedSystemComparison, LisseRationalRealization and
  Sheaf.LinearAlgebra.PowerSpectrumConjugation (`LinearMap.power_spectrum_conjugation`).

The additional statement dependencies are
def-zl-classical-weil-filtration-transport-data (added in this H2 repair),
def-zl-normalized-classical-weil-realization and def-per-lisse-completed-system-data.
The last two are already landed; the first records ownership of the exact existing
filtration data definitions. The theorem lem-zl-classical-weil-filtration-heart-transport
is retained in proof_deps and is no longer cited in stmt_deps. Its conclusion is used
only by the proof plan. All data declarations are reused, not copied.

### Edge cases and searches

Checked r=0 (Fin 0 has no quotient conditions, sole term is zero), zero-rank stalks
(characteristic polynomial 1 and empty root multiset), empty C₀ (no closed points),
disconnected schemes, m=1, and residue degree f=1 after a nontrivial constant extension.
For q=2, m=2 and an original degree-two point, f can be 1: the statement uses the
residue degree, not m. The eigenvalues i and -i both square to -1, retained twice.
A nontrivial Jordan block has the same algebraic multiplicities after powering;
there is no semisimplicity assumption. The finite-stage ULift construction accommodates
the existing classical Ω universe without shrinking or equating scheme/coefficient
universes. Compatible geometric lifts are quantified with their actual map equality.

Searches performed for this item:

* msearch.py leanfinder: "Restriction of a lisse Weil sheaf filtration along a curve
  over a finite constant extension is exact and local Frobenius eigenvalues are
  residue degree powers" — 8 unrelated arithmetic Frobenius/Witt-type results,
  no match for the assertion.
* msearch.py loogle: "ShortComplex.ShortExact, LinearMap.charpoly, Multiset.map" —
  no result; first identifier was not recognized by the search service.
* msearch.py loogle: "LinearMap.charpoly" — 12 hits including charpoly,
  charpoly_natDegree, charpoly_sub_smul and aeval_self_charpoly. These are polynomial
  tools, not this sheaf restriction theorem.
* msearch.py grep: "curve.*restriction|restriction.*filtration" — no Mathlib match.
* rg in lean/WeilConjectures and lean/Sheaf for restriction/filtration/Frobenius names,
  plus the exact item id in lean/WeilConjectures — found the generic filtration,
  constant-extension and immersion interfaces used here, and a downstream consumer;
  no existing declaration of this item. Follow-up rg located the exact normalized
  point, pullback compositor, classical finite models and local-factor signatures.

No statement correction, disputed statement, or dependency replacement is proposed.

## New nodes

`def-zl-classical-weil-filtration-transport-data` owns the existing declarations in
Sheaf.Paper.ClassicalWeilFiltrationHeartTransport, with `existing: true` and no new
module: zlClassicalStep, zlClassicalOrbitPoint, zlClassicalSteps, zlClassicalLocal,
zlFiniteFibre, zlExtendedFiniteFibre, zlFiniteFibreMap, ZlClassicalFibreComparison,
ZlClassicalFiltration, ZlFiniteFiltration, ZlClassicalPure and ZlFiltrationTransport.
Its statement describes precisely these constructions and all defining fields of the
filtration and comparison records, including prescribed arrows, one finite stage,
all return periods, top identification, exactness, naturality and purity equivalence.
It asserts no existence result. Its stmt_deps cite only underlying definition nodes.
The main existence proposition and theorem remain with the theorem node.

Source: latest blueprint real-mixed-by-curves proof paragraphs 1–2 and 4, and the
existing declarations' Bhatt–Scholze 6.8.4, 6.8.14, 6.8.15 and Weil II 1.1.8–1.1.10
citations. Search logs are recorded verbatim as structured msearch responses in the
new node: LeanSearch and LeanFinder each returned eight unrelated general filtration,
isocrystal or condensed-module declarations; Mathlib grep found no matches.
`blueprint_refs.py search classical-weil-filtration` returned zero nodes. The exact-name
rg across dag/nodes, lean/WeilConjectures and lean/Sheaf found the declarations only
in the landed theorem module and its theorem node's declarations list, with no existing
definition owner. The new node registers those existing definitions rather than making
a second definition or extracting/copying their Lean code. The original item helpers
remain owned by the item's lean.declarations.

## Dependency modules

None. All used dependencies have usable landed interfaces. The finite-stage route
uses their actual coefficient universes and normalized point models.

## Clause review

Q31 re-read the complete node against the final proposition after compilation, including
r=0, quotient arrows, all-period local comparisons, residue degree, multiplicities,
reality and the absence of semisimplicity. This is a worker self-check; the independent
review is the maintainer's delivery review, as prescribed in the dispatcher brief.

## Validation

All compiler calls use scompile.py; no live library files were edited, no git command
was run in the shared repository, and no global build was run. The initial complete
module compiled without errors or warnings. The final normalized-comparison revision
also compiled without errors or warnings (48.4 s sandbox, 56.4 s module). The prescribed
deliver2.py --no-push dry run returned OK: commit 294b7d2bbe8 passed the server
preflight and per-file compilation. This report update records that result before
the final delivery invocation.

## Returned delivery repair H2

Returned immutable head: ad0e30c2c36b. The maintainer accepted the mathematics and
requested that statement dependencies own the plain filtration data independently
of the existence theorem. Added def-zl-classical-weil-filtration-transport-data as an
existing-declaration definition node with all required metadata, searches and a
self-contained data-only statement. Replaced the theorem id in the item's stmt_deps
with this definition id; retained the theorem unchanged in proof_deps. No Lean
statement, definition or theorem body changed. The report's dependency and new-node
sections were updated accordingly. This repairs the ownership mismatch rather than
rebasing or re-pushing the old packet.

Compared retained sandbox data to the current read-only repository: all item fields
except the authorized lean/stmt_deps delivery fields agree. The new definition node
was absent from the current DAG. deliver2.py will build the repaired packet on the
current server branch. The unchanged theorem module is recompiled via scompile.py
and both delivery checks are rerun for this repaired packet.

Repair validation: scompile.py successfully recompiled CurveRestrictionFiltrationSpectrum.
The repaired deliver2.py --no-push invocation checked both the existing data declarations
and the theorem module, and returned OK at e3fe0a6626e: preflight and compilation pass.
The definition-only dependency audit also passed (12 existing definitions; 10 direct
underlying definition dependencies; theorem retained only in proof_deps).

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
