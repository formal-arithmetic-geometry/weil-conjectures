## Worker report

The module `Sheaf.AlgebraicGeometry.FormalChartGeometricRegularity` states
`AlgebraicGeometry.formal_chart_geometric_regularity`. Its sole theorem has proof `sorry`.
All eleven helpers have actual data or are transparent predicates/abbreviations. No
statement correction or dependency-interface repair is needed. This repair adds two
definition ownership nodes for already published constructions. All statement
dependencies now name definition nodes; the former two theorem dependencies were removed.

Source checked: ILO PDF physical page 76, printed page 70, VI 1.6(i)--(ii) and 1.8.
The first gives the two completed presentations and the congruence modulo BOTH chart
monomials and parameters; the second is the log-smooth preservation theorem. The
expanded formal-model-to-geometric-stalk argument is the agent refinement explicitly
identified by this node, not an assertion that all its details are quoted in ILO.
The latest blueprint locality unit was also read; its contracting-correspondence statement
is distinct from this retained ancillary node, as the accepted split report records.

Hypotheses, in the order of the informal statement:

* `W : FineSaturatedLogScheme` includes the locally Noetherian underlying scheme and
  fs log structure. `R Q` are multiplicative notations for the additive monoids;
  `_hR`, `_hQ` are their existing fs predicates. `β` and `_hβ` give the global R-chart.
* `y` is its scheme map to Spec Z[R]; `_hy` identifies every monomial with the
  structural image of the actual chart section. `h` is the chart homomorphism and
  `_hgp` says its canonical group-completion map is bijective.
* `chartScheme y h` is literally `pullback y (toricMap h)`, with `pullback.fst` and
  `pullback.snd` its projections. `N`, `γ`, `_hγ`, `_hγmap` specify the associated
  Q-chart log structure: a chart means logification by the dependency's definition,
  and the last equation ties its structural map to the Q-monomials on this pullback.
  Thus N is not an unrelated log structure or an extra regularity assumption.
* `Ω`, its Field and IsAlgClosed instances, and `z` are the chosen geometric point.
  `baseRing y h z` is A = the affine-neighbourhood strict henselization at z projected
  to W. This is the published upstream `Scheme.strictHenselization` construction;
  the recorded small-diagram `Scheme.strictHenselizationRing` is canonically identified
  with it by `Scheme.smallStrictHenselizationColimitIso` in the imported extension
  module. The former has the published local/nontrivial instances. No extra
  Noetherianity or local-ring hypothesis is imposed on A.
* `baseMap` is its canonical structural map. `alpha` is the ring-valued R-chart
  obtained by composing that structural map with y and applying Spec's fully faithful
  inverse on morphisms. Consequently it is the given structural chart on A, not a
  free choice of map. `Scheme.strictHenselizationEval` is the distinguished closed
  geometric point of A for the same Ω.
* `zA`, `_hzA` and `_hzAclosed` specify exactly the lift to Spec A times_W Z obtained
  from that closed point and z. The two projection equations determine it uniquely.
* `eC` is the affine coordinate identification Spec C with that base change, where
  C is the EXISTING `Algebra.monoidChartTensor alpha h`. Its A-projection `_heCA`
  and Q-projection `_heCQ` fix both tensor inclusions, hence determine this coordinate
  isomorphism uniquely by the fibre product universal property. It is the usual
  affine-tensor base-change identification, which always exists; these binders are
  coordinate notation, not an assumption that the base change has special geometry.
  `tensorRight` constructs its Q-ring map directly as `Algebra.TensorProduct.includeRight`
  with the actual chart-induced algebra structures. It does not use the unowned
  `monoidChartTensorMonomial` helper.
* `q`, its prime instance, and `_hq` set q equal to the prime of `zA ≫ eC.inv`, via
  `Scheme.SpecToEquivOfField`. B is literally `Localization.AtPrime q` throughout.
* G is the EXISTING `ChartResidual.sourceFace alpha`; F is the EXISTING
  `ChartResidual.targetFace alpha h q`. Both use inverse images of the ring units,
  exactly as in the node. S is `Multiplicative (chartSharpMonoid alpha)` and T is
  `ChartResidual.targetSharp alpha h q`, i.e. the Associates quotient of the face
  localization. For integral fs monoids these are precisely R_G/G^gp and Q_F/F^gp,
  as the owning formal-extension/face-data definition nodes explain. `_hface` is h^-1 F=G.
  J is the EXISTING `localizedTensorBoundary alpha h q`, whose span is exactly the
  nonface monomials since F was defined by their invertibility in B.
* `a` is the sharp ring-valued chart on S; `_hasharp` spells out that its unit
  inverse image is the identity. `ε` is the unit character on R^gp. `_hα` is the
  prescribed equality on EVERY element of R_G, using the existing
  `localizedUnitChart` and `unitChartGroupMap`. Together these express the specified
  sharp chart with characteristic identification: the global R-chart identifies
  the log stalk with its logification, the displayed unit twist identifies that
  logification with the one for a, and the sharp unit criterion identifies its
  characteristic with S. No choice of a different characteristic monoid is made.
* `tB` and `_htB` are the same Ω-point lifted to Spec B. Localization's universal
  property makes this lift unique and ensures it exists for the specified prime.
  Thus all subsequent strict henselizations use the SAME geometric residue closure,
  rather than an independently chosen separable closure.
* `mixed : Bool` selects case (a), false, or (b), true. `_hmodel` is the transparent
  `HasCompletion` predicate. Its false branch fixes k to `IsLocalRing.ResidueField A`,
  has finite `n : ℕ`, and identifies the model with Ahat on EVERY S-monomial.
  Its true branch supplies V, `IsCohenRing p V`, the residue-field identification,
  n, theta, the congruence theta-p in `ToricMonoid.completedChartIdeal V S n`,
  and the monomial-compatible quotient equivalence. That boundary ideal includes
  the parameters. `ToricMonoid.Complete` is the EXISTING completion of E[S][t]
  at (m_E, nonzero S-monomials, t). No ordinary power series ring is substituted.

Conclusion, clause by clause:

* `ModelDimensions B T J mixed` keeps ONE witness D for the pair and BOTH dimension
  identities. D is a `Nontrivial` commutative ring with `IsRegularLocalRing` (which
  includes locality and Noetherianity), complete for its maximal ideal.
* In its false branch the ring equivalence is Bhat ≃ D[[T]], with equality of the
  mapped ideal J Bhat and the existing zero-variable completed boundary ideal L.
  In its true branch it is Bhat ≃ D[[T]]/(eta), with the same mapped-ideal equation
  for L in the quotient. The D-algebra equivalence rho reduces modulo L, so the
  two membership assertions say eta-bar belongs to m_D and not m_D^2. The canonical
  constant map determines this D-algebra equivalence uniquely.
* That same predicate asserts regularity of Bhat/J Bhat and
  dim(Bhat)+e = dim(D)+rank(T^gp), dim(Bhat/J Bhat)+e = dim(D), where e is
  `if mixed then 1 else 0`. This addition form is the node's subtraction formula
  without truncated subtraction. All these dimensions are finite for the local
  Noetherian rings in question. `rank T` uses rational tensor product and
  `Module.rank`, followed by `Cardinal.toENat`, the same rank convention as the
  published log-regularity definition; it does not use a possibly misleading finrank.
* The next two conjuncts state `IsRegularRing (B ⧸ J)` and
  `ringKrullDim B = ringKrullDim (B ⧸ J) + rank T`.
* The next conjunct asserts `IsIso` of the EXISTING CANONICAL
  `Scheme.strictHenselizationMap` for the projection Z_A -> Z at zA. The canonical
  map's defining theorem `strictHenselizationMap_over` supplies its equation over Z;
  `_hzA` identifies its target with the strict localization at z.
* The ring equivalence e identifies the ACTUAL ring-valued geometric stalk
  `strictLocalRing Z z` with `Scheme.strictHenselization tB`, i.e. B^sh. Its first
  clause characterizes the comparison on EVERY pointed etale germ: the lift k is
  over Z and carries the distinguished Ω-point to the specified neighbourhood point,
  and the value of e on each germ is pullback along k. Such a pointed lift to an
  etale object over a strictly henselian local scheme is unique (the equalizer is
  open and contains the closed point), so this is a canonical comparison, not an
  arbitrary ring equivalence. The following equations explicitly retain every
  Q-chart monomial and send the nonunit log ideal to `strictIdeal tB J` = J B^sh.
* The characteristic equivalence eT identifies N.characteristic z with the
  prescribed T, and its displayed value on EVERY chart germ is the canonical
  face-localized sharp class. Chart germs generate the characteristic, so this
  specifies the identification, rather than merely asserting unrelated isomorphism.
* The tJ clause specifies the compatible geometric point of Spec(B/J), identifies
  B^sh/J B^sh with `(B/J)^sh`, and records its value on EVERY b in B through the
  canonical quotient and strict-localization maps.
* The next two clauses are regularity of B^sh/J B^sh and the asserted dimension
  identity. The final two are regularity and the dimension equality on the actual
  log stalk, exactly `FineSaturatedLogScheme.IsLogRegular` at the chosen z (the
  dependency defines global log regularity by universal quantification over z).

Dependency declarations used (their signatures and docstrings were read):

* `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogStructure`, `IsChart`, `characteristic`, `characteristicRank`,
  `nonunitIdeal`, the prelog `germ`, `stalkAlpha`, and the pointwise clauses of
  `FineSaturatedLogScheme.IsLogRegular`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`,
  `snd`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
* `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`.
* `WeilConjectures.AlgebraicGeometry.StrictHenselization` and its imported
  `StrictHenselizationExtension`: `Scheme.strictHenselizationRing`,
  `Scheme.strictHenselizationScheme`, and `smallStrictHenselizationColimitIso`.
  The affine-neighbourhood form is `Scheme.strictHenselization` from
  `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`; its local structure,
  evaluation and structural map are in `Sites.StrictHenselizationLocal`.
* `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, used in rank and
  inside the published algebra tensor construction, not redefined here.
* `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
* `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`;
  the ring structures come from the imported Algebra module.
* `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`.
* `Sheaf.AlgebraicGeometry.IsRegularScheme` retains the recorded regularity
  dependency; the ring clauses use its recorded Mathlib matches
  `IsRegularLocalRing` and `IsRegularRing` in `RegularLocalRing.Defs`.
* `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, also inherited by the
  regular-local class on D.
* `def-per-formal-monoid-extension-data`, module
  `Sheaf.RingTheory.FormalMonoidExtensionModel`: `monoidChartTensor`,
  `monoidChartTensorBase`, `chartSharpMonoid`, `localizedUnitChart`,
  `unitChartGroupMap`, `localizedTensorMonomial`, `localizedTensorBoundary`.
* `def-trf-complete-toric-model`, module `Sheaf.RingTheory.CompleteToricModel`:
  `ToricMonoid.Complete` and `ToricMonoid.completedChartIdeal`. These are exact
  transparent aliases for the formerly theorem-owned completed model and ideal.
* `def-trf-log-regular-pair`, module `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `strictLocalRing`, `strictLocalGerm`, `IsFineSaturatedMonoid`, cited directly.
* `def-trf-chart-unit-face-data`, module
  `Sheaf.TraceFormula.ChartFaceResidualUnitDecomposition`: `groupMap`,
  `sourceFace`, `targetFace`, `targetSharp`, and `sharpMap`.
* `def-trf-strict-henselization-canonical-map`, module
  `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`:
  `Scheme.strictHenselizationMap`, with its structural and point normalizations.

All recorded proof-dependency modules are imported without `public`, except modules
also needed by the statement, which are public. The unrecorded proof dependency
`lem-trf-chart-face-localization-logification` has no module to import and is omitted;
its proof obligation remains in this theorem's complete eight-step docstring. The
Mathlib proof leaves use FiniteType, Localization.Submodule and LocalRing.Quotient.
No new proof dependency is needed merely to state a theorem with `sorry`.

Edge cases checked against the statement before writing: n=0 is allowed in both
input branches. R, Q, S or T may be trivial; the boundary ideal may be zero.
Units and torsion in the original fs monoids are retained by group completion and
face localization. T-rank need not equal S-rank: residual unit factors are not
silently removed. A, B and D are nonzero because of the chosen geometric point,
prime localization, and explicit D witness respectively. An empty W or Z has no
chosen geometric point, so the pointwise theorem is vacuous there. The mixed
parameter condition excludes dim D=0 by its own source hypothesis; no characteristic
case is excluded artificially. No scheme properness, smoothness, excellence, log
regularity of W, freeness of R or Q, or equicharacteristic assumption was added.
All objects and monoids are in universe u; finite-generation lets arbitrary fs
charts be represented in that universe. No independent smaller test universe or
forced object/morphism-universe equality is present.

Searches made on 2026-10-24:

* msearch leanfinder: `Formal toric chart models imply logarithmic regularity at
  geometric stalks using completion and strict henselization`: 8 hits, including
  `instIsPreimmersionFromSpecStalk` and ordinary smoothness criteria; no match.
* msearch loogle: `"LogRegular"`: 0 hits.
* msearch grep: `LogRegular|FormalMonoid|formalMonoid`: 0 Mathlib hits.
* msearch leansearch: `Formal monoid chart completion regularity geometric strict
  henselization`: 8 uniform-space-completion hits; none concerns log chart models.
* rg of `lean/WeilConjectures` and `lean/Sheaf` for `FormalMonoid|formalMonoid|formal_chart|
  GeometricRegularity|ChartFace|sharpification|ResidualUnit` found the published
  extension-model, dimension, residual-unit and log-regularity modules read above.
  None states this full pointwise formal-model/geometric-stalk comparison. In
  particular `exists_completed_chart_of_logRegularAt` goes in the reverse direction
  and `EtaleLogHom.isLogRegular_of_isLogSmooth` has a log-regular target hypothesis.
* Searches of `WeilConjectures` and `Sheaf` for this node id found no declaration;
  `dag/lean_names_upstream.json` likewise has no attachment for the item. The
  published CompactObject example is withdrawn; its node's record was read as
  required, and current module/header conventions were taken from live modules.

Validation of this repaired version: `scompile.py` accepted both the sandbox and
final library module names with no errors or warnings (21.3 s and 15.6 s).
`deliver2.py --no-push` passed server preflight and compilation, printing
`OK (dry run)` for commit 320a7d63d60. The only postponed proof remains the
item theorem. The final delivery reruns these checks after this report update.

## Second reading by Q32

I reopened the node and the completed file for a separate second pass. This is a
self-reading: this dispatch explicitly prohibits starting other agents; no independent
worker is being claimed. The maintainer's independent review remains the delivery gate.

The pass checked the following potential mismatches individually: W is fs and locally
Noetherian through its bundled data; both global charts and both scheme monomial maps
are tied to actual sections; h is a group isomorphism without a free-monoid restriction;
A is the same pointed strict henselization through the upstream canonical colimit
comparison; zA is the distinguished closed-point lift; q is its precise tensor-coordinate
prime; B, F, G, S, T, J are the published constructions; h^-1 F=G is explicit; a and
epsilon satisfy the equality on all R_G; the two completion cases retain finite n,
residue field k, Cohen uniformizer p and theta-p modulo chart monomials AND t.
The single D witness in ModelDimensions belongs to the pair and both formulas, has
regular-local Noetherian structure and completeness, and its parameter is reduced
through a D-algebra equivalence. The arithmetic uses addition of e, so no truncated
subtraction changes the mixed case. The regular B/J, canonical IsIso over Z, e on
stalks, eT on characteristic, mapped ideal, quotient strict henselization, regular
geometric stratum, dimension and final pointwise log-regularity clauses are all present.

The concrete issue found in this pass was that merely fixing e on chart monomials would
not characterize its action on all coefficient germs. I added the full pointed-etale-germ
clause with both over-Z and Ω-point equations. This makes e the canonical comparison on
all sections. The server compiler then accepted the full file with no warnings. No
remaining mathematical mismatch or disputed statement was found. The repair second reading below additionally checks both new definition ownership nodes.


## Returned-delivery repair

The immutable returned head is e5ca95d5a2e4. The live item still has the original
accepted informal statement and no Lean record; the sandbox retains that delivery.
This repair preserves its theorem signature and all H3-accepted mathematical clauses.
The server delivery wrapper rebases the reviewed sandbox work onto the current live head.

1. Added `def-trf-chart-unit-face-data`, owning exactly
   `Algebra.ChartResidual.groupMap`, `sourceFace`, `targetFace`, `targetSharp`,
   `sharpMap` in the existing published module. The item cites this definition node.
   No second copy of a notion or declaration is introduced.
2. Added the landed definition `def-per-formal-monoid-extension-data` to the item.
   Its owned tensor, base, sharpening, unit-localization/group and localized
   tensor monomial/boundary definitions cover every occurrence. Replaced the body
   of `tensorRight` by `Algebra.TensorProduct.includeRight` with the two actual
   chart-induced algebra structures; `monoidChartTensorMonomial` is no longer used.
3. Used the already landed definition owner `def-trf-complete-toric-model` rather
   than creating a duplicate completed model. `HasCompletion` and `ModelDimensions`
   now use its transparent aliases `ToricMonoid.Complete` and
   `ToricMonoid.completedChartIdeal`. Their bodies are definitionally the original
   `AddMonoidAlgebra.CompletedLocalModel` and
   `AddMonoidAlgebra.completedLocalModelBoundaryIdeal`. Thus the exact completion
   and boundary ideal already have a definition owner, cited directly here.
4. Added `def-trf-strict-henselization-canonical-map`, owning the existing
   `Scheme.strictHenselizationMap`. Its definition chooses a uniquely determined
   witness, characterized by BOTH the structural square and the geometric-point
   equation, as recorded in the new definition statement. No arbitrary map is used.
5. Added `def-trf-log-regular-pair` directly for `strictLocalRing`, `strictLocalGerm`
   and `IsFineSaturatedMonoid`. Removed
   `lem-trf-chart-face-residual-unit-decomposition` and
   `lem-trf-formal-monoid-extension-model` from `stmt_deps`; their conclusions were
   never used in the signature. Original proof dependencies remain unchanged.

The five repairs change dependency provenance and a transparent tensor construction;
they do not change the mathematical statement, hypotheses, or conclusions. No
`statement_change` is needed and no disputed statement was found.

## New nodes

`def-trf-chart-unit-face-data` supplies a definition owner for the unit inverse
images G and F, the localized target sharpening T, the quotient map from Q and
h's induced group-completion map. Its source is ILO VIII 3.1.1--3.1.2, printed
pp. 98--99, the notation used by the chart refinement. These constructions already
exist in `Sheaf.TraceFormula.ChartFaceResidualUnitDecomposition`; the record uses
`existing: true` and lists the five definitions. Searching DAG definition records
found no owner; blueprint_refs search `residual face` found none. Mathlib LeanSearch,
Loogle and grep returned localization and unit lemmas, no whole construction.
The exact raw search results are in the new node's `mathlib_searches`. Project
searches found the reused declarations, avoiding private copies.

`def-trf-strict-henselization-canonical-map` supplies a definition owner for the
unique pointed strict-henselization map over a scheme morphism. Sources: Stacks
04HX and 04GU. Its two equations fix both the structural and geometric-point
normalizations, and its recorded existing signature is verbatim. Searching all
DAG definition records found no owner; blueprint_refs `strict henselization morphism`
returned related statements but no definition of this canonical pointed map.
LeanFinder returned ordinary residue-field maps; LeanSearch returned localization
lemmas; Mathlib grep had no matches. Both project source trees were searched;
the exact existing construction was found in the Sheaf module. The new record
uses it without changing the published module or importing a theorem conclusion
as a statement dependency.

Both new nodes have no proof, introduce no theorem or sorry, and have explicit
source, search, creation and blueprint-lineage records. Their statements cite
exactly their recorded definition dependencies. No new Lean file is needed for
these already published declarations, as allowed by brief-stage2 section 5.

## Repair second reading by Q32

I reread both new records and the existing declarations with their full signatures,
docstrings and bodies. This is the authorized self-reading (the dispatcher prohibits
subagents); the maintainer independently reviews the delivery. The face node
states only the five data constructions, without adding the residual-unit theorem.
The canonical-map node records the two equations of the unique witness and does
not confuse it with an arbitrary map, the affine structural morphism, or an IsIso.
The complete-model aliases have exactly the same underlying definitions, including
parameters in the boundary ideal. The direct tensor inclusion is the same canonical
Q-ring map. The main theorem signature remains verbatim identical to the returned
version, and every H3-accepted clause listed earlier is retained. The n=0, trivial-T
and both completion-case edge checks still apply. No remaining mismatch was found.
