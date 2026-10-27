## Worker report

The item is stated in `Sheaf.Paper.SmoothExchangeScalarCompatibility`, namespace
`WeilConjectures.SmoothExchangeScalarCompatibility`. The new postponed theorem is
`smoothExchangeScalarCompatibility`. The definitions construct the actual three-factor
smooth exchange and both prescribed endpoint scalar comparisons. Nothing is proved in the
new statement module. The natural isomorphism in Conclusion is pinned componentwise to
that constructed exchange, rather than supplied as a hypothesis or chosen as an arbitrary map.

Hypothesis and clause correspondence:

- `D : FiniteFieldDatum` contains p prime, the positive exponent a, the finite field and
  its fixed algebraic closure k. `C : D.CoefficientDatum` contains ell prime, ell different
  from p, and the fixed coefficient algebraic closure. `Field D C` consists of precisely
  its finite Q_ell subextensions; `E L` and `h : E ≤ L` give E contained in L. Equality is
  allowed. `setting D C E` is the existing purity datum at E with bookkeeping level 1;
  rationalIso uses the whole integral system, not just its level-1 reduction.
- The four schemes have `Over (Spec (.of D.k))`. Each structure morphism has
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`. The four arrows are `IsOver`.
  The Cartesian hypothesis is `IsPullback u f' f v`. The relative dimension is `d : ℕ`,
  with `SmoothOfRelativeDimension d f` and `IsSeparated f`. There is no smoothness,
  flatness or properness assumption on v. The dimension and finite-type properties of
  f', and the Noetherian, dimension and invertibility consequences for all schemes,
  are supplied as the existential `TwistedPullbackScalars.Geometry` in the conclusion.
- `RCat D C E W` is the existing raw `sfRationalConstructibleCategory C.l E.val W`.
  These are the framework coordinates used by the published TwistedPullbackSquareScalars
  PBC presentation; there is no Karoubi envelope or change of underlying notion.
- `G D C f S E` is the recorded constructible exceptional functor. S and S' range over
  the published normalized exceptional systems. These are coordinate realizations of
  the specified adjoints; no ambient-adjoint or admissibility assumption is imposed.
- `gamma` is exactly `RationalSmoothPurityCanonical.rationalIso` at the canonical
  compactification and coefficient stage. Its integral map is the finite-trace-normalized
  integral trace transpose, not a free purity orientation. Its source `H` uses the
  existing shifted Tate line as the first tensor input. This is the published source
  presentation of Lf*(-)(d)[2d].
- `middle` pulls that actual tensor back using `canonicalRationalPullbackTensor`, then
  pulls back its shifted line using the existing pullback commShiftIso and
  `CanonicalTate.rationalPull`, then applies `TwistedPullbackScalars.t`. That last map is
  c_(u,f) inverse, the square equality, and c_(f',v), exactly the middle identification
  of the finite smooth exchange after reconstruction and rationalization. The line-first
  presentation merely moves the existing symmetry and shift constraints together with
  gamma; it introduces no exceptional base-change mate or rescaling.
- `exchange` is pullback of inverse gamma, followed by middle, followed by gamma at
  Lv*K. Its endpoints are `A = G_f ⋙ Lu*` and `B = Lv* ⋙ G_f'`.
- `betaA` is the natural-isomorphism composite p_u followed by Lu*_L(b_f).
  `betaB` is b_f' followed by G_f',L(p_v). Here p is exactly the published
  `rationalPullbackScalarComparison`, and b is `RationalScalarComparisonIdentification.b`,
  the counit-normalized field comparison of the same exceptional system.
- `Conclusion` asserts existence of a natural isomorphism e with `(e E).app K` literally
  equal to `exchange ... E K` for EVERY rational K. Its next conjunct is
  `whiskerRight e_E T_X' ≫ betaB = betaA ≫ whiskerLeft T_Y e_L`.
  Evaluating at K gives precisely beta_B ∘ T(Ex_E) = Ex_L ∘ beta_A in the node's
  right-to-left composition convention. It is an equality of natural transformations,
  not just an equality for a chosen lattice or a generic commutative square.
- The last four conjuncts retain the identity-extension UnitEquation, the successive
  extension CompositionEquation for BOTH beta families, and ShiftCompatibility of e
  and both beta families. The unit/associators are the existing scalar unit/alpha;
  the shift structures are composed from the recorded exceptional rightShift, ordinary
  pullback shift, and scalar tShift. Thus all specified coefficient identifications are
  retained explicitly, including the equal-field and shift cases.

Dependency declarations actually used:

- Sheaf.Paper.PurityFiniteSetting: `WeilConjectures.PurityFiniteSetting`.
- Sheaf.Paper.PbcRationalCategory and Sheaf.Paper.TwistedPullbackSquareCoordinates:
  the existing PBC raw rationalization and its published framework-coordinate presentation.
- Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted: `sfRationalTwistingCoefficient`.
- Sheaf.Paper.DerivedPullbackTensorHom: `rationalDerivedPullback`, `rationalDerivedTensor`,
  `rationalPullbackScalarComparison`.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients: the normalized `System`
  and its `fields.rationalComparison`; Sheaf.Paper.RationalScalarComparisonData:
  `RCat`, `H`, `G`, `T`, `b`, `gShift`, `tShift`, `unit`, `alpha`, `UnitEquation`,
  `CompositionEquation`.
- Sheaf.Paper.RationalSmoothPurityCanonical: `rationalIso`.
- Sheaf.Paper.AdicPurityObjects (through the recorded rational comparison imports):
  `purAdicResidueInvertible`, the canonical coefficient inverse already used by H.
  The new definitions use this same instance, with no extra invertibility hypothesis.
- Sheaf.Paper.CompletedPullbackTensorComparison: `canonicalRationalPullbackTensor`.
- Sheaf.Paper.CanonicalTateComparisons: `CanonicalTate.rationalPull`.
- Sheaf.Paper.TwistedPullbackSquareMaps: `TwistedPullbackScalars.t`.
- Sheaf.Paper.TwistedPullbackSquareScalars: the existing `TwistedPullbackScalars.Geometry`
  and `finiteResidueInverse`, recorded by the definition node
  `def-pur-smooth-exchange-geometry` with `existing: true`. The module is publicly
  imported because the statement uses these definitions. Its theorem remains a
  proof dependency, and the item cites the definition owner in stmt_deps.
- Sheaf.Paper.AdicPurityScalarNaturalityData: `Field`, `composeShift`, `ShiftCompatibility`.
- The already stated proof dependencies PbcRationalTransport,
  FiniteSmoothPullbackExchange and upstream Purity.Smooth.Reduction are imported. The
  endpoint lemma currently has no usable recorded Lean module; its complete argument is
  retained by name in the theorem proof docstring and is not replaced by an assumption.

Edge cases inspected: E=L is included via le_rfl and both unit equations; E⊆F⊆L may
have equal stages. d=0 retains the zero shift and zeroth Tate line. The schemes and X'
may be empty; there is no nonempty or positive-dimensional hypothesis. K may be zero;
all components and the equation quantify over every object and every localized arrow.
The square is arbitrary Cartesian and v remains unrestricted. The category/site size
is the existing Scheme.{u}, small pro-etale object u+1/morphism u convention; all
variables and universes are explicitly bound.

Searches, before construction:

- msearch.py leanfinder, "Smooth purity pullback exchange commutes with extension of
  coefficient fields": 8 hits, concerning standard smoothness under base change,
  purely inseparable prime-spectrum maps, and scheme tensor-product pullback facts.
  None states this constructible exceptional scalar equation.
- msearch.py loogle, `"purity", "scalar"`: 0 hits.
- msearch.py grep, `purity.*exchange|exchange.*purity`, AlgebraicGeometry: 0 hits.
- rg of lean/WeilConjectures and lean/Sheaf for the item id and scalar/smooth exchange
  names found no existing declaration of this statement. Upstream smoothPullbackExchange
  is the finite-coefficient map, not this rational scalar compatibility theorem.
  Existing RationalSmoothPurityCanonical.rationalIso_scalar concerns one smooth arrow,
  not the Cartesian-square exchange; its canonical maps are reused.

The current blueprint's coefficient-change proposition (det-sp-purity-coefficient-change,
inside literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport)
was read together with its proof. Its rationalization and finite-field extension clauses
retain the prescribed counit-compatible purity maps. No statement correction is made.
The resolved stage-1 repair note is the already completed re-split; its accepted proof
plan is preserved verbatim in the node, and step-by-step in the theorem docstring.

## Dependency modules

`def-wf-tensor-unit-square-data`: another published import in the statement dependency
closure failed in `WfTensorUnitSquareData.tensor` and `.beta`: generic tensor structure
inference left the universe in EssentiallySmall unresolved. The module is delivered
with `letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _`
installed before those same constructions. The imported integralOperationsSiteSmall
instance otherwise introduces an unconstrained extra universe under max. Its two
local instance-disabling directives are no longer needed and are removed, as are the
module-wide options disabling respectTransparency. No site or coefficient universes are
identified: the small pro-etale site retains objects in u+1 and morphisms in u, with
coefficient modules at u+1. The canonical total comparison, signed tensor, product,
mapping fiber and both unit coordinates stay the original constructions. This is a
lean-only repair of its existing definition node, cited by the item. No mathematical
statement, declaration signature, axiom or sorry is added or changed.

`lem-pur-twisted-pullback-square-scalars`: its current server source still contains
both original definitions. The new definition node reuses them there with existing:true;
this theorem's lean.declarations now lists only Conclusion and the theorem. The
module contains no import of a second defining module. Its only source changes from
the current server are the already validated compile-only transparency adjustments:
normal respectTransparency checks, no local opacity for D, and local implicit
reducibility for the small aliases D, H, U and V. All data, declaration signatures,
docstrings and proof bodies remain verbatim. No new axiom or sorry is introduced.
The theorem node cites the definition owner in stmt_deps; the new definition node
does not depend on the theorem, so the ownership edges remain acyclic.

## New nodes

`def-pur-smooth-exchange-geometry` records the existing declarations
`WeilConjectures.TwistedPullbackScalars.Geometry` and
`WeilConjectures.TwistedPullbackScalars.finiteResidueInverse` in
`Sheaf.Paper.TwistedPullbackSquareScalars`, with `existing: true` and no lean.file.
It gives the notions a definition-node owner; it creates no Lean declaration or
additional module. The item cites this node instead of citing the scalar-square
theorem merely to obtain its geometric data. This follows brief-stage2 section 5's
existing-declaration rule and the latest return's explicit instruction to import
and reuse the existing declarations. SmoothExchangeGeometry.lean is removed from
the packet. There is no alternate name, copy, wrapper type or duplicate proof.

The definition node's statement is a definition package, not an existence assertion.
Its field correspondence is exact: noethX/noethX'/noethY/noethY' are Noetherian schemes;
dimX/dimX'/dimY/dimY' are Fact wrappers around existence of a natural bound on their
topological Krull dimensions; invX/invX'/invY/invY' are Fact wrappers around the
coefficient prime being a unit in every stalk; finiteF and compactF assert locally
finite type and quasi-compactness of f; separatedF', finiteF', compactF', smoothF'
assert precisely separation, locally finite type, quasi-compactness and relative
smooth dimension d for f'. There is no separatedF field and no Cartesian hypothesis.
The consuming theorem supplies the bundle as a conclusion. The empty scheme and d=0
remain allowed. finiteResidueInverse is the existing construction using
coefficientPrime_isUnit_stalk and the residue homomorphism. Its inverse is uniquely
determined; no arbitrary comparison or existence-only choice is used.

The current server source was read with scompile.py --source and compared with the
read clone and the source used for the previous return: all are identical. Both
reused declaration blocks, including their original docstrings, remain in that
module verbatim. The complete source diff consists only of the transparency options
and attributes described above. Searches of all delivery modules find one structure
Geometry and one def finiteResidueInverse, both in the original module. The item
imports that module, and the removed SmoothExchangeGeometry module is not imported
or delivered. The prior repair's physical relocation is withdrawn in favor of the
latest instruction to reuse these existing declarations.

Searches for ownership and an existing bundle: msearch.py leansearch, "Bundle
Noetherian finite dimensional schemes and smooth separated finite type morphism after
base change with invertible coefficient prime", returned eight ordinary smoothness,
separation and finite-type base-change facts. msearch.py leanfinder, "Geometric
hypotheses for smooth purity exchange: four noetherian finite dimensional schemes with
coefficient prime invertible and two finite type morphisms", returned eight facts about
SmoothOfRelativeDimension. Neither provides this bundle. msearch.py grep,
`structure.*Geometry|smooth.*exchange.*geometry` in Mathlib/AlgebraicGeometry, returned
one unrelated RelativeGluing.lean documentation line. Their actual JSON search-log
records are included in the new node. A repository rg for the new notion, Geometry's
qualified name and finiteResidueInverse found only the existing theorem node/module;
no definition owner existed. `blueprint_refs.py search purity geometry` found five
nodes concerning Thom classes, deformation-section geometry and projective bundles;
`search twisted pullback` found seven broader coefficient/twist nodes. None defines
this package, so same_as is empty. The earlier literal-phrase searches each returned
zero. `blueprint_refs.py ancestor` returned prop-pur-rational-purity-trace-coherence.
The current blueprint Step 1 explicitly transports the base-change squares of G12;
this package records their geometric typing data.

## Current-baseline repair by NF

The dispatcher assigned this retained NH repair to NF. The local NH sandbox was
absent; the returned immutable packet 2ed21cfdd88f0982c5398d66ab1d716e06972d37
was recovered read-only from the server object store into the NF sandbox.
The earlier report above records its mathematical interface and prior checks;
those old compile results are historical, not validation of the present packet.

Current server main already has the maintenance ancestry repair on
`def-wf-tensor-unit-square-data`, rooted at `fix-prop-projection-formula`.
All existing node copies have been refreshed from current main, preserving its
review and proof metadata. Only the delivery's Lean records and required definition
ownership dependencies are retained. No statement correction is made.

Current main has split `AffineSpaceZeroSectionPurity` into imports of
`AffineSpaceZeroSectionConstructions` and `CoordinateZeroBaseChange`.
The old repair predates that split and would duplicate the extracted declarations.
Its module and dependency node are therefore omitted; current main supplies them.
The accepted WfTensorUnitSquareData and TwistedPullbackSquareScalars elaboration
repairs remain in the packet. Geometry and finiteResidueInverse are still reused
in their original module with existing:true. No new definition copy is introduced.

The preceding mathematical correspondence was rechecked against the recovered
module and the current blueprint coefficient-change statement and transport proof.
The unrestricted Cartesian square, canonical purity composite, both endpoint
comparisons, natural-transformation equation, and unit/tower/shift clauses remain
unchanged. Fresh compilation and preflight results will be recorded below.

Fresh searches on 2026-10-26 repeated the item leanfinder query (eight smoothness,
pullback, and prime-spectrum hits; no exceptional scalar equation), Loogle
`"purity", "scalar"` (zero hits), and Mathlib AlgebraicGeometry grep
`purity.*exchange|exchange.*purity` (zero hits). The actual responses are retained
in searches.jsonl. Repository searches for the item id and declaration names
again found no existing theorem. The recovered main theorem's signature still
matches lean.statement verbatim.

## Fresh compile diagnosis

The first dry run passed the two dependency modules (TwistedPullbackSquareScalars
9.4 seconds and WfTensorUnitSquareData 10.9 seconds in library mode), but its
main-file sandbox check exceeded 120 seconds and triggered server confirmation.
A separate exact-source probe with only profiler options added passed in 13.9
seconds (sandbox) and 10.7 seconds (library); cumulative elaboration was 1.44
seconds and typeclass inference 3.19 seconds. No individual declaration was slow.
The probe is scratch-only; its profiler options are absent from every delivered
module. This diagnostic does not count as the clean final packet validation.

The original confirmation ended with a server connection timeout while still
checking imported prerequisites, before reaching the target. The ordinary dry-run
command was repeated unchanged under the brief's cut-off-command rule. The
profiler probe established that no slow declaration or mathematical repair was
needed in the main file.

## Final validation

The ordinary `deliver2.py NF lem-pur-smooth-exchange-scalar-compatibility
--no-push` dry run printed OK for commit `2e1a6eba713`: every delivered module
and the existing-declaration probe compiled cleanly, and server preflight passed.
Library times were SmoothExchangeScalarCompatibility 13.1 seconds,
TwistedPullbackSquareScalars 12.9 seconds, and WfTensorUnitSquareData 10.9 seconds.
Sandbox times were respectively 12.8, 11.5 and 15.8 seconds. Both existing
declarations were checked successfully. No profiler setting is in a delivered module.
The final push uses the same Lean files and records, with this validation paragraph
added to the report; the delivery wrapper checks compilation and preflight again.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
