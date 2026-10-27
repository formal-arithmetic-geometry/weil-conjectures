## Worker report

Q38 states `lem-sf-tensor-hom-signed-transposes` in
`Sheaf.SixFunctors.TensorHomSignedTransposes`, with principal declaration
`WeilConjectures.TensorHomSignedTransposes.signed_transposes`.
Every helper is listed in `lean.declarations`. Definitions have actual data;
there is one postponed theorem, whose docstring gives all eight proof steps.
The node statement, proof and mathematical constructions are unchanged.
The ten presentation records are real definitions moved into an independent
definition module. The complete Verdier data interface has an independent module
as a section 1(B) dependency repair. Neither imports the quarantined theorem
modules; the item imports these source definitions.
The returned-delivery repair adds definition ownership and statement dependencies
as detailed below.

The source read was the current
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.md`
and its `.proof.md`, especially the displayed five-arrow chain and shift clause.
The DAG item's eight-step expansion supplies the more explicit signs and squares.
The ten presentation records have been moved from the quarantined parent
source into the owning definition module. Only the records and definitions are used: neither its exchange theorem
nor `Package` nor `CorePackage` is invoked or assumed. In particular no downstream
exchange compatibility theorem is used as a premise. Reusing a presentation record
introduces no theorem assumption from the module that contains it.

### Hypotheses, objects and the five arrows

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite-field datum is `D`, with
  `hl : l ≠ D.p`; `Ω` is an algebraic closure of `Padic l` used by the existing
  coefficient-indexed operation system. This closure is bookkeeping for the
  published categories, not an additional condition on the coefficient field.
- `X,Y : Scheme.{u}` carry the recorded `Over (Spec (.of D.k))` instances.
  `LocallyOfFiniteType` and `QuasiCompact` on their structural maps say they are
  finite-type schemes over this field. The named `f : X ⟶ Y` is over that base,
  separated, locally of finite type and quasi-compact.
- `S : ConstructibleExceptionalCoefficients.System l Ω D hl (f := f)` supplies
  the specified constructible adjunctions. `c : Compactification f` is the
  existing auxiliary compactification used to define the actual projection.
  The operation is precisely `S.ring.operation c (s.stage l)`.
  The fixed six-functor conventions are realized by these existing canonical
  operations and their inclusions; no new six-functor or exceptional functor is
  defined in this delivery.
- `s : RingStage l` has exactly the finite and integral constructors. Finite
  coefficients have a finite extension `E` and positive level `n : ℕ+`;
  integral coefficients have its coefficient integers. Rational and closed
  stages cannot occur in this theorem.
- `admissible : Admissible l Ω D f c (s.stage l)` is the existing exact
  specialization of exceptional admissibility to the selected coefficient stage.
  Its finite/integral cases use the dependency's recorded admissibility predicates.
- `d : Model ...` is the hypothesis that the full-domain adjunction/projection
  bijections in the statement are supplied. Its Hom bifunctors, closed
  adjunctions, `pull`, `star` and projection isomorphisms range over all the
  published finite-Tor constructible categories, not a smaller testing domain.
- `r : RingModel l Ω f s d` identifies the supplied Hom and tensor operations
  with their actual ringed derived operations and signed evaluation, and
  identifies `d.pull ⊣ d.star` with the actual derived adjunction. It is the
  meaning of using those operations, not an extra exactness or shift assumption.
- `p : Projection ... r (S.ring.left c s)` pins the projection to the actual
  counit/open compactification transformation. In particular its `projectionMap`
  and `normalized` fields forbid substituting an arbitrary invertible map.
- `integral : IntegralRealization l Ω d` is `True` at finite coefficients. At
  integral coefficients it identifies both closed adjunctions with the existing
  `podIntegralClosed` partial closed structures. Those structures are normalized
  by ordinary signed internal-Hom evaluation precomposed with the actual
  `podCompletedTensorUnit`. This expresses the node's use of completed tensor
  and ordinary internal Hom into a complete target.
- `M : C l Ω X (s.stage l)` and `N,L : C l Ω Y (s.stage l)` are universally
  quantified in `HomSquares`. `C` is exactly the recorded full category of
  bounded constructible objects with finite Tor dimension. The existing
  `Model.left` is `A = star(Hom(M,G N))`; `Model.right` is `B = Hom(F M,N)`.

`fiveTransposes` is the following actual composite of equivalences:

1. `(d.closedY.transpose L (F.F.obj M) N).symm` uncarries a map from `L` to `B`.
2. `Iso.homCongr (d.projection L M).symm (Iso.refl N)` precomposes with
   `d.projection L M`. By `Projection.normalized`, this is the inverse of the
   actual projection, conjugated by the two signed symmetries.
3. `F.adjunction.homEquiv` is the specified exceptional adjunction.
4. `d.closedX.transpose` curries with the specified signed evaluation.
5. `d.adjunction.homEquiv` is the specified ordinary pull/direct-image adjunction.

The library's closed adjunction uses evaluation order `L ⊗ M`; the node displays
`M ⊗ L`. This is the existing `Model` convention. The two Koszul braidings in
`Projection.normalized` convert the latter chain to the former chain exactly.
No unsigned flip or independently chosen Hom-set equivalence is substituted.

### Every conclusion clause

- `∃ shifts : Conclusion l Ω d` supplies the Hom shift structures and ordinary
  direct-image shift. This is an output, never a hypothesis. Its exchange is
  normalized by the same five-arrow map applied to identity; naturality of the
  given five adjunctions makes this an equivalent representable packaging.
- `Nonempty (RingShifts l Ω r shifts)` pins source-Hom shifts to
  `VerdierExchange.DualShiftModel` and its explicit signed Hom-complex component
  formula. It pins target-Hom shifts to `RingedHomUniverses.homCommShift`, the
  existing unsigned target comparison, and `star` to the actual derived
  pushforward shift. Thus neither Hom shift is a freely chosen endpoint iso.
- `Nonempty (AdjointShifts l Ω d r shifts)` provides the actual pullback shift,
  its normalization under `r.pull`, and `d.adjunction.CommShift ℤ` for the
  ordinary adjunction. The `exceptional` field records the unit equation for
  `F.adjunction` and its existing shifts. The counit follows from the same
  standard adjunction compatibility, and `Operation` already records both unit
  and counit compatibility. These conditions uniquely make the right shift the
  transpose of the left one.
- `targetA` composes the shifts of `F.G`, the unsigned target-Hom functor and
  `d.star`. It is exactly `A(M,N[r]) ≅ A(M,N)[r]`.
  `targetB` is exactly `B(M,N[r]) ≅ B(M,N)[r]`.
- `negativeShift` uses `shiftFunctorOpIso A (-r) r (neg_add_cancel r)` and the
  contravariant functor's shift. Consequently `sourceA` and `sourceB` are
  exactly `A(M[r],N) ≅ A(M,N)[-r]` and its `B` counterpart. The shift on the
  opposite category is Mathlib's negative opposite shift, opened explicitly.
- `shiftHom` composes `Iso.homCongr` with the inverse Hom equivalence of
  `shiftEquiv' ... .toAdjunction`. Thus it moves `[r]` in the output to `[-r]`
  on the test object, and `[-r]` to `[r]`, using the actual shift adjunction.
- `HomSquares` first asserts equality of the functions
  `shiftHom(targetA) ∘ fiveTransposes(M,N[r],L)` and
  `fiveTransposes(M,N,L[-r]) ∘ shiftHom(targetB)`.
  Its second equality is
  `shiftHom(sourceA) ∘ fiveTransposes(M[r],N,L)` equals
  `fiveTransposes(M,N,L[r]) ∘ shiftHom(sourceB)`.
  These are whole Hom-set functions, not just identities on a selected morphism.
- `ActualProjectionShifts` supplies separately normalized tensor shifts on `X`,
  the compactifying scheme, and `Y`. `TensorShiftNormalization` fixes each
  comparison on every flat K-flat pair using the published representative
  comparison, localization shift, and actual cochain `mapBifunctorShift₁Iso`
  and `mapBifunctorShift₂Iso`. The second has the Koszul coefficient, the first
  is unsigned. No map-shift compatibility is assumed in this normalization.
- Its `beta` field states `BetaSquares` for the actual
  `Data.tensorPullback` followed by tensor of the actual proper counit and
  identity. Its `proper` field states `ProjectionSquares` for the actual
  `Adj.rightAdjointProjectionMap Data.tensorPullback.hom`.
  Both predicates contain two explicit equations: shifting the first input,
  and shifting the second. The direct-image shift in them is defined by
  `Adj.rightAdjointCommShift ℤ`, so it cannot be independently rescaled.
- Its `compact` field applies those two squares to the actual
  `PurCompactSupport.projectionMap`, whose definition is the proper mate pasted
  with the canonical open projection and the geometric pullback compositor.
  This is not a mere claim that some projection is shift-compatible.
- For an integral stage, the final conjunct supplies `IntegralCompletionShifts`
  for both `X` and `Y`. The quantified residue-invertibility instances merely
  make the existing integral interface available; over the given finite field
  they are canonical consequences of `hl`, not extra geometric hypotheses.
  The data uses the literal ordinary tensor of `pullbackTensorCalculus` and
  normalizes its shifts on K-flat representatives. Its `left` and `right`
  fields are both actual `podCompletedTensorUnit` squares against the existing
  `tensorShifts.integralLeft` and `tensorShifts.integralRight`. Those comparisons
  contain the strict tower and signed Roos formula in their definitions.
  `reductionLimit : PurReductionLimitShiftData` retains the actual reduction,
  finite evaluation, K-injective limit, signed Roos triangles, and unit/counit
  shift equations. No exactness of arbitrary products or equality-detection
  by independent finite reductions is asserted.

### Dependency declarations read and used

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, its finite
  tensor/Hom/Tor domain conventions; reexported through the existing model.
- `Sheaf.Paper.ExceptionalAdjointAdmissibility`:
  `IsExceptionalAdjointAdmissibleAtFiniteStage` and the integral predicate,
  used in the existing `TensorAdjunctionExchange.Admissible` specialization.
- Mathlib `CategoryTheory.Pretriangulated`, `HasShift`, `shiftEquiv'`,
  `shiftFunctorOpIso`, and `Adjunction.rightAdjointCommShift`.
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`: the specified derived
  ordinary/exceptional adjunction conventions; the constructible versions used
  here are `ConstructibleExceptionalCoefficients.Operation.adjunction` and
  `Model.adjunction`, with their actual realization equations.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData`;
  used by the actual `PurCompactSupport.projectionMap` definition, not copied.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: actual completed tensor
  construction and its global comparison. The statement uses its established
  global `integralCompletedTensor` presentation, as do the shift dependencies.
- `Sheaf.SixFunctors.TensorHomTranspositionData`: `Model`, `Model.left`, `Model.right`,
  `RingModel`, `Projection`, `PartialRealization`, `Conclusion`, `RingShifts`,
  `Admissible`. All these signatures and normalization fields were read.
- `Sheaf.SixFunctors.VerdierExchangeData`: `ringHom`, `ringInclusionShift`,
  `DualShiftModel`, `ProjectionTensor.toModel`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`:
  `RingedHomUniverses.hom`, `homCommShift`, `sourceShift`, `LeftFormula`,
  `RightFormula`; the same independent site universes are retained.
- `Sheaf.Paper.IntegralCompactSupportCoefficientData`:
  `PurCompactSupport.pull`, `push`, `projectionComparisons_existsUnique`,
  `projectionOpenFactor`, `projectionMap` and their full normalization equations.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `podCompletedTensorUnit`,
  `podIntegralClosed` and its ordinary-to-completed transpose normalization.
- `Sheaf.SixFunctors.IntegralOperationShiftData`:
  `IntegralSystemRealization.tensorShifts`, its two integral comparisons and
  their finite-level/Roos normalization fields.
- `Sheaf.Paper.PurReductionLimitShiftAdjunction`: `PurReductionLimitShiftData`,
  especially its resolution, signed Roos, unit and counit fields.

The remaining imports are the node's recorded proof dependencies, for the eight
steps in the theorem docstring. They are plain imports; modules supplying types
in the signature are public imports. No prerequisite theorem was restated.

### Edge cases and searches

Checked the zero shift, negative shifts and double negation explicitly in the
sign and source/test-object formulas. At `r=0` the actual canonical shift
comparisons produce identity squares. Zero objects and zero test morphisms are
included in the universally quantified Hom sets. Both finite and integral stages
are retained, with level zero excluded only by the existing positive coefficient
level convention. Site universes are object universe `u+1`, morphism universe
`u`; no extra equality of these universes is imposed. All category and coefficient
universes and implicit variables are explicitly bound; auto implicits are off.

Searches actually run:

- `msearch.py ... leanfinder` with query
  `Signed shift compatibility of the five tensor Hom adjunction transpositions with the actual projection formula and completed tensor`:
  eight generic hits including rigid tensor/Hom equivalences and
  `MonoidalClosed.compTranspose`; none states the geometric normalized chain.
- `msearch.py ... loogle` with query
  `CategoryTheory.tensorLeftHomEquiv, CategoryTheory.Adjunction.commShiftIso`:
  no result; the latter anticipated name is not the API name in this Mathlib.
- `msearch.py ... grep` with query
  `tensorLeftHomEquiv|tensorRightHomEquiv|shift_counit_app` in CategoryTheory:
  seven generic results, no exact statement of the item.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id, signed
  transposes, tensor-Hom, projection, Hom shift and completion-unit names:
  found the parent presentation and the normalization modules listed above.
  None already states the full pair of Hom-set equations plus both actual
  projection-input and completion-unit squares. One exploratory unescaped
  regular expression failed; it was not treated as a negative search result.
- Targeted `rg` searches and full signature reads in Mathlib's shift,
  adjunction and triangulated-opposite modules identified `shiftEquiv'`,
  `shiftFunctorOpIso` and `rightAdjointCommShift` for the canonical comparisons.

The helper definitions in the item module spell out its maps, normalization
predicates and conclusion fields. The repair supplies three definition nodes
reusing already published definitions, and cites all omitted definition owners;
there are no new mathematical constructions. The Verdier definition interface
has a section 1(B) dependency module repair.
The transposition owner has its own source module of real definitions. The
Verdier definition dependency is repaired in its own source module.

## Second reading by Q38

The dispatcher explicitly forbids starting another agent, and there is no lead.
This is therefore a fresh self-review with the node, source and complete module
open; it is not represented as a second person's review.

I checked each hypothesis and clause against the mapping above. The review found
that the library's tensor-Hom adjunction orders the test object first; the
existing `Projection.normalized` already inserts both signed braidings, so the
five equivalences must use that presentation rather than an unsigned permutation.
I used those exact equivalences and recorded the reason above. I also separated
ordinary integral tensor from completed tensor: the latter's transpose is pinned
by `IntegralRealization`, and both actual completion-unit squares are explicit
conclusions. Finally, the source comparison uses `shiftFunctorOpIso` rather than
identifying the two opposite shifts by definitional reduction. This preserves
negative shifts and yields exactly `L[r]` in the second Hom equation.

The hypotheses contain no `CommShift` assertion about exchange or projection.
`Conclusion`, `RingShifts`, `AdjointShifts`, `ActualProjectionShifts` and
`IntegralCompletionShifts` are all on the conclusion side. The actual proper
counit composite, its adjoint, the compactification paste, both Hom variables and
both completion-unit inputs were all checked separately. The mathematical
statement is not disputed or corrected. The returned review correctly identified
missing definition ownership and DAG citations, repaired below.

The module compiled cleanly through `scompile.py` in both its sandbox and library
module presentations. Delivery preflight and its per-file compile are run after
this report and node record are written.


## Returned-delivery repair: c2041a3b2c0d, H10

The H10 diagnosis is accepted. The previous compilation had loaded cached
artifacts for quarantined `Sheaf.Paper.TensorAdjunctionExchange` and
`Sheaf.Paper.VerdierExchange`; it did not establish that those modules could
be built from current sources. The previous public-abbreviation repair was
therefore insufficient. This delivery removes that dependency at the source.

I read `coord/rework.tsv` entries 2417 and 2510, `coord/queue.md`, the complete
quarantined sources, and `coord/build-errors/Sheaf.Paper.VerdierExchange.txt`.
The root error is a heartbeat timeout in the old `RingRealization` signature,
followed by unknown declarations. The extracted definition interface compiles
with the existing default options and no heartbeat increase.

`Sheaf.SixFunctors.TensorHomTranspositionData` now contains the ten actual
records and constructions, with their original public names under
`WeilConjectures.TensorAdjunctionExchange`: `Model`, `Model.left`, `Model.right`,
`Model.inverseComponent`, `Conclusion`, `PartialRealization`, `RingModel`,
`Projection`, `RingShifts`, `Admissible`. They were moved from the readable
quarantined source, rather than reconstructed from printed types. Their data,
instance fields, implicit arguments, signed normalizations and universes are
unchanged. The module imports the independently extracted Verdier data and
ordinary dependencies. It imports no exchange theorem or parent package.

The item now opens `TensorAdjunctionExchange`, as its original implementation
did, and uses these real definitions from the owning module. The node's theorem
signature remains verbatim identical to its prior delivered signature. The
explicit `Model.left l Ω d` / `Model.right l Ω d` calls are the same constructions.
Both Hom equations, the fixed braidings, the actual inverse projection,
completion-unit squares, negative shifts and all universes remain as reviewed.
The principal theorem is the only delivered `sorry`; both definition modules
contain zero `sorry`s and assert no existence theorem.

The complete `def-sf-verdier-exchange-data` interface is repaired under section
1(B), as detailed below. A source-only import traversal from the delivered item,
including transitive proof imports, found no path to either quarantined exchange
module and zero missing `Sheaf.*` source files. This addresses source rebuilding,
in addition to checking individual imports against published artifacts.

The original public names are deliberately retained so the quarantined parent
can import the new definition module when its rework resumes; it must remove its
old copies instead of redeclaring them. A scratch consumer uses the complete
parent source with exactly that import change and the ten definitions removed.
This tests that the parent can consume the moved interface without an import
cycle. The quarantined parent theorem is not part of this delivery, is not a
premise of this item, and its downstream node record is not modified.

The previous F1/F2 repairs remain: all three new definition owners and the eleven
existing owners requested by the maintainer are present in `stmt_deps`. The
parent theorem node is absent, preserving the acyclic statement dependencies.
The item JSON differs from current main only in `lean` and additions to
`stmt_deps`; its statement, proof and other fields are unchanged. The dependency
node changes only in `lean` with the section 1(B) reason. The delivery wrapper
rebases the packet on the live branch.

## New nodes

`def-sf-tensor-hom-transposition-data` owns the ten real definitions in
`Sheaf.SixFunctors.TensorHomTranspositionData`, retaining the original
`WeilConjectures.TensorAdjunctionExchange` namespace. Its statement and
hypothesis/clause mapping are unchanged from the accepted F1 ownership repair:
`Model` supplies closed Hom structures, pull/star adjunction and projection;
`left` and `right` are the two bifunctors; `inverseComponent` is the transpose
of the identity; `Conclusion` supplies normalized exchange/shift data;
`PartialRealization` preserves the allowed pairs and evaluation;
`RingModel` fixes actual ringed operations and evaluations; `Projection` pins
the actual proper/open map and both signed braidings; `RingShifts` pins signed
source, unsigned target and direct-image shifts; `Admissible` is the existing
stage specialization. Source: current blueprint `fix-lem-tensor-adjunction`,
five-arrow construction and shift clause. None asserts that a model or conclusion
exists. The zero object, every integer shift, the positive finite stages and the
integral stage remain included with the original site/coefficient universes.

`def-sf-integral-completion-transpose` still records the existing
`WeilConjectures.podCompletedTensorUnit` and `podIntegralClosed` in
`Sheaf.Paper.DerivedAutomorphismHomEvaluation`. The first is the reduction/limit
unit followed by the tensor comparison and inverse Roos realization. The second
is uniquely characterized by ordinary transposition after precomposition with
that unit, on every permitted internal-Hom pair. Source: the same integral
five-arrow normalization, Stacks 099B and 0A0E. It adds no perfectness assumption,
new map or arbitrary choice. The prime, finite extension, scheme and residue
invertibility match the source section variables. The zero map is retained.

`def-sf-integral-finite-tor-inclusion` still records
`WeilConjectures.PurCompactSupport.finiteTorIntegralInclusion` in
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`. It is the literal
full-subcategory inclusion, `obj M := ⟨M.obj, M.property.1⟩` and
`map v := ObjectProperty.homMk v.hom`. It forgets only the uniform Tor witness,
with no extra hypothesis or claim that all constructible objects have finite
Tor amplitude. Source: the integral finite-Tor domain of the five-arrow chain.

The original three-kind searches are preserved verbatim in each new node's
`mathlib_searches` and in `searches.jsonl`. LeanSearch and LeanFinder found generic
adjunction, completion and full-subcategory declarations, not these specialized
interfaces. The common Mathlib grep query
`TensorAdjunctionExchange|PartialRealization|RingShifts|podCompletedTensorUnit|podIntegralClosed|finiteTorIntegralInclusion`
returned zero results; `rg` in `lean/WeilConjectures` found none. DAG and Sheaf
searches located the existing constructions, then recorded only under theorem
owners. Blueprint searches for `transposition`, `completion unit`, `finite Tor
inclusion`, `five`, `tensor-adjunction` and `completed tensor` found related
nodes and the parent, not another owner. No new notion was duplicated: two nodes
reuse existing definitions, while the transposition definitions have been moved
out of the unavailable parent as explicitly requested by this H10 return.

## Dependency modules

`def-sf-verdier-exchange-data`: its recorded module
`Sheaf.Paper.VerdierExchange` is quarantined and cannot supply a rebuildable
interface. The replacement module `Sheaf.SixFunctors.VerdierExchangeData` contains
the complete definition node's constructions, under the original
`WeilConjectures.VerdierExchange` names. The dependency node's statement, source,
DAG edges and every other field are unchanged; only its `lean` record is repaired.

The module includes the adjoint compositor; ambient ring Hom and actual unit;
restricted duals, substitution and exchange; stage data, duals, canonical epsilon;
ring realization and stage conclusion; raw dual, fixed K-injective target, signed
Hom comparison, dual-shift model and inclusion shift; ring shift realization;
stage scalar data, kappa maps and evaluation-transposed dual scalar maps;
counit-normalized star scalar map, scalar equation and shift data; K-flat tensor
representative normalization and its projection model; actual ring projection;
coefficient-unit restriction and scalar arrows; and the normalized integral
compact-support compositor. Every listed clause in the dependency statement is
therefore retained. It contains no all-stage `Package`, `Assertion`, or
`verdier_exchange` theorem, and imports none of their proof-only dependencies.

Every construction body and record field is taken from the inspected quarantined
source. The small-site instance was made public, with the same value
`essentiallySmallSelf`, because it occurs in the public K-flat normalization
signature; it is named in `lean.declarations`. This changes no universe or
mathematical assumption. The first-Hom shift still uses the signed complex
comparison `(-1)^(m*q)`, and the projection and scalar arrows retain all canonical
normalizations. No missing condition is replaced by an arbitrary map or a merely
existential choice. The sources and searches are those of the existing definition
node; this is an interface relocation, not a new DAG notion.

The H11 advisory remains an openly declared self-review: no independent worker
was claimed. I reread the real extracted records and the item together. The
natural-language statements and every mathematical equation are unchanged from
the independently accepted substance. No statement correction was required.


Validation of the final source extraction: the prescribed `scompile.py` compiled
`VerdierExchangeData`, `TensorHomTranspositionData` and `TensorHomSignedTransposes`
separately in dependency order, in both sandbox and module presentations, with no
errors or warnings. It also compiled the scratch full parent consumer with its
new import and removed duplicate records, both presentations, with no errors or
warnings. No timeout limit or heartbeat budget was raised. The delivered files
contain no diagnostic commands; the probe remains only in the sandbox scratchpad.
The wrapper dry run and final delivery follow these checks.
