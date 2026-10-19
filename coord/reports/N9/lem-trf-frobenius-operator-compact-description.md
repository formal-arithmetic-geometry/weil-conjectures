## Worker report

The item is stated in `Sheaf.Paper.FrobeniusOperatorCompactDescription`, declaration
`WeilConjectures.TraceFormulaCoefficientConventions.frobenius_operator_compact_description`.
It is a statement on the ordinary compact-support coefficient complex itself, with one
postponed proof. Its helper constructs the direct power transport separately from the
repeated transport used to define the operator. No statement correction is made.

Hypotheses and clauses:

- The global finite-field datum and coefficient conventions are the single binder
  `T : TraceFormulaCoefficientConventions.{u}`. Its fields retain prime p, a >= 1,
  q = p^a, k0 of cardinality q, its algebraic closure k, prime ell different from p,
  the chosen finite intermediate extension E/Q_ell, the positive coefficient level,
  and a separated finite-type X0 over k0. The category is the recorded intrinsic
  constant-ring module derived category on the small pro-etale site.
- `(K,phi) in D^b_ctf,W(X,A)` is `K : T.strictWeilComplex`. Its carrier and Weil
  isomorphism are the published fixed-pair construction, not a derived category of
  Weil sheaves. No stability or extra structure is assumed.
- Every positive integer m is represented uniquely as `r + 1`, with `r : ℕ`.
  Positivity is required by def-trf-frobenius-operators and def-trf-iterated-weil-map.
  The item does not introduce a zero or negative iterated Weil isomorphism.
- `c₀ : Compactification T.X₀.hom` retains the representative over k0 used in the
  node's proof. It is arbitrary, and compactifiability follows from the existing
  separated finite-type hypotheses. The geometric compactification is exactly
  `frobeniusCohomologyCompactification`, with target Spec k, for all powers.
- `RΓ_c(X,-)` is `T.finiteGlobalCompactSections c₀`, the composite of the recorded
  `sfIntrinsicCompactSupport` and exact point evaluation `T.finiteLocalSections`.
  This is Fib_s(Ra_X!(-)), with the same point-category localization and ULift
  coefficient convention as the dependency's finite compact transport. The ambient
  functor permits actual functorial action on maps; K is still restricted to the
  required bounded constructible finite-Tor category.
- The phrase “m-th iterate of global geometric Frobenius” is the first equality:
  `T.finiteGlobalFrobenius c₀ K r = (T.finiteGlobalFrobenius c₀ K 0) ^ (r + 1)`.
  Endomorphism powers are categorical composition powers.
- The displayed equality in the node is the second equality. The right-hand side
  is `T.finiteGlobalDirectPowerTransport c₀ K.obj.carrier r` followed by the functor's
  image of `(T.iteratedWeilIsomorphism K (r+1) ...).hom`. Lean's `≫` applies the
  leftmost arrow first, so this renders precisely H(phi^[m]) composed with direct
  compact-support transport along g^m.
- `phi^[m]` is the recorded `iteratedWeilIsomorphism`, with exactly the canonical
  pro-etale constant-ring pullback-composition comparisons used by its definition.
- The last clause, `IsIso (T.finiteGlobalDirectPowerTransport ...)`, renders the
  node's designation of the first arrow as a base-change *isomorphism*.
- The direct map is constructed from `pointPowerTransportFinite` (restriction,
  colimit insertion and derived pullback along h^m), the unit-normalized
  `pointPowerPullbackModel`, and `FrobeniusExchange.finiteCompact` for g^m, its
  middle compactification power and h^m. Its square witnesses are pastes of the
  existing Cartesian squares. No arbitrary map or isomorphism is a hypothesis.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, its geometric
  fibre, and `FiniteFieldDatum.CoefficientDatum` (through coefficient conventions).
- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `coefficientRing`,
  `geometricBaseChange`, `structureMap`, bounded constructible and finite-Tor
  predicates, `pointFibre`, `compactSupportComplex` and `compactSupportCohomology`.
- `Sheaf.Paper.TraceFormulaStrictWeilComplex`: `strictWeilComplex`,
  `strictWeilForget`, `strictWeilFrobenius`.
- `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator`: `finiteLocalSections` and all
  four local declarations retained publicly by the repaired dependency module.
- `Sheaf.Paper.IteratedWeilMap`: `iteratedWeilIsomorphism`, its recursive construction
  and `iteratedWeilPullbackModel`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`:
  `frobeniusCohomologyCompactification`, `frobeniusCompactTransportFinite`.
- `Sheaf.Paper.FrobeniusPullbackComparisonCoherence`: `frobeniusPullbackPower`,
  `trfPositiveFunctorPower`, `frobeniusPullbackPowerComparison` and its coherence
  theorem. The new definition node `def-trf-frobenius-pullback-power-comparison` records
  these existing definitions and is cited in stmt_deps. The coherence theorem is
  retained only in proof_deps; none of these comparisons uses its proof or `.choose`.
- `Sheaf.TraceFormula.PointTransportComposition`: `pointFrobeniusAut`,
  `pointPowerTransportFinite`, `pointPowerPullbackModel`. This already-landed node
  is added to stmt_deps for its direct power-transport construction.
- `Sheaf.Paper.FrobeniusGeometricExchange` and its public imports:
  `FrobeniusExchange.finiteCompact`, `galois`, the retained model's middle/open/proper
  maps, and the canonical open-square derived pullback coordinate comparison.
- `Sheaf.SixFunctors.FrobeniusSquareCartesian`: `FiniteFieldDatum.frobenius_square_cartesian`.
  Mathlib `IsPullback.id_horiz` and `IsPullback.paste_horiz` construct power-square
  witnesses; the local proof terms are just the witnesses for that construction.
- Stated proof dependencies are imported: `Sheaf.CategoryTheory.NaturalTransportInduction`
  (`NaturalTransport.compared_eq`), `Sheaf.Paper.IteratedWeilCocycle`
  (`iterated_weil_cocycle`), and `Sheaf.Paper.IsomorphismDerivedPullback`
  (`isomorphismFiniteDerivedPullback_termwise`), together with the publicly imported
  comparison coherence, scheme-Frobenius, exchange and transport modules.
  `lem-trf-compact-frobenius-transport-composition` and
  `lem-weil-frobenius-cohomology-transport-iso` have no published Lean module in the
  inspected DAG, so there is no proof-only module to import for those nodes.

Edge cases checked before writing: m=1 uses exactly one degree-one transport and the
identity comparison; m=2 composes two transports with the inverse canonical comparison.
Both positive coefficient level 1 and general positive levels are covered by splitting
the recorded natural level into zero (impossible by its own positivity) or successor.
No case of p=2 or ell=2 (when distinct from p) is excluded. The zero complex and the
empty scheme require no nonzero or nonempty assumption. Arbitrarily negative
cohomological degrees remain available in the repaired operator definition. Scheme
object/morphism universes and the u+1 module carriers have not been identified.

Searches for an existing statement (all performed with the prescribed msearch wrapper
or direct rg on the permitted source trees):

- leanfinder: “Geometric Frobenius on compactly supported cohomology is the direct
  power pullback followed by the iterated Weil isomorphism”: 8 hits on purely
  inseparable Frobenius and Witt isocrystals; no match.
- loogle: `"Frobenius", "cohomology"`: 0 hits.
- leansearch: “Frobenius compactly supported cohomology iterated Weil isomorphism”:
  8 hits about iterateFrobenius and iterated derivatives; no match.
- msearch grep: `Frobenius|frobenius` in Mathlib AlgebraicGeometry: 0 hits.
- rg of the item's id, `compactDescription|compact_description`, and compact-support
  transport names in upstream WeilConjectures and lean/Sheaf: the id occurs only
  in supporting proof modules; no theorem already states the item.
- rg of `finiteGlobalFrobenius|finiteGlobalCompact|compactFrobeniusPower` in upstream,
  lean/Sheaf and dag/lean_names_upstream.json: no existing declarations.
- Read upstream `AlgebraicGeometry.Etale.frobeniusOperator`: it is the linear map on
  Hom(unit,M) in the etale sheaf-derived category, not an endomorphism of the actual
  intrinsic pro-etale compact-support coefficient complex. The previous operator
  node's lean.note independently identifies the missing global clause.

The source statement was opened in the current main-20261015 blueprint. The resolved
stage-1 repair note was read: its split is retained without changing any proof step.
No STATEMENT-DISPUTED issue or natural-language statement correction is needed.

## Dependency modules

`def-trf-frobenius-operators`: the published Q52 record supplies clause 2 only;
its note explicitly identifies the missing compact-support clause 1. Under §1(B),
this delivery extends its owning module
`Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` by appending six global definitions.
It retains the primary `finiteLocalFrobenius` declaration, its recorded signature,
and all four original local declarations byte for byte. The record lists those
four local declarations followed by the six global declarations. No separate
`TraceFormulaGlobalFrobeniusOperator` module remains. The two required public imports
are `FrobeniusCohomologyTransport` and `FrobeniusPullbackComparisonCoherence`.

`finiteGlobalCompactSections` realizes RΓ_c as compact support followed by exact
point evaluation. `finiteGlobalCompactStep` uses the recorded degree-one compact
transport and its unit-normalized pullback presentation change;
`finiteGlobalRepeatedTransport` has exactly m factors;
`finiteGlobalComparedTransport` follows it by H(d_m⁻¹);
`finiteGlobalFrobenius` follows this by H(φ^[m]);
`finiteGlobalFrobeniusCohomology` applies H^i for every integer i. All data are
constructed; no extra hypotheses or postponed proofs enter this dependency module.

## New nodes

`def-trf-frobenius-pullback-power-comparison` records the existing plain definitions
in `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` with `existing: true` and no
new module. Its main declaration is `frobeniusPullbackPowerComparison`; it also lists
`trfPositiveFunctorPower`, `trfPositiveFunctorPowerSplit`, `frobeniusPullbackPower`,
and `frobeniusPullbackPowerSplit`. The source is the current compact-description
blueprint's m-th-iterate assertion and its canonical pullback-composition construction.
The natural-language statement defines actual positive pullback powers, recursive
functor powers, their canonical binary splitting and d₁=id, dₘ₊₁=T(dₘ)∘C₁,ₘ.
It asserts no coherence theorem. This is exactly the recurrence in the existing source,
where predecessor indices represent positive exponents. Every dependency supplies
its recorded coefficient datum, Frobenius or canonical pullback comparison.

Search records retained in the node and `searches.jsonl`: LeanSearch returned eight
unrelated Frobenius/pullback results; Loogle returned no match for
`frobeniusPullbackPowerComparison`; Mathlib and upstream grep returned no match.
Project grep found precisely the five existing definitions in the coherence module;
DAG search found only their auxiliary listing under the coherence theorem, and
blueprint_refs.py found no definition node. The new node therefore reuses those
existing declarations, as R1 requests, rather than duplicating them. Its statement
introduces no coherence assumption; m=1 gives the identity and the successor case
is the published whiskering and comparison construction.

## Returned points repaired

R1 (H2): the item cites the new definition node instead of
`lem-trf-frobenius-pullback-comparison-coherence` in stmt_deps. The theorem stays in
proof_deps and remains imported for the eventual proof. The point-transport theorem
remains a statement dependency as explicitly accepted in the return: its actual
canonical point-power construction uses the unique comparison selected by `.choose`.

R2 (H13/H4): the dependency record and owning local module are extended in place as
specified above. All four Q52 local declarations and their primary signature remain;
the six global definitions are appended. The separate global module is absent.
Current shared sources were searched for `compactPowerTransport` and
`finiteGlobalDirectPowerTransport`: neither is published, and the Q05 compact
composition node has no Lean record, so the direct map remains owned by this item.

Validation: the prescribed scompile.py checked both delivery files separately in
import order, including their library forms, successfully and without warnings.
The final library checks took 13.3 seconds for the dependency repair and 28.9 seconds
for the item. An initial cohomology localization-size mismatch was repaired by using
exactly the recorded point target's HasDerivedCategory.ofIsGrothendieckAbelian instance;
explicit base-square annotations resolved the chosen-pullback elaboration. Every
variable and universe is explicitly bound. There are no postponed proofs in the
dependency repair and exactly one in the item, matching the item DAG node.

Repair self-check (2026-10-18): the initial deliver2.py dry run compiled both
saved modules and checked all five existing comparison declarations. Its sole
preflight failure was the missing `## New nodes` report section. This report now
describes the saved R1/R2 repairs, removes the obsolete separate-module description,
and supplies that section. Comparison with the current shared node copies confirms
that the dependency changes only `lean` and the item only `lean` and `stmt_deps`.
The item's natural-language statement and proof plan are unchanged. The original
four local declaration bodies are byte-preserved; the only new postponed theorem
is the item's named theorem, with its complete proof docstring. The independent
maintainer review remains the second reading; no second worker was started.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
