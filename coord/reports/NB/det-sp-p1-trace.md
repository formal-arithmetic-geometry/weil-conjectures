## Worker report

The delivery states `AlgebraicGeometry.ProEtale.proEtale_projectiveLine_trace` in
`Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace`. The original node's statement,
proof and proof dependencies are unchanged. Its statement dependencies gain already
landed interfaces, three existing-definition ownership nodes for the canonical maps,
the canonical trace-system node, and the exact Cartier-realization interface below. There are no
dependency-module repairs.

The canonical all-base family conditions are defined in
`Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem`; the main theorem imports
that interface. `SpP1BaseTraceConditions` is exactly the conjunction of the four
base-normalization predicates described below.

The sole postponed proof is the named main theorem. All other declarations are fully
written constructions, type families or proposition definitions. Existential maps are uniquely fixed
by their exact canonical formulas; none is an arbitrary map supplied as a hypothesis.

Hypotheses and objects:

- `ℓ : ℕ`, `hℓ : ℓ.Prime`, `n : ℕ`, `_hn : 0 < n` render the prime and positive exponent.
  A is exactly `ULift.{u + 1} (ZMod (ℓ ^ n))`, the canonical copy in the existing
  module-sheaf universe. The killing equation is `CharP.cast_eq_zero`. The finite
  instance is explicitly constructed from `ZMod.fintype` and `pow_pos hℓ.pos n`;
  it is a term, not an added hypothesis. No completion occurs.
- `geoP1Comparison`, `geoP1Pullback`, `geoP1Pushforward`, `geoP1Unit`, and `geoP1Twist`
  are the recorded ordinary small-pro-etale module derived objects and functors.
  Twists are exact ν* of the signed etale finite Tate sheaf in degree zero with
  the displayed shift. The positive line is the roots-of-unity module for Z/N;
  the negative line is its sheaf Hom dual. The untwisted Chern component uses the
  existing derived tensor/evaluation construction `Etale.p1DecompositionMap`.
- P is `ProjectiveLine S`, q is `(ProjectiveLine S ↘ S)`, W is `pullback q q`, and
  Δ is `pullback.diagonal q`. The two projections are the existing
  `Etale.projectiveLineDiagonalProjection S a`: false is first, true is second.
- `[IsNoetherian S]` occurs in `SpP1DiagonalIntegrals`, with the recorded finite
  affine Noetherian-cover meaning. The first two clauses cover all schemes as
  required by the node's final paragraph. `IsUnit (N : Γ(S, ⊤))` renders invertibility
  of ℓ: N=ℓ^n and n>0 make these equivalent, including on the empty scheme.

Clause 1:

`SpP1ChernFamily` supplies the etale derived arrows c on all bases.
`SpP1NormalizedDecompositions` requires their actual abelian cohomology realizations
`Etale.ordinaryFiniteP1ChernSpec`, the Kummer boundary of the recorded O(1).
`SpP1DecompositionFamily` gives d with exactly the displayed domain and codomain.
The first map equality fixes d to `geoP1SumComparison`, followed by ν* of the existing
`Etale.p1DecompositionMap` using this same c, followed by `geoP1PushComparison`.
Thus it is precisely the unit-and-Chern map, and `IsIso (d S hS)` asserts (1).
`SpP1BaseChange` states its exchange square with `geoP1UnitExchange` and
`geoP1SourceMap`. S, S', and g are arbitrary; no flatness or Noetherianity is imposed.

Clause 2:

`SpP1TwistedFamily` consists of actual isomorphisms b with the specified endpoints.
The two remaining equalities in `SpP1NormalizedDecompositions` fix inl then b.hom
and inr then b.hom to the existing etale positive shifted unit and Chern adjunct,
respectively, followed by the canonical pro-etale comparison mate. The unit uses
the roots-normalized `projectiveLineTraceTransport`; the second component uses
`ordinaryFiniteP1ChernPushforward` on the very same c. Mate coherence identifies
these with the pro-etale unit and adjoint of the comparison-pulled Kummer class.
The trace is the existing `geoP1Trace`, exactly b.inv followed by `biprod.snd`.
The second square in `SpP1BaseChange` is its arbitrary-base-change compatibility.
`SpP1TraceChern` says that its fixed second component integrates to identity on A_S.
`SpP1RationalPointChern` quantifies over every algebraically closed Ω and every
Ω-rational section x of P1, supplies its Cartier ideal, and equates its actual
`Etale.supportedKummerChern` with that same hyperplane cohomology class. This gives
the normalization at every rational point on every geometric fibre. Arbitrary
geometric structural morphisms are included in the base-change quantifiers.

Clause 3:

`SpP1DiagonalIntegrals` quantifies over every Noetherian S with N invertible.
Its hI is invertibility of the actual diagonal ideal. The supported class κ is
required to satisfy `Etale.SupportedKummerBoundary`, the full normalized relative
Kummer boundary, not just an equation after forgetting supports.
The class `cΔ : GeoCartierClass ... Δ` is tied to this same κ by
`SpP1CartierCompatibility`, definitionally exactly
`(Ext.mk₀ geoCartierSourceComparison).comp cΔ (zero_add 2) =
κ.mapExactFunctor comparisonUpperStar`. This is the literal characterization of
`exists_geoCartierCycleClass`; boundary uniqueness and its invertible source
comparison fix precisely the class used in (G6).

The arrow δ has the fixed endpoints RΔ_* A_P -> A_W(1)[2].
`CartierDerivedCompatibility` directly equates this same δ with the exact
pro-etale derived realization of cΔ. The explicit exactness witness is
existentially asserted for the closed direct image, not assumed of the base.
The source identification `cartierUnitSingleIso` is the canonical
comparison/single-functor isomorphism followed by comparison of constant sheaves.
The target identification `cartierShiftSingleIso` is canonical commutation with shift
followed by comparison with the single functor. Thus the actual cΔ occurs in the
defining equation for δ itself. The older duplicate formula transporting the
etale realization through an auxiliary comparison isomorphism e is removed;
the source requires the direct Cartier realization, which is now explicit.

The α family has exactly A_P -> Rp_a* RΔ* A_P as endpoints. Its two equalities
fix it to the inverse derived-identity comparison followed by the inverse of
`rightDerivedLowerStarFactor` for `pullback.diagonal_fst` or `diagonal_snd`.
This is directly the canonical composition identification from p_a Δ=id;
`IsIso (α a)` also asserts its displayed invertibility.
The τ family has exactly the projection-trace endpoints. Its equation fixes each
member to the existing projective-line chart's adjunction unit, canonical direct-image
factorization, normalized twist pullback, and the same b-defined trace over P.
The final equality is literally α then Rp_a.map δ then τ equal to identity on A_P,
for both Boolean indices. Every map and its source identification is included.

The final arbitrary-base consequence is the unrestricted S in the first two clauses.
The proof docstring explains descent from Spec Z[1/ℓ] and compatibility with its
structure morphisms, following the node's proof.

`HEq` only compares terms of the same fixed Hom or cohomology types. The recorded
source and target objects are identical on both sides; `eq_of_heq` and `heq_of_eq`
identify it with ordinary equality. This avoids expensive redundant kernel checking
of concrete derived-category instances without changing any mathematical equation.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `ProjectiveSpace`, `ProjectiveSpace.isPullback_map`, its properness instance,
  and `ProjectiveLine`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`:
  the ordinary derived adjunction and exact/left-derived inverse-image comparison.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`, whose unbounded termwise functor is the
  existing `geoP1Comparison`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`:
  `Scheme.finiteEtaleTateSheaf` and its positive line, with the roots-normalized
  pullback interface of `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `Scheme.kummerSequence_shortExact` and its actual Kummer boundary.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `ProjectiveSpace.twist`, through the existing Kummer-class definition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, its projections and diagonal.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` supplies the
  general composition proof interface; the existing ordinary fixed-module
  specialization `ProEtale.rightDerivedLowerStarFactor` is used directly from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  the existing derived tensor used by the recorded Chern-adjoint construction.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  the actual divisor ideal and dual-line interface used by `supportedKummerChern`.
- `Sheaf.AlgebraicGeometry.GeoCartierCycleClass`:
  `GeoCartierClass`, `geoCartierConstant`, `geoCartierLine`,
  `geoCartierSourceComparison` and its theorem's supported-boundary normalization.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`:
  `Scheme.proEtale_ringed_open_closed`, for exact closed image in the proof plan.
- `Sheaf.AlgebraicGeometry.GeoP1Cohomology`: all its canonical coefficient,
  comparison, exchange, source, pullback and trace helpers are reused directly.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer` and
  `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition`: the actual Kummer class
  and canonical negative-twist/evaluation decomposition map.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`:
  `ordinaryFiniteP1ChernPushforward` and the existing ordinary adjunction interface.
- `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals`:
  `projectiveLineDiagonalProjection`, `projectiveLineDiagonalChart`, and the etale
  diagonal-integral theorem used by the proof plan.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem` and
  `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`: the canonical exact
  closed-image realization and the supported-boundary and divisor-Chern predicates.


The existing `def-amb-p1-trace` owning node is also cited for its normalized
`projectiveLineTraceTransport`. The three new ownership nodes have `existing: true` records on unchanged landed
modules; the trace-system and Cartier-realization nodes supply the two new definition modules. No object, site, coefficient action, or canonical map is
replaced by a new notion.

Edge cases checked: the empty scheme; disconnected and nonreduced Noetherian bases;
non-Noetherian and nonflat base changes; ℓ=2, n=1; both coordinate rational points;
and both projection indices. Only the source's positive-exponent condition excludes
n=0. All universes and variables are explicitly bound. No extra decomposition,
exactness, canonical-map, or geometric hypothesis is assumed.

Searches:

- msearch LeanFinder: "projective line proetale cohomology Kummer decomposition
  trace diagonal integrals"; eight unrelated group-cohomology/cotangent results,
  no projective-line trace theorem.
- msearch Loogle: "ProjectiveSpace, ProEtale.derivedLowerStar"; no hits (Mathlib
  does not know the project-specific ProjectiveSpace identifier).
- msearch grep, AlgebraicGeometry: "projective.*[Tt]race|geoP1|[Pp]1.*[Dd]ecomposition";
  zero Mathlib hits.
- msearch LeanSearch: "projective line decomposition trace proetale diagonal cycle
  class"; eight unrelated matrix-trace/projectivization/immersion results.
- rg and id search in WeilConjectures: no declaration attached to det-sp-p1-trace
  and no existing theorem covering its pro-etale trace plus diagonal identities.
- rg in Sheaf: found GeoP1Cohomology, ProjectiveLineTrace and
  ProjectiveLineDiagonalIntegrals. Their exact signatures were read: the first
  covers only Noetherian base changes and has no diagonal integrals; the latter
  two are etale. Their objects and canonical arrows are reused, rather than
  reintroduced. No existing declaration states the whole node.

No statement dispute or source correction is needed.

## Second reading by NB

No independent worker reading was performed: the dispatcher requires direct worker
delivery and forbids starting other agents. The maintainer independently reviews this
packet. The worker checked each hypothesis, formula, and clause against the original
node and its recorded dependencies, including the actual supported Cartier comparison,
the two canonical source identifications, and unrestricted base changes.

## New nodes

`def-sp-p1-proetale-trace-system` defines the canonical decomposition and trace-family
predicate for all bases. Its module contains the three family types and the four
normalization predicates `SpP1NormalizedDecompositions`, `SpP1BaseChange`,
`SpP1TraceChern`, and `SpP1RationalPointChern`; `SpP1BaseTraceConditions` combines
those exact predicates. It neither asserts existence nor changes the project
objects, functors, twists or canonical arrows. Its source is the item's clauses
1--2 and final arbitrary-base consequence. Separating this independently usable
interface lets each module compile within the required per-file limit.

Searches for this notion: blueprint_refs.py search returned zero blueprint matches;
rg of DAG nodes, Mathlib, WeilConjectures and Sheaf found only the existing etale
interface and the Noetherian pro-etale theorem, which are reused. LeanSearch query
"normalized projective line Kummer decomposition trace system arbitrary base change"
returned elliptic-curve base-change and normalized field-trace results. LeanFinder
query "canonical projective line decomposition and trace family with base change
and rational point normalization" returned eight Weierstrass-projective results.
Mathlib AlgebraicGeometry grep for
"projective.*trace.*system|normalized.*[Pp]rojective|SpP1" returned zero hits.
The new node records these outputs and cites every existing notion it uses.

The worker also checked the new definition against each formula in clauses 1--2:
all its quantifiers, endpoints, Kummer normalization, both exchange equations, the
hyperplane identity, and the rational-point divisor equation are explicit. Its
finite-ring and positive-N binders specify the intended coefficient interface;
they do not add hypotheses to the main prime-power theorem.

Validation: scompile.py compiled both delivered modules separately, in dependency
order, against the live library. The trace-system module took 27.8 seconds and the
trace theorem module took 45.2 seconds. Both compiled without errors or unexpected
warnings. The first preflight identified a blueprint ancestry-path metadata mismatch
in the new node; its `via` now matches the tool's required empty path for this item.


### Returned-delivery repair

The saved packet was first tested unchanged with deliver2.py --no-push: it passed
preflight and per-file compilation at dry-run commit 5db91fd8335. This is only the
starting check; the following changes repair the independent review of immutable
head c93f38353dfc and are not an unchanged re-push.

H2: replace `sk-lem-geo-p1-cohomology`, `thm-amb-p1-decomposition`, and
`lem-amb-p1-diagonal-integrals` in the item's stmt_deps by the three definition
ownership nodes below. Make the first two replacements also in
`def-sp-p1-proetale-trace-system`, including its bracketed definition citations.
The original item's statement, proof and proof_deps remain verbatim from the live
base: in particular its etale decomposition and diagonal theorems remain proof
inputs. The geoP1Cohomology theorem itself is not used by the statement.

Advisory: add the explicit equation `CartierDerivedCompatibility ... cΔ δ`.
This prevents the cΔ conjunct from being disconnected from δ. It uses the
canonical exact-functor/single-object comparison already defined by
`Etale.supportedExactDerivedMap`, now applied to pro-etale closed direct image.
The finite-colimit-preservation witness belongs to the conclusion. All sources
and targets are transported by the fixed comparison/single/shift isomorphisms;
no arbitrary identification is introduced. Both projection identities and the etale supported-class characterization of cΔ
remain present. The earlier auxiliary e and duplicate etale formula for δ are
removed, since the direct exact pro-etale realization now states precisely the
source’s requested definition of δ.

### Existing definition ownership

Additional new ownership nodes, all in sec-six-functors-basics:

- `def-sp-p1-comparison-arrows` records the existing definitions in
  `Sheaf.AlgebraicGeometry.GeoP1Cohomology`: comparison, pullback, pushforward,
  their pull/push comparisons, sum comparison, constant and signed coefficient
  objects, normalized coefficient pullbacks, source map, exchange and its two
  coefficient specializations, and the second-projection trace. Its primary
  declaration is `AlgebraicGeometry.ProEtale.geoP1Comparison`; every owned helper
  is listed in lean.declarations. No assertion of decomposition invertibility,
  trace existence, or Noetherianity is included.
- `def-sp-p1-decomposition-arrows` records the existing
  `AlgebraicGeometry.Etale.p1DecompositionTwist` and `p1DecompositionMap` in
  `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition`. For every supplied
  Chern arrow, the latter is the actual coproduct of the unit and tensor/evaluation
  adjunct; it asserts no isomorphism and requires no Noetherian base.
- `def-sp-p1-diagonal-charts` records the existing
  `AlgebraicGeometry.Etale.projectiveLineDiagonalProjection` and
  `projectiveLineDiagonalChart` in
  `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals`. False/true are the
  first/second projections. The relative charts are the flipped/unflipped
  canonical projective-space base-change isomorphisms, including their structural
  equations. They carry no coefficients or Noetherianity assumptions.

The three existing modules are unchanged and no Lean module copies their data.
The trace-system module is also unchanged. Search before adding these nodes:
for each notion msearch LeanSearch and LeanFinder were run with its corresponding
plain-word query; each returned eight results without the complete project
notion. In the diagonal case Mathlib's cover-dependent pullback charts appeared,
which are not these relative projective-line charts. msearch grep for each pair
of concrete identifiers in Mathlib AlgebraicGeometry returned zero hits. Exact
outputs are recorded in each new node. rg of dag/nodes found the helpers only
attached to their theorem owners and a consuming tower theorem, never a definition
owner. rg of WeilConjectures found no definition with these identifiers; rg and
full source reads of Sheaf found the unchanged matching definitions above.
blueprint_refs.py search returned zero matches for
`projective.line.*(comparison|decomposition|diagonal)`.

Self-check: the ownership changes add no hypothesis and no mathematical object;
the diagonal equation uses precisely the cΔ already quantified and fixed by the
normalized supported Kummer comparison. Empty schemes and both Boolean
projections remain included. The base-trace family still quantifies over all
schemes and arbitrary base morphisms. All new nodes have empty proof fields and
`existing: true`; the main theorem remains the only postponed proof in this packet.


The two fixed transports in the direct Cartier equation are named
`cartierUnitSingleIso` and `cartierShiftSingleIso` in `Sheaf.AlgebraicGeometry.CartierDerivedRealization` and listed
in that definition node’s lean.declarations. Their definitions are the literal constant/single and
shift/single comparisons described above. Naming them avoids repeatedly
elaborating their large concrete derived-category instances. Their bodies have
no postponed proof or chosen arrow.


### Canonical Cartier derived-realization node

`def-sp-cartier-derived-realization` owns
`Sheaf.AlgebraicGeometry.CartierDerivedRealization`: the generic
`AlgebraicGeometry.ProEtale.CartierDerivedCompatibility` predicate and the
canonical `cartierUnitSingleIso` and `cartierShiftSingleIso` comparisons. For an
exact additive F, a supplied Ext class c, and specified source/target transports
s,t, the predicate is the literal equation
`HEq δ (F.rightDerivedFunctor.map s.hom ≫
supportedExactDerivedMap F X Y c ≫ t.inv)`. The item supplies both transports
by their named canonical formulas, and the δ already has precisely this Hom
type. There is no arbitrary map or hypothesis on the base. The shift comparison
is defined for any exact additive functor, then applied to ν* and the actual
Tate line. The constant comparison is defined for every scheme.

This is an independently usable specification of the relationship between a
Cartier Ext class and a supplied derived arrow, not an existence assertion or a
replacement for exact direct image. It imports and reuses the existing
`supportedExactDerivedMap` without copying it. It is distinct from the existing
etale supported Kummer-system predicate, and from the Ext-class construction
`GeoCartierClass`: it identifies the very arrow subsequently used under derived
projection with that class. Source: clause 3’s explicit definition of δ from cΔ.
The node cites the existing derived-category, supported-realization, coefficient,
Tate-line and Cartier interfaces. Its module has no theorem or sorry.

Searches for this interface: msearch LeanSearch and LeanFinder for
"exact derived direct image realization Cartier Ext class canonical source target
comparison" each returned eight generic Ext/exact-functor results, including
`Ext.mapExactFunctor_hom`; these are the existing ingredients, and do not define
the supplied-arrow predicate with its fixed transports. The existing generic
realization is reused directly. Mathlib grep for
`CartierDerivedCompatibility|cartierUnitSingleIso|cartierTwistSingleIso` returned
zero hits. rg of DAG, Sheaf and WeilConjectures returned no matches, and
blueprint_refs.py search
`Cartier.*derived.*realization|exact.*Cartier.*comparison` returned zero matches.
The new node records the actual complete msearch outputs.


### Repair validation

The final three-module scompile.py run passed with no errors or warnings:
CartierDerivedRealization compiled at its library path in 29.5 seconds,
ProEtaleProjectiveLineTraceSystem in 27.8 seconds, and
ProEtaleProjectiveLineTrace in 47.1 seconds (its sandbox compilation took
41.3 seconds). All used the prescribed 60-second limit. The source and target
transports are factored into the independent exact Cartier-realization interface;
its HEq wrapper uses the actual derived Hom universe. Temporary diagnostic
#check commands and scratch copies were removed.

The final self-check matched every lean.statement verbatim against its module,
checked every bracketed citation of each new definition against stmt_deps,
verified all Lean lines at most 100 characters and all variables/universes bound,
and confirmed that the item differs from current live source only in lean and
stmt_deps. Its statement, proof and proof_deps are unchanged. The theorem-owner
references named by H2 are absent from the item and trace-system stmt_deps.
All three existing-definition modules remain untouched. The only sorry is the
named theorem proEtale_projectiveLine_trace with its source and proof docstring.
