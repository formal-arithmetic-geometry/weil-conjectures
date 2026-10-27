## Worker report

The module Sheaf.Paper.ClassicalFiniteWeilDiagramRealization states
WeilConjectures.classical_finite_weil_diagram_realization with sorry. Its only
postponed theorem is that declaration. All auxiliary definitions have concrete data:
typed words, list expressions and their evaluation; normalized-stage records; the
canonical IsoAlgebra transport functors; and the predicates expressing prescribed
module lifting and coefficient coherence. These helpers spell out this node's
clauses and do not introduce another sheaf, coefficient, site or realization notion.
No node statement, dependency, proof or metadata is changed outside lean.

Clause-by-clause correspondence:

* The prime power, base field and algebraic closure are FiniteFieldDatum D;
  l, Fact l.Prime, hl : l ≠ D.p and Ω with Field, Algebra and IsAlgClosure give the
  coefficient hypotheses. Y₀ is Over (Spec D.k₀), with LocallyOfFiniteType,
  QuasiCompact and IsSeparated on its structure map. Y is literally
  (D.geometricFiber Y₀).left and Frobenius is D.geometricFrobenius Y₀.
* IsNoetherian and separatedness are the inherited zlClassicalNoetherian and
  zlClassicalSeparated instances. The supplied datum R records finite dimension
  in R.dimension. The theorem additionally concludes Finite (ConnectedComponents Y) and
  ∀ y, IsClopen (connectedComponent y). There is no connectedness hypothesis.
* R : ZlClassicalRealization D l hl Ω Y₀ is universally quantified before M and
  the arrow data. Its functor, normalization, pullback and pullback_pinning are
  the caller's fixed datum from def-zl-normalized-classical-weil-realization.
  Every existential P₀, E, N and prescribed lift is relative to that same R.
  No realization is chosen in the conclusion.
* I and A have independent universes and only Finite instances; s,t : A → I
  are the source and target maps. M : I → ZlClassicalWeil is the actual classical
  lisse algebraic-coefficient category with its Weil isomorphisms. The arrows
  a : ∀ j, M (s j) ⟶ M (t j) are its commuting-square morphisms.
* J is an arbitrary finite equation index. The endpoints x,y : J → I × ℕ
  record vertices and actual iterated Frobenius pullbacks. ZlWeilWord has identity,
  arrow, Weil hom, Weil inverse, composition and pullback constructors. A
  ZlWeilExpression is a finite list of integer-weighted words. Distributing
  composition and pullback over addition expresses every finite additive composite
  in this form, including differences, repeated terms and the empty sum.
* zlClassicalEquation tests the equality on all actual geometric adic fibres,
  using lisseAlgebraicFiberFunctor. Geometric stalks detect equality of sheaf maps;
  inverse limits and the two coefficient extensions are the recorded classical
  fibre construction. This describes additive equations without choosing a new
  additive structure on the coefficient localization.
* The existential E : Padic.FiniteCoefficientFields l Ω is one finite field for
  all vertices, maps, inverses and equations. N consists of IsoAlgebra objects for
  the actual completed-system raw pullback operation. Each carrier is RawRational,
  whose integral object is the recorded normalized finite-free tower, with the
  geometric-stalk freeness condition and locally constant finite ranks. Positive
  exponent n+1 is indexed by n, exactly as in CompletedLisse.Systems.
* b gives rational Weil arrows, and β gives classical Weil isomorphisms to M;
  the first conjunct identifies each prescribed arrow with its finite model.
  The next conjunct is equality of the signed word sums in the raw rational
  category BEFORE extension to Ω. A separate conjunct states their equality
  after the finite heart functor P.finite.
* P extends ZlClassicalPullbackModels, retaining its finite lisse realization,
  module comparison P.sheaf, coefficient_values and sheaf_linear. The comparison's
  completed.rationalObject identifies its module with the rationalization of
  completed.equivalence.inverse of the tower; completed.completion and its IsLimit
  condition identify that inverse with lim ν* N_n. Its rational_map and rational_add
  give exactly a(1 tensor f). P.finite_fullyFaithful states the normalized Hom
  bijections on these systems.
* P.heartWeil uses IsoAlgebra.mapOfNatIso P.finite_pullback and restricts to the
  actual sf heart using P.lisse. Thus it carries BOTH Weil hom and inverse,
  and its arrows are Weil-equivariant. The theorem explicitly records lissity
  at finite coefficients and IsCommonStageLisse after the realization R.
* P.ordinary_unit is the ordinary module-unit / completed rational-unit square;
  P.finite_unit is the canonical finite-level adjunction-unit square with literal
  automorphism reindexing. P.classical_values requires equality to the existing
  classical pullback object identification, not a freely chosen isomorphism.
  P.stage_pullback_objects is equality of the actual endpoints. P.pinning is
  precisely the common-stage pullback equality through P.stage at BOTH endpoints.
  These fields expand the same existential in ZlClassicalPullbackStage so the
  diagram and the pinning use the same finite witnesses.
* P₀ provides such witnesses at every finite field. ZlDiagramCoefficientCoherence
  ties their realizations and Frobenius Along data to ONE existing normalized
  Family. Its FieldChange, FieldComposition and Mixed fields supply naturality,
  associators and pullback compatibility under finite coefficient extension;
  FieldNormalized is required for every finite inclusion. No new arbitrary
  scalar map replaces the canonical tensor maps.
* ZlPrescribedWeilLifts states the final unique-lifting clause. It universally
  quantifies the finite field of an identification, a classical Weil model β,
  an arbitrary lisse finite heart Weil object H, its common-stage image η to an
  arbitrary K, and the prescribed module iso ξ. The hypothesis is precisely the
  ordinary-module Weil square with zlDiagramModuleWeil, whose comparison is
  P.along.comparison inverse followed by realized Weil structure. Its conclusion
  is ∃! common-stage Weil iso B with a finite heart iso ψ whose module map is ξ
  and whose common-stage map is the explicitly displayed composite using β,
  P.stage and η. Thus uniqueness concerns the prescribed map, not an arbitrary
  isomorphism between isomorphic endpoints. Common-stage maps and equations have
  a finite representative, so the universal finite-stage quantifier includes
  identifications requiring further coefficient extension.
* No assertion requires the rational b or N.str to preserve the integral towers.
  There is no nonzero-rank, nonempty-base, nonempty-index or Frobenius-fixes-
  components assumption. Zero objects and zero words/sums remain permitted.

Dependency declarations read and used (including their signatures and docstrings):

* Sheaf.Paper.LisseIntegralSmallCoefficients and its public original
  Sheaf.Paper.LisseAdicSheaves: Scheme.LisseIntegralSheafOfUniverses,
  LisseIntegralSheaf, LisseRationalSheaf, LisseAlgebraicSheaf, and normalized
  scalar operations. The recorded small-coefficient interface remains imported;
  the existing CompletedLisse interface uses the large actual subfields E.val.
* Sheaf.Paper.SfConstructibleHeart: sfRationalHeartProperty, sfCommonStageHeartProperty,
  sfRationalHeart and sfCommonStageHeart.
* Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients:
  generalAlgebraicallyClosedConstructibleCategory, Stage, inclusion, Coefficient.
* Sheaf.Paper.LisseRationalRealization: LisseRealization.lisse_rational_realization;
  its public data interfaces At, Along, PullNormalized, Family, FieldNormalized.
* Sheaf.Paper.FiniteFieldFiber: FiniteFieldDatum and geometricFiber.
* Sheaf.AlgebraicGeometry.FrobeniusDetailed: FiniteFieldDatum.geometricFrobenius.
* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: finite_coefficientExtensionRing
  and its public coefficientExtensionIntegers / Uniformizer / Ring constructions.
* Sheaf.Paper.SfWeilSheafComplex: sfWeilComplex, sfWeilSheaf, sfWeilForget,
  sfCommonStageWeilSheaf, sfCommonStageWeilForget, sfWeilStageObject.
* Sheaf.AlgebraicGeometry.ProEtaleSiteComparison: proEtaleSiteComparison,
  proEtaleSiteComparisonModules; the existing CompletedLisse.proEtaleDiagram uses
  the actual coefficient comparison pullback and its limit, not a private site.
* Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules / Mathlib SheafOfModules.
* Sheaf.Paper.NormalizedClassicalWeilRealization: ZlClassicalRealization,
  ZlClassicalPullbackModels, ZlClassicalPullbackStage, zlClassicalModel,
  zlClassicalFiniteUnit, zlCompletedBase, zlRealizationBase, ZlClassicalRealization.weil.
* Sheaf.Paper.LisseAdicAutomorphismPullback: lisseAlgebraicAutomorphismPullback
  and the original normalized rational pullback; no substitute Frobenius functor.

Existing recorded proof modules are imported privately. Four proof dependencies
have no Lean record on the base (separated-finite-type-base-change,
noetherian-finitely-many-components, classical-system-raw-lisse-realization,
sf-pbc-normalized-heart-model); they are not statement prerequisites: the exact
notions needed here are already supplied by the recorded normalized realization
and CompletedLisse interfaces. Their proof steps are retained in the theorem's
complete proof docstring; no extra postponed helper theorem is introduced.

Edge cases checked: I=A=J empty; isolated vertices and no arrows; empty sum, zero
word coefficient and zero maps; rank zero; empty Y and disconnected Y; Frobenius
permuting connected components; rational maps with denominators not preserving
lattices; coefficient enlargement required for an equation or identification;
zeroth and repeated Frobenius pullback. None is excluded by the signature.

Searches performed:

* msearch.py leanfinder: 'A finite diagram of classical lisse adic Weil sheaves with
  equations descends to a finite coefficient field and admits normalized
  constructible heart realizations'. OK, eight hits about affine transition limits;
  none states this result.
* msearch.py loogle: 'CategoryTheory.Functor.FullyFaithful,
  CategoryTheory.Limits.IsFiltered'. Zero hits; the latter name was unknown.
  The actual FullyFaithful interface was read directly in the project sources.
* msearch.py grep: 'finite.*[Dd]iagram|[Dd]iagram.*finite', CategoryTheory.
  Twenty hits on filtered categories, finite limits and presieve diagrams;
  none on classical Weil realization.
* rg on lean/WeilConjectures and lean/Sheaf/Paper for finite diagrams, finite Weil
  realization and ZlClassicalRealization found the recorded datum and unrelated
  diagonal-completed/site realization theorems. grep for this node id in
  lean/WeilConjectures found no existing theorem. Thus no existing exact match.

Sources consulted directly: current blueprint latest, thm-zl-real-mixed-by-curves
proof paragraph 1; BS PDF Section 6.8, including the actual 6.8.4 statements;
Stanford L19 PDF pages 2--3, Proposition 1.1.9 (stable lattice and normalized
reductions). The node's source-based assembly is preserved.
No statement dispute, statement correction, dependency repair or new node.

## Second reading by NW

A second in-thread reading compared the node, dependency records and the whole
module. The dispatcher explicitly forbids starting other agents, so this is not
represented as an independent worker's review. The independent maintainer review
remains required.

The first pass's last clause was a tautological uniqueness of an already-given
heart isomorphism. It was replaced by ZlPrescribedWeilLifts, which starts from
an arbitrary given lisse heart Weil object and its actual prescribed module map,
requires exactly the module Weil square, and fixes the realized map of the unique
lift. The finite equation was initially stated only in raw rational systems; the
second pass added its explicit equality in the actual sf heart. It also added
explicit finite connected-component and clopen conclusions and finite/coefficient
lissity conclusions. Coefficient compatibility now uses one Family, with equality
of At and HEq of Along data, plus normalized finite FieldChange comparisons, rather
than unrelated pointwise stage choices. The stage record repeats the precise
existing pinning equations to bind them to the systems of this diagram; it does
not weaken them to endpoint isomorphisms. No new mathematical hypothesis was
introduced in these repairs. All definition data are real and the sole theorem
proof remains sorry.

## Returned delivery repair

The return against immutable head 1ccc04ede444 identified H3: the previous Lean
signature concluded ∃ R, although the prescribed-identification clause and the
filtration consumers use an already given R. This repair replaces that existential
with ∀ R before M and a. It retains ∃ P₀ and ∃ E for the input R. The module
introduction, proof plan, clause table and lean.statement now record that scope.
The mathematical node statement and its accepted split remain unchanged; this
repairs the Lean rendering, not the node statement.

I checked the return's stage/coherence concern against the complete interfaces
ZlClassicalPullbackStage, ZlClassicalPullbackModels, At, PullNormalized, Family,
CompletedLisse.Comparison and CompletedLisse.Operation:

* Start at each E with the existential witness R.pullback_pinning E. Keep its
  finite functor, finite_pullback, completed operation, classical_objects,
  finite_unit, stage, stage_pullback_objects and pinning. These already mention
  precisely the supplied R.functor and R.pullback.
* Choose ONE Family a from LisseRealization.lisse_rational_realization, with
  normalized Along and FieldChange records. At.completion_residues and
  localization_unit identify the coefficient maps. On integral representatives,
  the two At.integral isomorphisms identify the two derived realizations through
  the same scalar extension; the At.fractions rule extends this comparison over
  rationalization. Taking degree zero gives a natural linear isomorphism of
  sheaf realizations. Replace only the stage witness's realization and along
  by a.realization and a.along, and compose its sheaf comparison with that
  isomorphism. There is no requirement that R.models or R.functor equal a choice
  of Family, nor that independently chosen At witnesses be literally equal.
* PullNormalized fixes the Along comparison on integral tensors, with the
  ordinary adjunction unit, then on rational lisse objects by localization.
  Consequently the transported sheaf comparison still satisfies ordinary_unit.
  The unchanged finite_unit and pinning do not mention realization or along.
  The normalized completion maps therefore preserve all the owner's stage
  fields, while the resulting realization/Along fields equal those of a by
  construction. This meets ZlDiagramCoefficientCoherence for an arbitrary R.
* CompletedLisse.Comparison.rationalFullyFaithful and At.fully_faithful identify
  the same rational Hom groups via the linear sheaf comparison, giving
  finite_fullyFaithful. Their fraction and additivity formulas give finite_add.
  Operation.raw_map and finite_unit identify the actual classical reindexing on
  morphisms, yielding classical with the prescribed classical_values. These are
  consequences of normalized models, not additional hypotheses on R.

Thus the two helper records require no data-field changes. The expanded proof
plan explains this transport explicitly, so a future proof must implement it
rather than assume a compatible Family. Coherence of N under E≤E' remains the
coherent scalar-extension comparison already expressed by Family.fieldChange,
fieldComposition and mixed; no equality of integral lattices is asserted.
The advisory to expose the owner's stage body as a structure is a possible
owner refactor; its full defining body remains verbatim in ZlDiagramStage.

Consumer check: lem-zl-classical-weil-filtration-heart-transport's recorded
ZlClassicalFiltrationHeartTransport universally quantifies R, then a filtration
F, a given G and e : (R.weil).obj (F.terms last) ≅ G. The repaired theorem can
be applied to that R and the finite filtration diagram, retaining e for its
unique-lifting clause. lem-zl-curve-restriction-filtration-spectrum uses the
same finite diagram and prescribed lift in its restriction argument; no change
of R or of the given identification is now needed. Both uses hold. These are
the only two other node files naming this item in their dependency lists.
The zero, empty and disconnected cases in the original report remain allowed,
now for every given R; in particular an empty diagram does not choose a new R.

The sandbox node was compared with current main: lean is the sole differing
field. The delivery wrapper rebases the repaired files onto the live base.

## Repair second reading by NW

I reread the repaired signature against the unchanged node and the returned H3.
The formerly existential R is now an input after the derived stalk-unit letI;
M, arrows and equations follow it. The conclusion begins ∃ P₀, ∃ E. All fields
of P₀, the common-stage lissity clause and ZlPrescribedWeilLifts refer to that
input R. I checked the stage/family transport argument above against the owner's
full stage body and normalized comparison signatures, including the dependency
of ordinary_unit on realization and Along. No data field was silently dropped
or generalized. No additional premise was introduced. The normalized Hom
argument supplies the added fully faithful/additive/classical fields for every
R. All other clauses and permitted edge cases match the returned version that
the maintainer accepted. This is an in-thread second reading, not an independent
review by another agent (the dispatcher prohibits spawning agents).

Validation: the prescribed scompile.py compiled the repaired file in both sandbox
and library module modes with exit 0 and no compiler warnings or errors. The
exact lean.statement text and 100-character line limit were checked.
