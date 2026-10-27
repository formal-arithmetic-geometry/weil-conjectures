## Worker report

The module `Sheaf.Paper.IntegralSectionsPerfectReduction` states
`WeilConjectures.integralSections_perfect_reduction`, with `sorry` as its only
postponed proof. It retains the actual recorded integral ordinary and compact section
values. Their return types already assert boundedness, finite generation of every
cohomology module, and derived completeness, by `DerivedCategory.pointFgComplete`.
No tautological repetition of that membership is added to the theorem.

Hypotheses and clauses:

- `D : FiniteFieldDatum.{u}` supplies precisely the fixed finite field and its
  algebraic closure `D.k`, of characteristic `D.p`. `[Fact l.Prime]` and `hl : l ≠ D.p`
  give the coefficient prime. The field, algebra and finite-dimensional instances on
  `E : Type u` give the finite extension of the p-adic coefficient field.
- The valuation ring, uniformizer, ideals and quotients are the recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing`. The quotient index `n : ℕ` in this module means
  exponent `n + 1`, hence covers exactly every exponent ≥ 1, including the residue field.
- `X : Scheme.{u}` and `[X.Over (Spec (.of D.k))]` supply the scheme and structure map.
  `LocallyOfFiniteType` plus `QuasiCompact` is finite type; `IsSeparated` is separatedness.
  There is no properness, smoothness, nonemptiness, dimension-equality or geometric
  descent hypothesis. The compactification `c` is arbitrary, as in the recorded
  compact-support definition; it does not restrict the allowable schemes.
- `d : ℕ` gives the nonnegative integer dimension bound; `_hd` is
  `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. This permits the empty scheme, of dimension ⊥.
- `K : sfIntegralConstructibleCategory l E X` is the recorded derived-complete,
  intrinsically constructible integral object. Its ambient category is
  `scalarReductionSource.{u,u}`, over the **completed** coefficient sheaf.
- `_hTor` says that every `scalarReductionDerivedExtension` of `K.obj` has the SAME
  specified interval `[a,b]`, using `HasProEtaleTorAmplitude`. The predicate includes
  the ordering of the interval, so no extra ordering assumption is added.
- `integralOrdinarySections ... K` and `integralCompactSections ... c K` are exactly
  the recorded ordinary and compact `C_*` and `C_!`. Both are objects of the
  `pointFgComplete` full subcategory, whose definition was read in full; this accounts
  for the bounded, finitely generated, derived-complete conclusion.
- The two `IsPerfectRingComplex` conjuncts assert perfectness in their recorded
  module localization: bounded finite projective representatives, with the original
  coefficient ring and its scalar action.
- `IsIso (sfOrdinarySectionsReductionComparison ...)` and its compact counterpart
  assert isomorphy of the specified coefficient comparisons in the quotient-module
  derived category. These are actual arrows, not unrelated existential isomorphisms
  or a statement only about cohomology groups.
- The final quantifier selects exactly the two section values, by its equality
  disjunction. `P.IsStrictlyGE a` and `P.IsStrictlyLE (b + 2 * (d : ℤ))` give termwise
  vanishing outside the required SINGLE interval. `Module.Free` and `Module.Finite`
  for every `P.X i` give finite free terms. The `Nonempty` derived isomorphism identifies
  this complex with the actual derived quotient tensor of the corresponding section
  value. Neither a, b nor d depends on n.

Canonical maps and size conventions:

The ordinary projection retains the very Roos realization chosen inside `integralImage`.
The compact projection retains the defining Roos triangle of the actual
`sfIntegralCompactSupportValue`. Their vertices are determined up to isomorphism
preserving the defining projection. Definitions choose no unrelated map or scalar action.
Sections of each n-th projection, followed by the identity-on-sections restriction
comparison, have a unique adjunct for the normalized module tensor/restriction
adjunction. This adjunct is the coefficient arrow. The adjunction has the actual
unit `x ↦ 1 tensor x`, via `pointUnitIntegralModuleAdjunction`.

The packaged section values use small module localizations, whereas the published
`pointReductionModuleTensor` uses the standard localization. `sfSectionsCoefficientLift`
is the functor of Mathlib's canonical `Localization.uniq` equivalence. Its normalization
on cochain complexes is `Localization.compUniqFunctor`. The exact-section comparison
is constructed by `Localization.liftNatIso` from this normalization and the existing
`Functor.mapDerivedCategoryFactors`; it is not postulated. The coefficient arrows
precompose the tensor adjunct with that canonical integral-section comparison.
The finite sections already use the standard quotient-module localization, so no
finite-value transport is needed. Coefficients, scalar maps,
module carrier size, and input objects are retained. No universe equality is assumed.

Dependency declarations read and used:

- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, with an independent localization universe.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its category.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, `sfDirectImageTerm`,
  `sfDirectImageTransition`, and the recorded canonical derived direct images.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and its canonical coefficient data.
- `Sheaf.Paper.FiniteTorAmplitudeSites`, which publicly retains `FiniteTorAmplitude`:
  `finiteTorConstructibleIntegral` and its constituent `HasProEtaleTorAmplitude`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension` and `scalarReductionDerivedRestriction`.
- `Sheaf.Paper.QcqsCompactSupportRealization`, through the recorded ordinary/compact
  cohomology module: the original `sfIntegralCompactSupportValue` and its defining tower.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, publicly importing all original ring constructions.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`, publicly retaining
  `OrdinaryCompactCohomology`: `integralImage`, `integralOrdinarySections`,
  `integralCompactSections`, `finiteOrdinarySections`, and `finiteCompactSections`.
- `Sheaf.Paper.PointFgCompleteComplexes`: `DerivedCategory.pointFgComplete`.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration;
  its finite-type and separatedness conventions are the Mathlib classes used above.
- `Sheaf.Paper.PointReductionUnits`: `pointUnitIntegralModuleAdjunction` and
  `pointUnitIntegralDerivedSectionsRestrictionIso`. Its owning existing node is added
  to `stmt_deps` because the statement names the resulting actual canonical arrows.
- `Sheaf.Paper.PointSectionsDerivedReductionData`: `pointReductionModuleTensor`.
  Its owning definition node `lem-pod-point-sections-derived-reduction-data` is
  added to `stmt_deps`, and the data module is publicly imported for the ordinary-module
  tensor used by the signature. `Sheaf.Paper.PointSectionsDerivedReduction` remains
  a plain proof import for `lem-pod-point-sections-derived-reduction`; its theorem
  `point_sections_derived_reduction` is unused in the statement and helper definitions.

All proof-dependency modules with recorded bindings are imported. The proof-only node
`lem-sf-point-tor-amplitude-realization` has no Lean binding in the current DAG, so
there is no module to import for it; its full role remains in the theorem's proof
plan. No missing statement notion is replaced by a hypothesis. The new helpers are
only the projection-retaining and canonical localization/map constructions of this
item, and are listed in its `lean.declarations`.

Edge cases checked against the source and types: empty X; zero K; d = 0; a = b;
negative a and b; n = 0 representing exponent 1; nonproper X; torsion integral
objects such as R/ϖ. Strict degree bounds and Module.Free allow zero terms, so the
zero/empty cases are retained. There is no independent test-object universe that
could make the Tor hypothesis vacuous. The only coefficient lifts are the existing
ULift coefficient-size convention and the canonical equivalence of localization models.

Searches (all via the prescribed msearch wrapper where applicable):

- LeanFinder: “Integral constructible cohomology and compactly supported cohomology
  are perfect with uniform finite free derived reductions”: 8 results, including
  continuousCohomology and condensed-module declarations; none is this statement.
- Loogle: `DerivedCategory, "perfect"`: 0 results.
- Mathlib grep: `integral.*[Ss]ections.*[Pp]erfect|[Pp]erfect.*[Rr]eduction`: 0 results.
- LeanSearch: “Integral cohomology and compact support cohomology over a complete
  discrete valuation ring are perfect and commute with derived quotient reduction”:
  8 results about perfection of rings, valued local fields, and adic completeness;
  none states this cohomology theorem.
- Project rg: `integralSections|integral.*[Pp]erfect|[Pp]erfect.*[Rr]eduction|IntegralSections|integral-sections-perfect-reduction`
  in `lean/Sheaf/Paper` and `lean/WeilConjectures`: found existing point, tensor,
  completion and perfectness tools, but no declaration of the required combined result.
- Exact blueprint-id search in `lean/WeilConjectures`: no match.
- Project rg for each new helper and main declaration name: no existing declaration.

No statement correction, disputed statement, new DAG node or dependency rebinding is
needed. The two added statement dependencies are already landed; their dependency
closures were checked to contain no path back to this item.

Validation: the final module passes scompile.py in both sandbox and library module
modes, with no errors or warnings (32.6 s and 15.7 s respectively). The delivery
dry run passed server preflight and per-file compilation (commit 11115ee11db).

## Repair of returned delivery

The independent review of head `66fff8957a26` returned H2: the statement used only
`pointReductionModuleTensor`, owned by the existing definition node
`lem-pod-point-sections-derived-reduction-data`, rather than the conclusion of
`lem-pod-point-sections-derived-reduction`. Replaced that added statement dependency
with the data node and publicly imported `Sheaf.Paper.PointSectionsDerivedReductionData`.
The theorem module remains a plain import because the original proof plan cites it.
The data node's declaration list and the full tensor definition were checked in the
current main source. Comparison of the saved packet with current main found only the
intended `stmt_deps` additions and the new `lean` record; all original node fields agree.
The saved packet first passed a fresh dry run (`b4cbd680d94`), before this explicit repair.

Self-check: the Lean change affects only these imports. The theorem signature and all
helper bodies remain those independently accepted in the return. The added dependency
now owns precisely the tensor definition used in the statement. No theorem conclusion
is being used as a statement notion; no dependency record or mathematical statement changes.

Repair validation (2026-10-22): scompile.py passed the repaired module in sandbox
and library modes (31.1 s and 29.2 s), with no errors or warnings. The self-check
confirmed the verbatim recorded signature, unchanged original node fields, exactly the
two authorized added definition dependencies, one theorem sorry, explicit autoImplicit
false, and Lean lines at most 100 characters.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
