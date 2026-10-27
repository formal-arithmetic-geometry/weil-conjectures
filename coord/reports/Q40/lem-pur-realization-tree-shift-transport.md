## Worker report

The module `Sheaf.SixFunctors.RealizationTreeShiftTransport` states
`WeilConjectures.IntegralSystemRealization.realizationTreeShiftTransport` with one
`sorry`, exactly the postponed conditional theorem. All helper definitions have real data.
The original node statement, proof and proof dependencies are unchanged.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field, characteristic p | `D : FiniteFieldDatum.{u}`; base `Spec (.of D.k)` |
| Prime ell different from p, finite extension of Q_ell | `l`, `[Fact l.Prime]`, `_hl : l ≠ D.p`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| Valuation ring, uniformizer, positive quotient coefficients and completed sheaf on the small pro-etale site | The recorded `calculus l E W`, `System l E W`, `Integral l E W`, `inputReduction` and `coefficientSequenceLimit`; these use the actual coefficient-extension rings, fixed uniformizer and positive-level sequence site. |
| Ordinary unbounded derived systems and actual reduction/limit adjunction | `CoefficientDerivedSystemCalculus.reduction` and `.adjunction`, through the published `calculus`; no new category, functor, unit or counit |
| Pull, proper push, quasi-compact open extension, tensor, integral counterparts | `o : Operations l E`, the existing `Expression`, `systemInterpretation`, `integralInterpretation`; compact support remains its open/proper composite |
| Finite-type k-schemes and separated finite-type inverse-image maps | `e.val.geometric` and `t.val.geometric`; all schemes and maps are over the fixed base, with the stored proper/open constructor witnesses |
| Normalization, compatible etale origins, constructibility and common finite cohomology/Tor bounds at every intermediate, including hidden open intermediate | Existing `Expression.domain`, `Good`, `Origins`, `LevelBounds`, `Expression.admissible`. Inputs are the full subcategory of this predicate. |
| Derived-complete constructible integral inputs | `Expression.domain` requires `sfIntegralConstructible` at every input |
| Fixed cochain shifts, signed second tensor slot, strict-tower Roos limit | `systemShifts`, `integralShifts`, `reductionShift`, `limitShift`, `tensorShifts`; `sourceShift` and `integralShift` are the dependency's actual recursive comparisons. The dependency's `limitShift_roos` fixes their strict-tower representative normalization. |
| Finite independently indexed leaf occurrences; disjoint children at tensors | `IndependentExpression`, whose occurrence-label map is bijective. Equal input values are allowed. |
| Actual canonical c_V | `R : Realizations l E D o` and `R.comparison`; never an arbitrary endpoint isomorphism |
| Assume inverse-unit and unary/binary insertion squares, naturally for every integer | `_hInsertion : RealizationAdjunctionInsertionShift l E D o R`. This predicate names the actual `Recursion.pullA`, `properA`, `openA`, `tensorA`, inverse unit, and both designated tensor slots, with naturality. It is assumed; its theorem is not used. |
| Assume the actual leaf/unary/binary realization recursion | `_hRecursion`, using exactly `Recursion.Equations R R.comparison` for every `Recursion.BasicTree`. The compact-support constructor uses `R.supportRecursion`, the already specified open/proper composite. |
| Each leaf i and each integer r, full domain stable | First conjunct: `∀ ... (i : I) (r : ℤ), ∃ h : e.val.domain ... (Function.update K.obj i ((K.obj i)⟦r⟧)), ...`. The existential retains all new intermediate domain witnesses and hence translated common finite bounds. |
| chi_integral c_shifted = shifted c chi_source | First conjunct's equality: shifted comparison followed by `e.integralShift`, equals `e.sourceShift` followed by shifted original comparison (Lean uses diagrammatic composition). |
| Naturally in the entire input family | `R.comparison` is a natural isomorphism on the actual full domain; `sourceShiftIso`/`integralShiftIso` and the dependency's `shift_naturality` identify the used components as natural in all inputs, including spectator tensor operands. No pointwise arbitrary shift maps enter. |
| A collection of specified system generators | `G : TreeGenerators ... R`, selecting witnesses of the published `SynchronizedBasic` relation. `TreeSynchronizedPair G` is the generated subrelation, with the original identity, composition and expression-context constructors, a membership witness only at basic generators, and injectivity of intermediate labels in compositions (the statement requires independently indexed occurrences throughout). |
| Assume selected generators' system shift square and actual integral intertwining | `_hGenerators : TreeGeneratorShiftLaws ... G`: system equality before total limit and the two equations `L(s)c_T=c_V v` at the old/new families. Since c is an iso, these are exactly the stated conjugation formula. The integral square is not assumed. |
| Every finite composition and unary/binary context | Second conjunct quantifies every `TreeSynchronizedPair G` witness, including actual intermediate geometric/admissibility witnesses at both families. Contexts preserve the selected tensor side. |
| Both system and integral squares; same intertwining | `TreeMapTransport`: its first equality is in `System` before total limit; its second is the integral square; its third/fourth are the actual realization intertwining at both families. |
| Several independent input changes factor as single-slot changes | Third conjunct quantifies `q : List (I × ℤ)` with distinct first components. `treeShiftInputs` is the ordered dependent update; `treeSourceShifts` and `treeIntegralShifts` are real recursive composites of the same single-slot comparisons. Its equality is the corresponding finite composite realization square. |
| Conditional, asserting no local square | All insertion/generator laws are explicit theorem arguments. No insertion or generator theorem is applied to remove these hypotheses. |

The helper `treeSubexpressionShift` handles a needed typing detail without restricting
subtrees to use every global label: it follows the dependency's explicit successful
`variableContext` search, with equality witnesses identifying its old/new endpoints.
The local-generator law allows injective label maps, so unused global labels do not
prevent its application inside tensor contexts. These are equalities of actual
objects, not arbitrary isomorphisms supplied as extra mathematical assumptions.

Dependency declarations read and used:

- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, inherited `reduction` and `adjunction`,
  `coefficientDerivedSystemEvaluationCalculus`; actual `calculus` interface is
  inherited through the operation package.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `Realizations`, `Expression.systemObj`, `Expression.ringedObj`, `comparison`,
  `supportRecursion`, `completionIso`, and the underlying canonical/basic pairs.
- `Sheaf.SixFunctors.IntegralOperationShiftData`:
  `TensorShifts`, `tensorShifts`, `systemShifts`, `integralShifts`, `reductionShift`,
  `limitShift`, `Expression.SlotContext.shift`, `IndependentExpression.sourceShift`,
  `integralShift`, `sourceShiftIso`, `integralShiftIso`, `limitShift_roos`.
- `Sheaf.SixFunctors.IntegralRealizationRecursion`:
  `Recursion.Equations`, `BasicTree`, `ComparisonFamily`, the actual insertion maps.
- `Sheaf.SixFunctors.IntegralExpressionOccurrences`:
  `IndependentExpression`, `variableContext`, `variableContext_evaluate`, `inputShift`.
- `Sheaf.SixFunctors.SynchronizedCanonicalMaps`:
  `SynchronizedBasic`, `SynchronizedPair` and all its constructors, read to define
  only the subrelation generated by a selected collection, without new operations.
- `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift`:
  `RealizationAdjunctionInsertionShift`, `InsertionShiftLaw` and the five fixed-comparison
  helpers. Their new definition node
  `def-pur-realization-adjunction-insertion-shift-data` is cited in `stmt_deps`.
  The insertion-shift theorem node is not a statement dependency and its theorem
  is not used; no dependency record changes.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: existing finite-Tor category predicates.
- Proof-only dependencies: `SfIntegralConstructibleTriangulated`
  (`sfIntegralConstructible_isTriangulated`), `NormalizedDVRTower`
  (`NormalizedDVRTower`), `FixedEtaleOriginWitness` (`FixedEtaleOriginWitness`),
  `ProEtaleTorIntervalShift` (`coefficientProEtaleTor_interval_shift`), and
  `IntegralSystemExpressionDomain` (`Good`, `Origins`, `LevelBounds`, `domain`).

Edge cases checked before and after drafting: a single leaf gives the inverse-unit
square; repeated object values have distinct independent labels; no expression over
an empty leaf type exists but the quantification is valid; zero objects/empty opens
use the existing operations and impose no nonzero or nonempty hypothesis; r=0 and
negative r remain allowed; the signed right tensor comparison is used without
symmetry; an unchanged other operand is covered by naturality; unused labels are
allowed at local generators; the empty collection gives only identities/contexts;
the empty list gives the original comparison; singleton and two distinct updates
are the displayed single-slot composition. Every finite coefficient level is indexed
as n+1 by the existing construction; no n=0 quotient is introduced.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query "Recursive realization comparisons of finite unary
  tensor expression trees commute with independent leaf shifts and transport
  synchronized canonical maps": 8 hits, on TensorPower casts and first-order term
  realization; none is this statement.
- `msearch.py loogle`, `CategoryTheory.NatTrans.CommShift`: 12 hits, generic shift
  structures/composition; none includes the actual system realization/domain.
- `msearch.py grep`, `CommShift|commShift`, `CategoryTheory/Shift`: 25 hits, generic
  shift interfaces, no expression-tree realization statement.
- `rg` in both live `lean/WeilConjectures` and `lean/Sheaf`, and upstream name index,
  for the item ID, realizationTreeShiftTransport, TreeInsertionSquares: no exact match.
  The existing IntegralRealizationShiftCoherence theorem was read in full. It proves
  the unconditional global theorem for all canonical maps, so it is not the conditional
  local-generator induction principle requested here, and it is not imported.
- For selection/closure helpers, `msearch.py leansearch`, query "Generated closure of
  a selected subset of synchronized natural transformation generators under
  composition and unary binary expression contexts": generic HomRel.CompClosure and
  multiplicative closures only. `loogle CategoryTheory.HomRel.CompClosure` confirms
  it closes parallel-arrow relations under arbitrary compositions, not the typed
  four-map synchronized relation with expression contexts. `msearch.py grep`
  `Synchronized|SelectedGenerator|GeneratedPair` in CategoryTheory: zero hits.
  `rg` of project SixFunctors and DAG plus `tools/blueprint_refs.py search` for
  selected synchronized generators found no selected-subcollection interface.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors/`
`sk-thm-sf-compatibility/fix-prop-coherence.proof.md` in full, plus its unit statement.
It says coherence is inherited from maps on their stated domains. This node is the
reviewed agent-formulated conditional tree obligation, not the unit's own statement.
No statement correction, hollow data or disputed statement is introduced.
The selection/shift/finite-list helpers belong to the statement's own hypotheses and
conclusions, and are listed in lean.declarations with source/blueprint docstrings.

Validation: the final module is checked using scompile.py alone against the live
published library, both the sandbox probe and its actual module path, below 60 s.
The dry run and push are recorded by the delivery wrapper.

## Second reading by Q40

A separate pass by the same dispatcher-started worker reopened the node and final
module. The brief explicitly forbids starting another agent; this is a self-review,
not a claim of independent review. The maintainer's independent review is still due.

The first version assumed laws for all basic maps. I changed this to an arbitrary
selected collection and its generated subrelation, retaining all actual map indices.
The first hypothesis draft also included the generator integral shift square; this
was removed: the local law now assumes only the system square and old/new realization
intertwining, and the integral square is part of the conclusion. I checked subtree
labels separately: they can omit other global labels, so local laws now use injective
label maps and the dependency's successful explicit context search with endpoint
equalities, rather than the root-only bijective-label interface. The full root uses
IndependentExpression as required. I checked composition order in all three main
conjuncts, the strict-system equality before L, both tensor constructors, compact
support's hidden open intermediate and finite-list recursion. The clause table above
was checked against both the unchanged node statement and the final signature.

Final review refinement: composition in the selected subrelation explicitly retains
injectivity of the intermediate occurrence-label map as well as its geometric and
admissibility witnesses. Thus a factorization cannot silently pass through an
expression duplicating an independently supplied leaf. Subtrees may still omit
global labels, as required. No original dependency relation is changed.

## New nodes

`def-pur-realization-adjunction-insertion-shift-data` records the existing predicate
`WeilConjectures.IntegralSystemRealization.RealizationAdjunctionInsertionShift` in
`Sheaf.SixFunctors.RealizationAdjunctionInsertionShift`, with `existing: true` and
`lean.note`. No predicate is copied and no new Lean module is needed. The helper
names recorded with it are `insertionCompositeShift`, `InsertionShiftLaw`,
`insertionLimitShift`, `insertionSourceShift`, and `insertionTargetShift`.
This node replaces the theorem dependency identified by return H2.

Clause correspondence for the new definition: the generic naturality, invertibility,
integer square, and exact zero/addition-coherent comparisons are the four conjuncts
of `InsertionShiftLaw`; the fixed composite comparisons are the bodies of
`insertionCompositeShift`, `insertionSourceShift`, and `insertionTargetShift`.
The six families are exactly the structure fields `unit`, `pull`, `proper`,
`openExtension`, `tensorLeft`, and `tensorRight`. Their binders retain every finite-type,
separated, proper, and quasi-compact open hypothesis. Four unconstrained integer
bounds are quantified in each field. `GeneratorReduction.SystemAdmissible` enforces
the normalized, compatible-origin, constructible cohomology and finite-Tor domain
on every specified input/output, including both tensor operands and output; `unit`
also requires `sfIntegralConstructible`. The actual maps are the inverse-or-zero of
the actual unit, `Recursion.pullA`, `Recursion.properA`, `Recursion.openA`, and
`Recursion.tensorA`. The signed `tensorShifts.systemRight/integralRight` comparisons
are retained. The predicate makes sense for any prime ell and finite-field datum;
it adds no ell-versus-characteristic hypothesis of its own. This is a definition
of the local-square assumption, with no assertion of its inhabitance.

Searches for this definition: LeanSearch and LeanFinder each returned eight generic
adjunction/shift results, not this normalized six-family predicate; Mathlib grep
for `RealizationAdjunctionInsertionShift|InsertionShiftLaw|insertionCompositeShift`
in `CategoryTheory` returned zero hits. `rg` in `WeilConjectures` returned no hits;
`rg` in `Sheaf` found exactly the existing module and its helpers. DAG searches found
only the insertion theorem node, with no definition node owning this predicate.
`tools/blueprint_refs.py search "insertion shift"` returned zero blueprint matches;
its ancestor query gave `thm-pur-rational-and-qbar-purity`. The queries and returned
names are recorded in the new node's `mathlib_searches`.

## Returned delivery repair

Compared with immutable returned head `45a679750f32` and the current main node,
the Lean module and the item's mathematical statement are unchanged. The original
eight dependencies remain, and the additional insertion theorem dependency is
replaced by the definition node above. This is the requested H2 repair; no predicate
is duplicated (H4), and no theorem is added to discharge an assumed local square.

The spectator advisory is resolved by the existing coherence interface, independently
of `TreeGeneratorShiftLaws` and hence without `hc` or `hd`. For a synchronized basic
witness at the two families, `SynchronizedPair.basic` uses the actual completion
isomorphisms supplied by `R.completionIso` at the old and new admissible families.
`SynchronizedPair.components` then gives the two `CanonicalPair` witnesses. Applying
`R.coherence` to each gives exactly the two realization-intertwining equalities.
The integral arrow in these equalities is the same completion-conjugate arrow as in
`TreeGeneratorShiftLaws`: on the domain, `inverseOrZero` of the completion map is
the inverse of `R.completionIso`. Neither `SynchronizedPair.components` nor
`R.coherence` has a variable-context or selected-label hypothesis. The selected
closure forgets to `SynchronizedPair` constructor by constructor, so the same route
works under its identity, composition, unary and tensor constructors. In particular,
a generator in the unchanged tensor operand still intertwines both realizations
even though `variableContext` for the shifted spectator label returns none there.
Its contribution to the ambient system shift square is tensor-shift naturality in
the other operand at this unshifted generator; no additional local square is needed.

Self-review of the repair checked all six predicate fields against the new definition
node, its exact recorded signature, each cited dependency, the existing-only helper
list, and the removal of the extra theorem edge. Zero and negative shifts, empty
domains, and both signed/unsigned tensor slots retain the previous delivery's behavior.
