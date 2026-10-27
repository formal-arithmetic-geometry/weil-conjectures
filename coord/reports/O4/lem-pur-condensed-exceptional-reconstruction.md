## Worker report

This module states `WeilConjectures.CondensedExceptionalReconstruction.condensed_exceptional_reconstruction`.
It constructs the comparison to the exact upstream bounded constructible exceptional functor as
an ordinary adjunction transpose. Its only postponed proof is the main theorem. All auxiliary
definitions have explicit data. No smoothness, purity isomorphism, ambient unbounded pro-etale
exceptional adjoint, or arbitrary lift of derived diagrams is assumed.

The node is unchanged apart from its Lean record and citations of already landed interfaces.
The six new definition nodes below own the normalized presentations, reconstruction context, comparison, scalar normalization and two existing supplied-data interfaces; no dependency node is repaired.

Hypothesis and clause correspondence:

- The prime is `l : ℕ` with `[Fact l.Prime]`. The base `k : Type u` has `[Field k]`,
  `[Fact (ringChar k).Prime]` and `[Fact (ringChar k ≠ l)]`.
- `CondensedERealization.Base k` is the recorded packaging of a scheme with its structure map,
  locally finite type, quasi-compactness, and separatedness. `f` has the recorded `IsOver`
  structure. The supplied `context` and `Family.comparison` quantify over every such pair, morphism, and
  geometric compactification. No algebraic closedness of k is required.
- `Field l` is the canonical universe lift of Q_l, with the transported norm, scalar algebra,
  and degree-one finite-extension structure. `embedding` is the canonical map to `PadicAlgCl l`.
  The integral full category and raw rationalization are `CondensedERealization.Integral` and
  `pbcRationalization`; the completed sheaf is `pbcAdicCompletion`. These use the published
  lifted-coefficient presentation. No new integral or rational category is defined.
- `Omega` is `BoundedConstructible` for `Profinite.padicAlgClRingObj l` pulled to the scheme.
  This is the finite-intermediate-field-valued condensed coefficient, not the naive continuous
  function ring into the closure. `realization` is exactly localization, J_T supplied by the
  recorded `Data`, then `omegaScalar` along `embedding`, restricted using its recorded
  constructible-preservation theorem.
- The compactification is the actual `Compactification f`. `Context.etale` gives the ordinary
  etale proper/open system functor; `Context.brown` its Brown adjunction. The finite right
  adjoints are the recorded `StrictEtaleExceptionalAdjoint` evaluated by `finiteUpper`.
  `brownLevel` uses `Adjunction.rightAdjointUniq` with the evaluation isomorphisms, hence the
  finite-level comparison is counit-preserving.
- `Context.source`, `target`, and `middle` are the recorded ordinary system site adjunctions.
  `SequenceImageBridge` pins the presentation comparisons on underlying sections, ordinary
  mates, and complex localization; its derived direct comparison is the derived adjunction
  mate. `supportSequence` composes these exact proper/open comparisons. Thus the presentation
  change is not a freely chosen natural isomorphism.
- `input` is the actual derived reduction, transported to etale systems. `brownTower` is
  precisely inverse site image of the Brown output of its direct site image. `Conclusion`
  asserts bounded-below transport only for the data in the statement.
- `Datum` supplies L, an actual object of the ordinary derived category of strict pro-etale
  varying-coefficient systems, and all specified phi_n. Indices are n : ℕ with positive exponent
  n+1. The zero coefficient exponent is never included and the first nonzero stage is retained.
- `Datum.Normalized` uses the dependency's actual transition adjoints and quotient cocycle.
  `Datum.Transitions` is the explicit square with those semilinear transitions for every n ≤ m.
- `Datum.Alternative.supplied` retains the actual system isomorphism and its evaluation equation.
  `Conclusion.supplied` requires that very isomorphism, rather than replacing it by an arbitrary
  witness with equal evaluations. `Alternative.single` supplies only r and all level bounds
  `IsGE r` and `IsLE r`. No system-isomorphism hypothesis occurs in this branch. The theorem's
  proof plan constructs it by good truncation of ordinary cohomology systems.
- `Datum.BoundedConstructible` gives one common pair of integral bounds and the existing
  intrinsic finite-stratification constructibility predicate at each level. No common
  stratification is imposed. `Datum.Reconstructs` requires integral membership of the actual
  `coefficientSequenceLimit` output and invertibility of the actual reduction/limit counit.
- `Datum.proCounit` is the transported ordinary Brown counit after applying theta.
  `sequenceCounit` writes it in the ringed sequence presentation; `integralCounit` applies
  the actual total right derived limit and inverse reconstruction unit. `condensedCounit`
  localizes, realizes, extends to the closure, and inserts the inverse specified coefficient
  projection and compact-support inclusion comparison. `comparison` is literally its
  `homEquiv` transpose under the exact upstream constructible adjunction.
- `Conclusion.invertible` asserts this particular comparison is invertible. `Conclusion.iso`
  packages that same hom; an abstract isomorphism of the endpoints is not substituted.
- `AtCompactification.naturality` uses an integral map b and an actual derived-system map a
  commuting with the Brown identifications (`SystemMap`). `singleDegreeMaps` says that if both
  systems lie in the same r, their level squares alone imply that system square.
- `Family.refinement` uses the existing whole-system `systemRefinement`. Its first equation
  specifies the transported counit and the comparison of the two actual reduction adjunctions.
  The second equation compares the reconstructed isomorphisms through `exceptionalRefinement`,
  the actual ordinary counit mate of the existing intrinsic condensed compact-support
  refinement. Limits carry the same system map; no arbitrary integral comparison is supplied.
- `RealizationProperties.regular_mem` and `coefficientUnit` give U of the explicit regular
  completed module in degree zero isomorphic to the condensed regular unit.
  `coefficientInclusion_normalized` fixes the pre-transpose map on every section to the
  composite coefficient inclusion. `coefficientUnit_normalized` fixes the displayed unit
  isomorphism to its transpose through `normalizationAdjunction` and the recorded comparison
  with U. This is tensor multiplication (b tensor a maps to b times the image of a).
  `shiftClosed` restricts the actual ambient shift, and `shifts_normalized` fixes every
  component of `shifts` to `normalizationModel.commShiftIso` transported through the
  recorded scalar comparison. There is no bare Nonempty unit/shift comparison.

Dependency declarations used:

- `Sheaf.Paper.CondensedERealization`: `Base`, `Integral`, `Rational`, `Coefficient`, `At`,
  `Data`, `Base.map`, with the full scalar-extension and coefficient normalization interfaces.
- `Sheaf.Paper.PbcRationalCategory`: `pbcRationalization` and the actual integral scalar action.
- `Sheaf.Paper.IntegralUniformCoefficient` / `BoundedConstructibleComplete`:
  `PbcIsBoundedConstructibleComplete`, `PbcBoundedConstructibleComplete`, `pbcAdicCompletion`.
  The convenience specialization at E : Type (u+1) is not a second integral notion; this module
  follows `CondensedERealization`'s canonical ULift presentation.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`: `CoefficientDerivedSystemCalculus`,
  its reduction, adjunction and actual `coefficientSequenceLimit`.
- `Sheaf.Paper.FiniteCoefficientAdjointComparisons` and its public ordinary-system interfaces:
  `StrictEtaleCompactSupport`, `StrictEtaleExceptionalAdjoint`, finite evaluation adjoints.
- `Sheaf.Paper.EtaleTowerBrownAdjunction`: `EtaleTowerBrownAdjunction`.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`: `CoefficientSystemDerivedImage`, its
  system and finite-level inverse/direct comparisons and specifying adjunctions.
- `Sheaf.Paper.ExceptionalSystemTransport`: `ExceptionalProEvaluation`,
  `ExceptionalProCompactSupport`, `ExceptionalSystemSiteComparison`,
  `ExceptionalSystemCompactificationComparison`, `exceptionalSystemOriginComparison`.
- `Sheaf.Paper.ClopenStrictSystemComparison`: `ClopenProEtaleSystem`,
  `ClopenSequenceRealization`, `ClopenSystemComparison`, `clopenSystemRing`,
  `clopenSystemUniformizer`; these are the published normalization-preserving presentations.
- `Sheaf.Paper.CompactSupportCondensedRealization`: `RealizationAt`, `integralSupport`,
  `omegaMap`, `omegaScalar`, `omegaScalar_preserves`, `omegaProjection_isIso`,
  `systemRefinement`, `fieldRefinement` and their exact canonical normalization.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`:
  `boundedConstructibleUpperShriekOfCompactification` and
  `boundedConstructibleUpperShriekOfCompactificationAdjunction`.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible` and the public finite-system interface:
  `intrinsicFiniteTorsionConstructible` uses the recorded intrinsic sheaf predicate.
- Mathlib `CategoryTheory.Adjunction.rightAdjointUniq`, `leftAdjointUniq`,
  `conjugateEquiv`, actual derived localization, and full-subcategory inclusions.

The recorded `det-sp-unique-adjoint-coefficients` module was retired in this checkout;
its generic mate formula is already the Mathlib `conjugateEquiv`/ordinary adjunction mate
used here. No finite-global-field restriction from that historical convenience statement
is imported into the arbitrary-k assertion. No new coefficient mate notion is introduced.
The proof-only assembly lemmas without a current Lean record are listed in the main
proof docstring rather than invented as hypothetical black-box assumptions.

Sources read: current blueprint `sk-prop-sp-integral-adjunction` Hom-bijection proof,
`sk-prop-sp-rational`, `sk-thm-sp-qbar` filtered Hom-colimit proof, and
`sk-thm-purity-transport` Steps 2–3, together with the current upstream `UpperShriek.lean`
construction and its explicit composite adjunction. No SGA route is used.

Edge cases checked: arbitrary positive prime characteristic different from l; l=2;
empty schemes and zero complexes; first positive coefficient level and identity quotient;
all negative/zero/positive shifts; single degree r arbitrary in ℤ; the supplied and
single-degree alternatives overlap without discarding the supplied map; actual system maps
beyond componentwise maps; identity and successive refinements. Site object universe u+1,
morphism universe u and coefficient universe u+1 remain unchanged. The Q_l universe lift
is canonical, not an extra field-extension hypothesis.

Searches: the saved `searches.jsonl` records actual msearch calls: LeanFinder for normalized
ordinary exceptional-tower reconstruction (8 unrelated condensed adjunction results),
Loogle `CategoryTheory.Adjunction.rightAdjointUniq, IsAdicComplete` (0 hits), Mathlib grep
`condensed.*[Ee]xceptional|[Ee]xceptional.*[Rr]econstruction` (0 hits), and LeanSearch for
reconstruction of normalized coefficient systems as the condensed exceptional inverse image
(8 unrelated normalization/condensed sheaf results). Source and `lean/Sheaf` rg with the
same pattern found no theorem for this comparison; the upstream blueprint-id grep found
no declaration. The target's proof docstring mentions the item but does not state it.

No statement correction or STATEMENT-DISPUTED finding is proposed.

## Second reading by O4

Author self-check for direct delivery; the maintainer supplies the independent review.
I reread the node and all clause-bearing records against the module. The initial scratch
draft omitted the theorem, its unit/shift clauses and refinement equations; these are now
explicit. I replaced an existential-only rendering of alternative (a) by a data-bearing
sum so the supplied theta is retained verbatim. I removed a placeholder constructibility
clause and used the published intrinsic finite-torsion predicate. I retained the actual
ordinary counit through all presentation changes, total limit, raw localization and closure
scalar extension. The comparison's target and specifying adjunction are exactly the current
upstream bounded constructible functor. Compilation and delivery checks follow below.

## New nodes

`def-pur-exceptional-reconstruction-context` records the normalized ordinary Brown/site/sequence
context used by the theorem. Its module is
`Sheaf.Paper.ExceptionalReconstructionContext`. The construction is sourced to the current
blueprint integral-adjunction proof. It reuses the landed reduction, finite adjunction, Brown,
site and sequence-presentation interfaces, adding the section/mate/localization equations
that pin down their presentation transports. The actual graph helper `sectionValue` states
HEq of the input section and its mapped value; all these section types have the same
coefficient universe. `complexSquare` and `localizationSquare` spell out the termwise map
and its localization equation. Definitions contain real data, and no theorem is postponed
in this module. Splitting this notion lets its checked construction be imported within the
per-file compile budget. LeanFinder returned eight unrelated module-presentation results,
Loogle and Mathlib grep returned zero matches; DAG and project searches found no existing
context. The searches are recorded in its `mathlib_searches`.

`def-pur-exceptional-reconstruction-presentations` owns the canonical lifted Q_l field,
its realization U and the termwise/section/localization normalization predicates. Its module
is `Sheaf.Paper.ExceptionalReconstructionPresentations`. These are the representative
constructions used by the context node, with the same source and searches. The extra
LeanSearch returned unrelated ring-localization results and generic derived-category
primitives; no existing normalized strict-system presentation context. The context module
owns `SequenceImageBridge` and `Context`; the comparison module owns the supplied-system
data and actual counit, while the main module states the theorem and its compatibility clauses. All five modules are checked separately.

The second reading also covers both new definition modules: the field is the canonical
universe lift, U is the displayed scalar-extension composite, and the ordinary section,
complex-localization, ordinary-mate and derived-mate equations are retained. The generic
pasting helper composes the very same proper and open presentation isomorphisms; it
introduces no new comparison choice. All section/complex maps are real constructions.

`def-pur-exceptional-reconstruction-comparison` owns the supplied-system datum, its
actual Brown, integral, rational and closure-valued counits, their adjunction transpose,
and the alternatives and conclusion records. Its module is
`Sheaf.Paper.ExceptionalReconstructionComparison`. The context and the existing
compact-support realization and exact upstream adjunction supply every operation;
all definitions have real data. It separates this canonical construction from its
invertibility theorem so each file meets the compile budget. New LeanFinder and
LeanSearch searches returned only generic condensed/ModuleCat adjunctions; Loogle
and Mathlib grep returned zero hits. DAG and project searches and reading the three
nearby reconstruction/refinement nodes found properties of other counits or theorems
about these maps, rather than this canonical construction. The main theorem now
imports this definition module and owns naturality, refinement, unit/shift clauses.

The final compatibility equations are named `ComparisonNaturality`,
`SingleDegreeCompatibility` and `RefinementCompatibility`; the result records retain
these exact predicates. Splitting their full equations out of the dependent record
fields avoids repeated kernel normalization without adding any mathematical input.
The five modules contain one postponed theorem in total, and no postponed definition.


`def-pur-exceptional-system-transport-interfaces` and
`def-pur-etale-tower-brown-adjunction-data` are existing declaration owners (no new Lean
module). Their precise content, sources and searches are described in repair point 2.
`def-pur-exceptional-realization-normalization` owns the new normalization module; its
construction, blueprint sources, complete search results and lack of an existing generic
U-specific normalization are described in repair point 3. All three are definition nodes,
with actual constructions or records of supplied data, and assert no new theorem.

## Repair of return L at immutable head 9f276d01b612

1. **F1 / H3, fixed comparison rather than its sign class.** The theorem now universally
   takes the supplied `CompactSupportCondensedRealization.ComparisonFamily C`, the supplied
   family `context` of `Context` records, and the equality `hcontext` identifying its
   reduction package with C's. `Family` is indexed by these inputs; it contains no
   existential context field. `specifiedSupport` transports precisely
   `(C.coefficient (Field l)).atCompactification` along that equality. `AtCompactification`
   takes this support realization as a parameter, instead of selecting one in its witness.
   Thus the `RealizationAt.realization`, both reduction adjunctions, and all site/sequence
   adjunction units and counits are fixed before the result is asserted. Twisting one of
   these packages changes an input, so does not supply -c for the same inputs. The constructed
   `Datum.comparison` still uses the exact upstream UpperShriek adjunction and the unchanged
   presentation, origin, and localization equations. The downstream
   `def-pur-condensed-smooth-purity-iso` can apply the theorem to its specified C and context
   and obtains that comparison, rather than choosing a sign from an existential package.

2. **F2 / H2, definition owners.** Added
   `def-pur-exceptional-system-transport-interfaces` with `existing: true` in
   `Sheaf.Paper.ExceptionalSystemTransport` for the ordinary pro-etale support, site,
   compactification and origin-comparison definitions, and
   `def-pur-etale-tower-brown-adjunction-data` with `existing: true` in
   `Sheaf.Paper.EtaleTowerBrownAdjunction` for the supplied Brown-data interface. These
   introduce no duplicate Lean definitions and assert no existence theorem. The item and
   the new definition-node statements now cite those owners rather than the existence
   theorems whose modules merely supplied the definitions. The genuine compact-support
   realization dependency stays: its constructible preservation, flatness and projection
   assertions type the statements and normalization. Added
   `def-pur-exceptional-reconstruction-presentations` directly to the item's statement
   dependencies as requested. The Brown existence theorem remains its original proof
   dependency and proof-plan step; its statement is not imported as an assumption.

3. **F3, canonical unit and shifts.** Added
   `def-pur-exceptional-realization-normalization`, module
   `Sheaf.Paper.ExceptionalRealizationNormalization`. It constructs the composite ambient
   scalar model, ordinary and derived restrictions, their original adjunction and exact
   composition comparisons, the recorded comparison with U, the sectionwise coefficient
   inclusion predicate, and the derivation of a specified ordinary inclusion. The coefficient
   unit in `RealizationProperties` is data with an equation: its image under the original
   composite scalar adjunction is exactly that derived inclusion. The latter is fixed on
   every section to the completed-to-rational inclusion followed by the actual closure
   coefficient map. This pins the unit to tensor multiplication, not its negative. The
   ambient model's `CommShift` is explicitly the derived scalar-adjunction structure,
   the exact inverse-encoding structure, and the exact-derived closure-extension structure.
   `shifts_normalized` pins every hom component to that canonical CommShift transported
   through the recorded model/U comparison. All integer shifts, including zero, retain
   those exact maps. These are conclusion equations, not added mathematical hypotheses.

The added normalization node was searched via LeanSearch (eight generic module scalar-
extension/tensor results), Loogle (zero combined CommShift/homEquiv results), Mathlib grep
(zero matching predicates), blueprint_refs (zero matching nodes), and project rg (only an
unrelated normalizationModelBaseChangeMap). The existing Tate-specific ambient scalar
model is a construction pattern, but concerns a different fixed rational embedding and
Tate input; the new helpers specialize the same generic derived APIs to the U in this node.
The two new existing-interface owners were searched via LeanSearch (eight generic sheaf
adjunction results), Loogle (twelve generic mate results), Mathlib grep (zero interface-name
hits), blueprint_refs and DAG declaration-owner rg (no definition owners). Their existing
source definitions are used verbatim. Actual tool summaries are in the nodes' mathlib_searches.

All original edge-case and clause checks continue to apply. There is still exactly one
postponed theorem. No node statement correction is needed: the repaired signatures retain
supplied choices as inputs and specify the maps already required by the natural-language
statement. The maintainer's independent review supplies the second reading.



Repair validation: `scompile.py` checked all five delivery modules individually against
live sources. The final run `repair-full-compile2.log` passed without errors or warnings:
presentations, context, comparison, realization normalization and main statement.
The earlier unit normalization elaboration exposed the distinction between a raw
HomologicalComplex.single and the canonical CochainComplex/DerivedCategory single;
`regular` now uses the canonical `DerivedCategory.singleFunctor` in degree zero, with
the same completed regular module. No arbitrary comparison is inserted.
