## Worker report

Module: `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift`.
Main declaration: `WeilConjectures.IntegralSystemRealization.systemAdjunctionOpenMapShift`.
The theorem alone is postponed, with `by sorry`; its docstring supplies all nine
accepted proof steps. All helper definitions have actual data. The helper indices
and predicates package this node's listed maps and domains; no independent
mathematical notion or replacement operation is introduced.

Hypotheses and objects, clause by clause:

- The geometric field, its characteristic p and finite-field origin are the existing
  `FiniteFieldDatum D`. The theorem assumes `_hl : l ≠ D.p`; `[Fact l.Prime]`,
  `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give the prime
  and finite coefficient extension. Its valuation ring, chosen uniformizer and
  positive quotients are those of the imported coefficient calculus, unchanged.
- Finite-type k-schemes are `PrimitiveSystemScheme D`, the published full
  subcategory of schemes over `Spec D.k` with `LocallyOfFiniteType` and
  `QuasiCompact` structural morphisms. Morphisms are arrows over this base.
  `PrimitiveSystemArrow` supplies separated finite-type arrows. Proper arrows
  carry `IsProper`; opens carry `IsOpenImmersion` and `QuasiCompact`.
- `System l E W` is the existing ordinary unbounded derived category of module
  sheaves on the small ringed sequence site. `Integral l E W` is the existing
  ordinary unbounded derived category of completed integral coefficients.
  The module does not form a new derived category, tensor or sheaf universe.
- Normalized systems, common finite cohomological and Tor intervals, and compatible
  retained etale-origin witnesses are exactly `Good l E W`: see its existing
  `IsNormalizedCoefficientSequence`, `LevelBounds`, `Origins` components.
  `systemShiftContextDomain` recursively requires `Good` at the root, each
  intermediate and each fixed tensor operand. Each finite collection of intervals
  may be enlarged to common intervals. Integral inputs use exactly
  `sfIntegralConstructible` through `SystemShiftCorner.good`, with no additional
  integral Tor hypothesis. Unit/counit paths and mate/adjunct paths explicitly
  require these same domain conditions for every object in their formulas.
- Canonical simultaneous models and their actual maps are the recorded
  `Operations`, `Compositors`, `OpenComparisons`. These retain cochain factorization,
  actual derived adjunctions, and section/transpose normalizations; arbitrary
  functors or arbitrary lifts cannot be substituted for the listed operations.
- The fixed cochain shifts are `systemShifts`, `systemPullShift`, `systemPushShift`,
  `systemOpenShift`, `reductionShift`, `limitShift` from the recorded shift-data
  module. In particular the right tensor comparison remains `systemRight` with
  generator sign `(r * i).negOnePow`, and the total limit retains its Roos model.
- The G primitive clause is the `primitive` constructor of
  `SystemAdjunctionOpenGenerator`, which requires the existing
  `PrimitiveSystemComparison` with its actual component family. Thus it includes
  precisely pullback compositors, square identifications, pullback/tensor,
  associator, unitors, Koszul symmetry with its permuted occurrence, open
  composition, restriction, clopen comparison and component projection.
- Units and counits of all three listed adjunctions are indexed by
  `SystemShiftAdjunction`: `direct` uses the actual `(o.direct f.left).adj`,
  `open` uses `(o.extension j.left).adj`, and `reconstruction` uses
  `(calculus l E W).adjunction`. `data` assigns each its published shift structures.
  `SystemAdjunctionOpenShift.unitCounit` asserts both actual component squares.
  Direct adjunctions cover separated finite-type arrows, including proper arrows;
  no properness hypothesis is imposed on inverse image.
- Direct-image compositors use `pushComp`, exactly `c.pushComp` (the adjoint
  conjugate of `c.pullComp`), on proper composable arrows.
- The beta constructor uses exactly `a.beta` on a cartesian square `IsPullback`,
  its commutativity equality, quasi-compact opens, and separated finite-type
  vertical arrows. Its inverse is fixed already by `a.beta_transpose`:
  P_gU(unit) followed by the inverse pullback-square identification.
- The gamma constructors `tensorLeft` and `tensorRight` use exactly
  `a.projection j.left`, separately for M and N. Its inverse is fixed by
  `a.projection_transpose`: tensor(unit, identity) followed by the inverse
  restriction/tensor comparison. Thus no arbitrary isomorphism with these
  endpoints replaces either normalized open map.
- `SystemAdjunctionOpenShift.generators` states the exact component equation
  `τ (M⟦r⟧) ≫ χ_target.hom = χ_source.hom ≫ (τ M)⟦r⟧'` for every `r : ℤ`.
  These maps are the canonical natural maps already recorded; the assertion is
  intrinsic in `System`, with no evaluation or scalar-restriction equality.
  The generator `inverse` covers both normalized open inverses, as well as the
  inverse of any listed isomorphism.
- For the general mate, `SystemShiftFunctor` stores H or T with its fixed
  `CommShift ℤ`. No unit/counit compatibility is assumed in the adjunction-data
  container. `alphaCompatible` is exactly the shift-square hypothesis on alpha,
  on the designated normalized domain. `mates` concludes the square for the
  explicit composite `eta2 ≫ G2.map alpha ≫ G2.map (T.map epsilon1)`, with
  source H G1 and target G2 T. `mateDomain` lists all input and intermediate
  objects, imposing no global preservation hypothesis on H or T.
- `adjuncts` gives both `eta ≫ G.map h` and `F.map h ≫ epsilon` forms. The
  `inverses` field is the cancellation rule for an arbitrary shift-compatible
  isomorphism at the same object and integer shift. The node's separately
  designated tensor slots are covered by its two gamma constructors and by
  choosing H,T with the corresponding compatible shifts.
- The generator has no proper/open interchange, projection mate, exchange square
  or realization constructor. No integral expression-realization assertion is
  part of the conclusion.

Dependency declarations read and used:

- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, its reduction and actual adjunction,
  `coefficientDerivedSystemEvaluationCalculus`.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `integralCompactificationSystemRealization`, `Realizations`; publicly supplied
  `System`, `Integral`, `calculus`, `Operations`, `Compositors`, `OpenComparisons`,
  `Good`, `Origins`, `LevelBounds`, `Compositors.pushComp` and the normalization
  fields in `IntegralSystemOperations` / `IntegralSystemExpressionDomain`.
- `Sheaf.SixFunctors.IntegralOperationShiftData`:
  `systemShifts`, `Expression.SlotContext.shift`, all five unary shift definitions,
  `TensorShifts` and the signed `systemTensorRightFormula`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: recorded `finiteTorConstructibleEtale`
  and reexported `finiteTorConstructibleIntegral`, `HasProEtaleTorAmplitude`;
  the actual system domain already uses the latter interval predicate in
  `LevelBounds`, without replacing it by a new Tor definition.
- `Sheaf.SixFunctors.SystemPrimitiveComparisonShift`:
  `PrimitiveSystemScheme`, `PrimitiveSystemArrow`, `PrimitiveSystemComparison`,
  `systemPrimitiveComparisonShift`.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `openTensorNormalization`;
  its reexported `Assertion.beta_inverse` and `gamma_inverse` have precisely the
  transposes already retained by the actual system `OpenComparisons`.
- Proof imports: `ExactDerivedAdjunctionUnitShift`,
  `PurReductionLimitShiftAdjunction`, `DerivedAdjunctionShift`. The two Mathlib
  proof leaves are `Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit`
  and `NatTrans.CommShift.comp` / whiskering, visible through the public shift
  imports. The upstream generic mate theorem
  `WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction` is a proof import.

Edge cases checked before writing and again on the final statement:

- r=0, positive and negative r all occur in unrestricted `r : ℤ` binders.
- Both tensor occurrences are present; the second uses the recorded signed
  comparison and is never replaced by the unsigned first-slot comparison.
- Identity opens, identity arrows, empty schemes/opens and zero inputs are not
  excluded by any binder. No nonemptiness or dimension assumption is added.
- All positive coefficient exponents occur through the recorded n+1 indexing;
  no degree-zero coefficient quotient is inadvertently required.
- Nonproper separated finite-type pullback adjunctions are retained; proper
  direct-image composition carries exactly the properness domain of S_p.
- Integral and system endpoints both have object universe u+2 and their actual
  category and shift instances. No artificial identification of site object and
  morphism universes is imposed.
- No faithfulness of derived finite evaluation is assumed. The theorem's
  equations are equalities in the original categories before evaluating.

Searches (2026-10-24):

- msearch LeanFinder: `Derived semilinear system adjunction units counits mates
  normalized open base change tensor comparisons commute with shifts` — 8 hits,
  all generic adjunction compatibility lemmas; no exact system/open statement.
- msearch Loogle: `CategoryTheory.Adjunction.CommShift,
  CategoryTheory.NatTrans.CommShift` — 4 generic unit/counit or class-constructor
  hits, no exact specialization including normalized beta and gamma.
- msearch LeanSearch: `Natural transformations and adjunction mates commuting
  with shifts` — 8 generic CommShift component/class hits, no exact node.
- msearch grep `CommShift|commShift`, Mathlib CategoryTheory/Shift — 25 hits in
  shift calculus, including Adjunction and generic composite shifts. None
  states this finite-system package.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the node id, adjunction/shift
  and mate terms found the generic upstream `NatTrans.CommShift.mateEquiv` and
  existing primitive/basic shift modules. These do not assert this node's
  canonical adjunction and open-map squares. The exact node-id grep in
  `lean/WeilConjectures` has no hit. All proposed helper/main names were searched
  in both source trees and `dag/lean_names_upstream.json`, with no collision.

Source read: current `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-compatibility/fix-prop-coherence.proof.md` (the current location is
sk-thm-sf-compatibility, whereas the historical node source path says package).
It still names the maps-used/coefficient comparisons and units/counits, and is
not itself a shift theorem. No statement correction is needed for this agent-
extracted obligation. No disputed statement or dependency repair was found.

Validation: prescribed scompile.py compiled the sandbox and canonical module
successfully, with no errors or disallowed warnings. No repository edits, git
commands, local builds or direct preflight invocation were used.

## Second reading by Q40

A separate second pass reopened the node and the complete module, matching every
hypothesis and clause against the definitions above. It checked the actual beta
and gamma transpose equations against the recorded OpenComparisons rather than
only checking endpoint types. It checked both gamma contexts, the primitive
symmetry's permuted slot, all three actual adjunction cases, both adjunct forms,
and the order of the general mate's three factors. It checked that the context
and mate-domain predicates retain all intermediate normalized systems and that
integral admissibility is sfIntegralConstructible. The initial scratch import
probe was removed; the final file contains no #check, local notation, local
instance or unbound implicit. The helper category/shift instances are case
selection of the existing endpoint instances, not postponed existence choices.
No semantic mismatch or node correction was found. All 22 public top-level
helper/main declarations are recorded in lean.declarations, and only the main
theorem has a postponed proof, with the accepted nine-step proof docstring.
