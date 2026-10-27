## Worker report

This delivery states `WeilConjectures.IntegralSystemRealization.SystemShift.properOpenProjectionShift`
in `Sheaf.SixFunctors.SystemProperOpenProjectionShift`, with one `sorry`. All helper data
are explicit recursions or predicates; there are no other postponed theorems, axioms, or
chosen endpoint maps. The node's statement, dependencies and accepted proof are unchanged.

Hypothesis and clause correspondence:

- The geometric coefficient datum is `(D : FiniteFieldDatum.{u})`, `[Fact l.Prime]`,
  `_hl : l ≠ D.p`, `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. `D.k` is the fixed algebraic closure of the finite field.
  The recorded coefficient constructions use its valuation ring, chosen uniformizer
  and quotient at exponent `n+1`, so all positive levels and only positive levels occur.
- All scheme indices are `Over (Spec (.of D.k))`; `Geometry` imposes locally finite type
  and quasi-compact structure morphisms (finite type). A pullback vertex also retains
  the separated finite-type condition. Proper and quasi-compact open witnesses are
  stored in the published `Expression.SlotContext` constructors.
- `System l E W` is the published `coefficientSequenceDerived`, the ordinary unbounded
  derived category of strict semilinear module systems on the ringed sequence site.
  `o : Operations l E`, `c : Compositors l E o`, `a : OpenComparisons l E o c`,
  `bridge : CanonicalBridge l E o`, and `h : ProperOpenCoherence ...` supply the exact
  operations and actual comparisons of the realization dependency. They do not assume
  any of the requested shift equations. `h.canonical` and `h.adjunct` pin its Gamma to
  the intrinsic semilinear mate and to the inverse of the displayed lambda.
- The fixed reduction/limit adjunction is the recorded `calculus l E W` used by these
  operations and by `systemShifts`. The system statement does not assert an integral
  output equation: its integral-input convention is respected when applying it to
  actual reductions of derived-complete constructible integral inputs. No replacement
  integral operation, limit or reconstruction map is introduced.
- `Domain` recursively checks every context vertex, fixed tensor operand and the open
  intermediate inside compact support with `GeneratorReduction.SystemAdmissible`.
  That existing predicate is normalization, compatible `Origins`, positive-level
  constructibility, cohomological support in `Set.Icc lo hi`, and Tor amplitude in
  `tl,th`, with ordered endpoints. `termsBounded` applies the identical predicate to
  the internal terms of the displayed mates; `properOpenTerms`, `exchangeTerms`,
  `projectionTerms` and `compactProjectionTerms` list those actual systems explicitly.
  The final `_adm` existential uses one common tuple for the whole finite pasting.
- `Slot` is an abbreviation for the existing explicit single-slot context, not a
  parallel expression language. `Square` is exactly
  `τ (M⟦r⟧) ≫ χ_target = χ_source ≫ (τ M)⟦r⟧'` with
  `Expression.SlotContext.shift (systemShifts l E o)`. Its tensor-right branch therefore
  uses the published signed `(-1)^(ri)` comparison and its unary branches use the
  published cochain/adjunction comparisons. `r : ℤ` includes all integer shifts.
- `_generators` assumes these squares on the stated admissible domains for the actual
  maps indexed by `Generator`: pullback compositors and square comparisons, both
  pullback/tensor slots, proper/open units and counits, direct-image/open compositors,
  normalized beta, both open projection slots, clopen comparison and the component
  projection. It does not assume any Composite shift square.
- `Composite.gamma` uses exactly `h.gamma`; the square is merely commutative, with
  proper verticals and quasi-compact open horizontals. No cartesian hypothesis is
  inserted, so noncartesian refinement squares with identity left vertical remain.
  `Composite.lambda` uses `properOpenLambda ... .hom.app M` directly. That definition
  is conjugate cartesian open restriction, `restrictFactor`, the clopen `J_s ≅ S_s`
  and direct-image compositor, with `s = StrictTower.squareLift ...` on the actual
  fiber product. It is not an independently chosen inverse.
- `Composite.exchange` uses `properExchange`, the existing unit/square/counit mate,
  with an `IsPullback` witness for the stated cartesian square. Its proper witnesses
  are exactly the admissible `S_p` and `S_r` operation domains, not invertibility of
  exchange. No exchange/projection isomorphism is assumed.
- `Composite.projectionLeft` and `projectionRight` are the two occurrences of the
  identical `properProjection`, the published `rightAdjointProjectionMap` of the
  actual tensor-pullback comparison. Its transpose is mu then epsilon tensor identity,
  so this is precisely the node's pi formula, including its unit.
- `compactExchange` uses `compactificationExchange`, hence the recorded
  `SuppliedExchangeProjection.compactificationExchangeFromData`: proper exchange on J
  followed by S of beta. The open and proper square witnesses state base change.
  `compactProjectionLeft` and `compactProjectionRight` use the same existing
  `compactificationProjection`, including `a.projection`, inverse `c.pullComp`, and
  the compactification equation. Thus gamma includes `P_j P_p ≅ P_f` in its exact
  published direction. Each tensor occurrence is tested separately with the other
  system fixed, even when those systems happen to be equal.
- `Pasting` is finite syntax indexed by the actual map family, not a hypothesis that
  an arbitrary map has the desired property. It includes generators, named Composite
  maps, identities, composition, inverses when the actual map is an isomorphism,
  output pull/push/open/compact-support/tensor contexts, and input whiskering.
  Input whiskering is the explicit recursion `insert`, its recursively computed
  `insertObjIso`, and `before`; these introduce no arbitrary transport maps. Every
  constructor retains all intermediate domain tests in the fourth index. This covers
  the composition/refinement comparisons built from Gamma and direct-image/open
  compositors, their canonical inverses, and every finite pasting in the node.
- The conclusion is the intrinsic morphism equality `Square ...` in `System`, not a
  family of evaluated equalities or a condition detected after restriction of scalars.
  Naturality in the selected and fixed operands comes from the exact published natural
  transformations and functorial constructions indexing Generator and Composite;
  composition, inverse and whiskering preserve their naturality. The equation is
  quantified over every choice of the fixed operands, not a selected representative.

Dependency declarations read and used:

- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientDerivedSystemEvaluationCalculus`;
  used through the actual `calculus` and system tensor/reduction operations.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `properExchange`, `properProjection`, `compactificationExchange`,
  `compactificationProjection`, `ProperOpenCoherence`, plus the publicly imported
  `Operations`, `Compositors`, `OpenComparisons`, `CanonicalBridge`, `System`,
  `properOpenLambda` and actual `pull` and `calculus`.
- `Sheaf.SixFunctors.IntegralOperationShiftData`: `systemShifts`, `tensorShifts`,
  `Expression.SlotContext.shift`; these carry the actual tensor model normalization
  and the same strict-tower Roos normalization (`limitShift_roos`).
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`; and
  `Sheaf.Paper.FiniteTorAmplitudeSites` / `FiniteTorAmplitude`:
  `finiteTorConstructibleIntegral` and `HasProEtaleTorAmplitude`, used through the
  established admissible-system predicate and recorded realization domain.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`: the actual `lambda`, `gamma`,
  `gamma_adjunct` and its intrinsic factorization, used via `CanonicalBridge` and
  `ProperOpenCoherence.canonical/adjunct`, not a second definition.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `compactificationExchangeFromData` and the counit projection construction used in
  the recorded realization maps. Its recorded higher-stage interface is usable.
- Existing helper interface `Sheaf.SixFunctors.GeneratorReductionStatement`:
  `GeneratorReduction.SystemAdmissible` (normalization, compatible origins and uniform
  constructible/Tor bounds). This is reused instead of defining that notion again.
- Proof imports: `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` and
  `Mathlib.CategoryTheory.Shift.CommShift` (id, comp, whiskerLeft, whiskerRight and
  composite shift comparisons). There is no dependency repair or duplicated notion.

Edge checks: integer zero, negative and odd shifts; the signed second slot; empty
schemes and empty opens (no nonempty binder); zero objects; identity proper maps;
clopen s an isomorphism; noncartesian identity-left refinement squares; equality of
fixed and shifted operands does not identify their occurrences; every positive quotient
including exponent one; no exponent-zero quotient; finite empty pasting is `id`;
exchange and projection are allowed to be noninvertible. Finite bounds are existential,
not numerically frozen by shifting. All universes are explicit and autoImplicit is false.

Searches actually run with `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- LeanFinder: `Proper open interchange and projection exchange composites commute with
  integer shifts in each tensor input`. Eight hits: generic CommShiftTwo structures,
  integer signs, and bicomplex tensor shifts; no complete semilinear-system theorem.
- Loogle: `CategoryTheory.NatTrans.CommShift, CategoryTheory.Adjunction`. Four hits:
  `Adjunction.CommShift.commShift_counit`, `.commShift_unit`, `.mk'`, `.mk`.
- Mathlib grep: `projection.*shift|shift.*projection|CommShift`, in CategoryTheory/Shift.
  Twenty-five hits on induced/localized/opposite/quotient shift structures; no item match.
- LeanSearch: `Canonical proper open exchange and projection maps of derived coefficient
  systems commute with integer shifts`. Eight hits on exact derived functor shifts,
  cochain shifts and cone shifts; no complete item match.
- Local `rg` over `lean/WeilConjectures` for the item id and proper-open/projection-shift
  patterns found generic `CategoryTheory/Adjunction/ProjectionMapShift.lean` and the
  fixed-coefficient etale `LowerShriekProjectionShift.lean`, not the combined system
  statement. Local `rg` over `lean/Sheaf` found the primitive comparison and integral
  realization shift theorems; the latter's conclusions concern the reconstruction
  realization comparison, not this conditional system theorem. Item-id search found
  no existing declaration. No matching repair note was present.

Validation: the complete module compiled in sandbox and library module mode with
`scompile.py`, each within the 60-second limit. The final clean run produced no warnings.
The only theorem proof is `sorry` as required by stage 2. No statement dispute or
source-based correction was needed. The latest blueprint source was read at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`;
the node's old package directory has moved there. Its shift obligation remains expressly
agent-formulated, as the source record already says.

## Second reading by Q129

Author self-check, performed with the node and completed module open; this is not an
independent review and no other agent was started, in accordance with the dispatcher
brief. The maintainer supplies the independent mathematical review.

I checked the field/coefficient binders, the actual strict-system category, the fixed
slot shifts, the generator hypotheses, each of lambda/Gamma/Ex_*/pi/Ex_!^c/PF^c, both
projection slots, noncartesian refinements, and the finite-pasting clause against the
node. I found and fixed two domain omissions during this reading: the inner `J_j M`
inside compact support and the inner unit/tensor/counit systems of the displayed mates.
The final Domain and Composite domain indices retain those systems and one shared
bound tuple. The initial recursive pasting-domain helper was replaced by an indexed
pasting grammar so each constructor explicitly retains its intermediate tests. Input
whiskering uses an explicit substitution recursion; no endpoint isomorphism is chosen.
The generator assumption is restricted to the node's admissible domain. The lambda and
Gamma maps are those supplied by the recorded intrinsic interfaces, and no cartesian
hypothesis was added to their proper/open square. The proof docstring follows all six
accepted proof steps, including the inverse-open-unit argument and the sign in the
second tensor slot. No node statement or accepted split was changed.
