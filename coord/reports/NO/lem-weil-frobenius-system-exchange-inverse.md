## Worker report

The module `Sheaf.Paper.FrobeniusSystemExchangeInverse` states the node in eight named
sorry theorems and packages only canonical maps/isomorphisms already supplied by the
recorded dependencies. No statement correction, new node, or dependency repair is needed.
The live node is stage-1 split/reviewed, not stage-2 stated; Q104's review does not prohibit
adding its missing Lean attachment. No repair note for this item was present.

Hypotheses and clauses:

- `D : FiniteFieldDatum.{u}` is the complete global finite-field datum, including arbitrary
  fixed algebraic closure. `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give exactly the coefficient data.
  The existing coefficient extension constructions fix its valuation ring, uniformizer,
  positive quotients and quotient transitions. Natural-number index `n` means exponent
  `n + 1`, including the first quotient.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` with locally-finite-type and quasi-compact structure maps
  are finite-type base-field schemes. `f₀ : X₀ ⟶ Y₀` is over that field; `fs`, `fft`, `fqc`
  require separatedness and finite type of this morphism, without separatedness of either
  structure map. `c₀ : Compactification f₀.left` retains the supplied open/proper model.
- `D.geometricFiber`, `fiberMap D f₀`, `galois D X₀`, `galois D Y₀` and the middle model's
  `galois` are the actual geometric fibers, maps, and coefficient Frobenii. They are never
  assumed linear over the algebraic closure. `geometricCompactification D f₀ c₀` is the
  base change of that same compactification at every quotient level.
- `coefficientSequenceDerived l E W` is the ordinary unbounded derived category of strict
  semilinear quotient module systems, represented by module sheaves on the vertical
  sequence site. Its coefficients are the finite constant sheaves; its limit realizes
  completed integral coefficients. `frobeniusSystemDirect` is an abbreviation for precisely
  `systemExchange`, the ordinary adjunction mate. `frobeniusSystemCompact` abbreviates
  precisely `systemCompactExchange`, the proper mate followed by proper image of open
  exchange. Neither abbreviation supplies new mathematical data.
- `frobeniusSystemDirect_isIso` and `frobeniusSystemCompact_isIso` assert `IsIso` of these
  natural transformations, hence invertibility on every object and natural inverses.
  The `...Iso` definitions use `asIso` of those exact arrows. Arbitrary inputs are explicitly
  `C : coefficientSequenceDerived ...`; no bounds, constructibility, finite Tor amplitude,
  cartesianness, normalization, or etale-origin witness is imposed on them.
- The two `..._inverse_evaluation` theorems produce a finite iso whose `hom` equals the
  existing `frobeniusDirectFinite` or `frobeniusCompactFinite` component. Its `inv` is
  `targetComparison.inv ≫ evaluation.map(systemInverse) ≫ sourceComparison.hom`.
  Thus the finite exchange itself, rather than an unspecified arrow with those endpoints,
  is identified. Both comparisons use exactly `systemPullEvaluation`,
  `systemDirectEvaluation`, `systemOpenEvaluationInv`, and `openSquareDerivedPullbackModel`.
  The compact comparison is assembled before reduction, so the theorem covers every C.
  These assertions do not assume or imply faithfulness of evaluation.
- `frobeniusDirectIntegral_isIso` and `frobeniusCompactIntegral_isIso` assert invertibility
  of exactly the geometric integral natural transformations from the recorded definition.
  Their domain is `sfIntegralConstructibleCategory`, i.e. the full bounded constructible
  derived-complete integral category. The direct theorem explicitly retains the morphism
  hypotheses from the node, even though the existing definition has a wider domain.
- `frobeniusDirectIntegral_inverse` and `frobeniusCompactIntegral_inverse` quantify over
  every `K : sfIntegralConstructibleCategory ...` and equate the underlying inverse arrow
  to `beta.inv ≫ coefficientSequenceLimit.map(systemInverse at reduction(K)) ≫ alpha.inv`.
  This is the displayed reverse-order formula in categorical composition notation.
  `coefficientSequenceLimit` is exactly scalar restriction followed by total derived
  inverse limit, not a choice inferred from individual reductions. Direct alpha packages
  `sourceComparison`; direct beta packages the inverse effective pullback counit. Compact
  alpha and beta additionally use the same projection-normalized `compactRealization`.
  Each helper is a real composite or `asIso` of a uniquely determined arrow, with proof
  inputs from named existing theorems; no hollow choice or arbitrary integral map occurs.

Dependency declarations inspected and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `geometricFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported coefficient
  extension module: `Padic.coefficientExtensionRing`, its quotient transition,
  `finite_coefficientExtensionRing`.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`, `Refinement`
  and its category; scheme properties use the Mathlib classes named in the convention node.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius` and
  `galoisMap`, reached through the recorded geometric exchange wrappers.
- `Sheaf.Paper.CompletedIntegralCoefficients`: `integralCoefficientSheafSystem`,
  `completedIntegralCoefficientSheaf`, its projections and completed-module categories.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearSections.semilinearDerivedSections`
  and `evaluation_mate`; imported as the proof dependency for joint conservativity and
  normalization of the actual derived-system operations and evaluated mates.
- `Sheaf.Paper.FrobeniusGeometricExchange` (the recorded square-exchange attachment),
  `Sheaf.Paper.FrobeniusSquareExchange` and `Sheaf.Paper.SystemOperationExchangeRealization`:
  all canonical system and finite exchanges and evaluation comparisons named above,
  `frobeniusDirectIntegral`, `frobeniusCompactIntegral`, `sourceComparison`,
  `reductionPullbackIso`, `compactAlpha`, `compactBeta`, `compactRealization`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.CompletedRlimFunctor`: `Scheme.completedRlim` and its universal derived
  pair; explicit proof-only import for `prop-weil-pbc-rlim-functoriality`.
- `lem-weil-frobenius-finite-exchange-inverse` currently has no recorded Lean module, so no
  proof-only import can yet be added for it. Its name and all proof steps are retained in
  the theorem docstrings for stage 3. It is not needed to type any statement here.

Searches (msearch.py, group NO and this item): LeanFinder query “Geometric Frobenius
exchange on derived semilinear coefficient systems is invertible and realizes the inverse
integral exchange” returned coefficient Frobenius identities in Perfection/Perfect only.
Loogle query `CategoryTheory.Functor.map_inv, CategoryTheory.IsIso` returned `Functor.map_inv`,
which is the generic functor identity, not the system/geometric assertion. Mathlib grep
`semilinear.*[Ss]ystem|[Ff]robenius.*[Ee]xchange` in CategoryTheory returned zero hits.
LeanSearch query “A natural Frobenius exchange on the unbounded derived category of strict
systems of sheaves is an isomorphism and its inverse is preserved by derived inverse limit”
returned resolution naturality, rightDerivedZeroIsoSelf, the unrelated monoidal
frobeniusMorphism, limitIsoFlipCompLim, and sheafPushforwardContinuousIso; none is a match.
Repository rg searches for Frobenius/system exchange and inverse names found the existing
canonical constructions used here, but no theorem with this node's whole-system conclusion.
The required item-id grep in WeilConjectures returned no hit. The adic/field-coefficient
GeometricFrobenius and GeometricFrobeniusMate modules concern AdicSheaf or module sheaves,
not these ordinary unbounded derived strict varying-ring systems and integral realization;
they do not state this node. All chosen new declaration names were searched in Mathlib,
WeilConjectures and Sheaf and had no hits.

Source check: Deligne PDF printed pp. 150--153, especially (1.1.7) and (1.1.14), confirms the
geometric inverse field Frobenius, coefficient action and transport-of-structure convention.
The extra unbounded system argument is correctly attributed to the agent-written DAG proof,
not to a nonexistent assertion of Deligne. Every sorry has the matching node id and its
relevant full natural-language proof steps in its docstring.

Edge cases checked: zero system; empty source or target; identity morphism; first quotient
n=0 (exponent 1); unbounded systems and noncartesian/non-normalized systems. No nonempty
scheme assumption or normalization was introduced. Alpha and beta are only used on the
stated integral constructible domain. Arbitrary sites' object/morphism universe difference
is retained by the existing pro-etale/sequence-site APIs (object level u+1, maps u); no size
equality is imposed on them. The common universe u is the existing coefficient/geometric
API's ambient size and can be enlarged for any fixed set of source objects.

Validation: scompile.py compiled both sandbox and actual module cleanly, with no diagnostic
commands or warnings. All eight theorem bodies are exactly `by sorry`; the other
declarations are canonical abbreviations and isomorphism composites. Node delta is lean only.
No STATEMENT-DISPUTED or mathematical fault found.

## Second reading by NO

Self-check by the dispatched worker; no independent worker was started, as explicitly
required by this dispatch. The maintainer supplies the independent reading. I reopened the
node and final module and checked every hypothesis and clause as mapped above. The initial
self-check found that merely stating preservation of inverses under evaluation failed to
name the finite exchange. I replaced that with the two explicit finite isomorphisms whose
forward maps equal the recorded finite exchanges, using operation/pullback conjugations.
The initial draft also lacked the displayed integral inverse equations; both are now
explicit, with the system inverse evaluated at the actual simultaneous reduction of K.
The direct integral theorem retains separated finite-type morphism hypotheses explicitly.
No site, coefficient or integral comparison is independently redefined.
