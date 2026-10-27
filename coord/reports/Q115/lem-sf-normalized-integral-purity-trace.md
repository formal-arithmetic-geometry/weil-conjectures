## Worker report

Module: `Sheaf.Paper.NormalizedIntegralPurityTrace`. It states
`WeilConjectures.NormalizedIntegralPurityTrace.normalizedIntegralPurityTrace` and defines
its component, actual counit, counit trace and explicit finite quotient equations.
No proof is supplied. Every theorem uses `sorry`; every definition has actual data.

Hypotheses and clauses:

- `D : FiniteFieldDatum.{u}` supplies p, q, the finite base field and its algebraic
  closure k. `C : D.CoefficientDatum` supplies the prime ell, ell ≠ p and fixed Qbar.
  `E : AdicPurityScalarNaturality.Field D C` is a finite intermediate coefficient field,
  with the recorded valuation ring, uniformizer and quotient rings. Its subtype is the
  existing finite-dimensional intermediate-field encoding, not an arbitrary ring.
- X and Y carry `Over (Spec (.of D.k))`, `LocallyOfFiniteType`, `QuasiCompact` and
  `IsSeparated` on their structure maps: exactly separated finite-type k-schemes.
  The morphism f has `IsOver`, separated finite-type instances and
  `SmoothOfRelativeDimension r f`, with `r : ℕ` allowing relative dimension zero.
- `S` and `A : AdicPurityScalarNaturality.Data D C f r S` specify the normalized
  exceptional-adjunction realization and simultaneous purity family in the statement.
  Their existence is the already recorded `adicPurityScalarNaturality`; these arguments
  retain the specified component instead of selecting an unrelated lift.
- `L` is in the actual completed-coefficient derived category, and `hL` is the recorded
  `sfIntegralConstructible` predicate. There is no finite-Tor premise on L.
  The first conjunct quantifies over every ordered residue cohomological interval [a,b]
  and asserts `HasProEtaleTorAmplitude` in the identical interval at every level.
  `∃ hTor` asserts membership in the family's uniform finite-Tor domain.
- `component` applies the full inclusion to `A.gamma E` and composes with exactly
  `A.targetRealization E`; its type is an isomorphism from `purAdicSource` to
  `purAdicTarget`. The inverse orientation is its `.inv`, never an independently
  chosen iso. `counit` transports the operation's actual adjunction counit through
  that same target realization and `S.ring.left`.
- `trace` is literally compact support of `component.hom` followed by `counit`.
  The theorem's forward and inverse equations use the actual
  `purAdicSourceReduction`, `purAdicTargetReduction`, and `purAdicFiniteArrow`.
  The finite iso e is pinned by `e.hom = purAdicFiniteArrow.hom`.
- The trace equation is `Q_Y(trace) = c ; P_n(a) ; t_n`, where c is the actual
  `PurCompactSupport.comparison` followed by `finiteImageIso`, transported by the
  normalized `reductionBridge` at both endpoints, and t_n is the
  recorded `coefficientValuedSmoothTrace`. The counit equation is separately
  retained, with `P_n(b)` and the specified finite exceptional counit.
- `supportComparison` names that same c, and invertibility is asserted at H_R L
  and G_R L. Source and target comparison invertibility is asserted separately.
- `FiniteEquations` quantifies over every 1 ≤ m ≤ n+1, including m=n+1, and
  displays finite purity, inverse, trace and coefficient-counit equations.
  `QuotientEquations` explicitly identifies reduction via n+1 then m+1 with
  direct reduction via m+1, for a, b and c. `reductionComposition` is the canonical
  tensor associator conjugated by the existing normalized `reductionBridge`.
  `quotientProjection` states the corresponding equality of actual ring projections.
  Nothing asserts uniqueness of arbitrary integral morphisms from their reductions.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum` and its recorded
  integral operation convention. The actual adjunction presentation used here is
  `ConstructibleExceptionalCoefficients.System` from the normalized-family dependency.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: `sfIntegralTwistingFunctor`;
  reexports the integral twist used by `purAdicSource`.
- `Sheaf.Paper.SmoothPurityMap`: `PurityFiniteSetting.smoothPurityMap`.
- `Sheaf.Paper.SmoothTrace`: `smoothCompactSupport`, `smoothExceptionalCounit`,
  `coefficientValuedSmoothTrace`.
- `Sheaf.Paper.AdicPurityScalarNaturality`: `Data`, `gamma`, `targetRealization`,
  `finiteReductions`, `finiteRightNormalized`, `operation`, `reductionBridge`.
- `Sheaf.Paper.PurAdicReconstruction`: `purAdicReconstruction`; the source/target,
  canonical reduction and specified finite-arrow declarations it publicly imports.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleIntegral`,
  `finiteTorConstructible` and their full categories.
- Proof imports: `IntegralResidueTor.integral_residue_tor` (in namespace
  WeilConjectures); `IntegralCompactSupportPrescribedReductions`;
  `Etale.boundedConstructibleIntegral_exceptionalAdjoint` in the recorded upstream
  `IntegralCoefficients`; `AlgebraicGeometry.exists_topologicalKrullDim_le`;
  `FiniteExceptional.finite_exceptional`; `FiniteReductionOfPurity` and its
  `finiteReductionOfSmoothTrace`. The proof-only node
  `lem-pur-adic-source-finiteness-reductions` has no Lean record in the read base,
  so there is no module to import for it. Its source-comparison assertion is stated
  explicitly in the present node, using the already recorded canonical constructions.

Edge cases checked: r=0; empty source or target; L=0 (any ordered interval);
residue index 0 means exponent 1 and every natural index n means exponent n+1;
all positive finite quotients and their identity case; ramified coefficient fields;
nonflat quotient maps (only derived tensor is used). No dimension lower bound,
nonemptiness, quotient flatness or site-perfectness is assumed.

Searches: `msearch.py` LeanFinder query “Integral adic smooth purity inverse orientation
counit trace compatible with finite coefficient reductions” returned algebraic smoothness
and cotangent facts, no match. Loogle `"purity"` returned compiler purity only. Mathlib
grep `purity|smoothTrace|adic.*counit|counit.*adic` returned unrelated adjunction/monad
files. LeanSearch “Integral smooth purity and its inverse orientation commute with
reduction and compact support counit traces” returned algebraic trace and condensed
counit facts, no match. Raw results are in searches.jsonl in the sandbox. `rg` searches
of both project roots and the upstream name index found `NormalizedOrientationPerfectDuality`
as a nearby package, but it does not retain the scalar-natural family as its specified
component: it existentially quantifies an unrelated reconstruction iso. It therefore
cannot be recorded as an existing exact match. The actual canonical constructions are
reused instead. The upstream `Smooth/Adic` theorem is also an abstract reconstruction
statement on supplied towers, not this chosen-family trace theorem.

No statement correction, new independent notion, dependency repair or disputed statement.
The maintainer's independent review reads the delivery, as specified in this dispatched
brief; no sub-agent or purported independent worker reading was created.

## Second reading by Q115

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
