## Worker report

Attach the exact existing declaration
`WeilConjectures.sixFunctorProjection_baseChange_integral` in
`Sheaf.Paper.ProjectionFormulaCoherence`, at
`lean/Sheaf/Paper/ProjectionFormulaCoherence.lean:523–548`.
No module is written: the one-definition rule requires an existing attachment.
The theorem's proof remains `sorry`; this is statement certification only.
Only the item's `lean` field changes. No new nodes or dependency repairs.

Sources read: the full item, its seven statement dependencies and their recorded
interfaces; current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`,
base-change paragraph (lines 18–41); the existing theorem and helper definitions
at lines 474–548. The live server source returned by
`scompile.py --source Sheaf.Paper.ProjectionFormulaCoherence` confirms the theorem
is present, not merely a quarantined candidate. The record copies the signature
verbatim from `theorem` up to `:=`.

Hypothesis and clause correspondence:

- Finite-field datum: `D : FiniteFieldDatum.{u}` contains `p`, finite `k₀` and
  algebraic closure `k`, with the specified field and closure structures.
  `C : D.CoefficientDatum` supplies the prime `C.l`, its inequality to `D.p`,
  and `C.Qbar`. The surrounding explicit binders are `E : Type u`, `[Field E]`,
  `[Algebra (Padic C.l) E]`, `[FiniteDimensional (Padic C.l) E]`, `n : ℕ`,
  `hn : 1 ≤ n`. Valuation ring, uniformizer and coefficient constructions are
  the existing ones used throughout the operation datum.
- `S : SixFunctorDatum D C E n hn` is precisely the supplied six-functor datum,
  extending `SixFunctorOperationDatum`, with its operations and comparisons.
- `Q : SixFunctorCompactifiedSquare D` retains the finite-type schemes, maps,
  Cartesian outer, proper and open squares, the open and proper factors, and
  both factorizations. `Q.compactification` and `Q.compactification'` use those
  factors. `[IsSeparated Q.f.hom.left]` is the separatedness hypothesis on f.
  `SixFunctorSpace` is finite-type over k without separatedness of its structure
  map; the theorem has no separatedness hypothesis on g.
- K and L have types `sfIntegralConstructibleCategory C.l E Q.X.obj.left` and
  `sfIntegralConstructibleCategory C.l E Q.Y.obj.left`. This category requires
  derived completeness, bounded constructible reductions and a common finite
  cohomological interval for all positive reductions.
- `S.toSixFunctorOperationDatum.integralFiniteTorDomain Q.Y L` unfolds to
  `finiteTorConstructibleIntegral C.l E Q.Y.obj.left L.obj`: one ordered integer
  Tor interval for every reduction of exponent `m+1`. It is imposed only on L.
- `S.higher.integral.pull` is U; `S.higher.integral.support Q.f
  Q.compactification` and its primed counterpart are F and F'. The tensors are
  `S.higher.integralTensor`, the recorded completed tensors. The entire equation
  is integral, before rationalization or finite evaluation. Discussion of other
  coefficient conventions introduces no additional conclusion at those stages.
- `(S.higher.integralExchange Q).projectionComponent K L` is the recorded P_f.
  `sixFunctorProjectionExchange (S.higher.integralExchange Q) M` is e_M. Its
  definition inserts only the recorded equalities `horizontal`, `compactSupport`,
  `compactSupport'`, `horizontal'` around `A.stage.compactExchange.app M`.
- `sixFunctorProjectionIntegralMu S u A B` is μ_u: the canonical
  `canonicalIntegralPullbackTensor` conjugated by the datum's
  `integralPullback` and `integralTensorNormalization` equalities.
- κ_L is exactly `(S.higher.integral.pullComposition Q.g' Q.f).inv.app L`,
  then `eqToHom (congrArg (fun f ↦ (S.higher.integral.pull f).obj L)
  Q.squareComm)`, then `(S.higher.integral.pullComposition Q.f' Q.g).hom.app L`.
  Thus it uses inverse compositor, the square equality and compositor in order.
  Mapping this with the tensor functor at U_g'K is identity tensor κ_L.
- The left route, read in Lean's left-to-right `≫` order, is U_g(P_f), then
  e_(K⊗U_fL), then F' applied to μ_g' followed by identity tensor κ_L.
  The right route is μ_g, then e_K tensor identity, then the primed projection.
  Its last component uses `compactSupportProjectionSquare Q.f'
  Q.compactification'`, retaining c'. Their common source is U_g(FK⊗L), and
  target F'(U_g'K⊗U_f'U_gL). The conclusion is equality of these precise arrows.

Dependency declarations used (all in namespace WeilConjectures unless qualified):

- `Sheaf.Paper.SixFunctorDatum`: `SixFunctorDatum`.
- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum` and
  `SixFunctorOperationDatum.integralFiniteTorDomain`.
- `Sheaf.Paper.ConstructibleProjectionMates`: `compactSupportProjectionSquare`,
  `compactSupportProjectionComponent`, and the recorded finite counterpart
  `CompactSupportFiniteProjection.component`. The integral statement uses the
  higher-stage projection component of the same supplied interfaces.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`,
  `.compactExchange`, `.projection`: the proper mate and open projection data.
- `Sheaf.Paper.CompletedPullbackTensorComparison` publicly exposes the integral
  construction in `Sheaf.Paper.CompletedPullbackTensorIntegralConstruction`,
  `canonicalIntegralPullbackTensor`. The primary recorded common-stage
  declaration is the final stage of this existing multi-stage interface.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.FiniteTorAmplitudeSites` publicly imports
  `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructibleIntegral` is its
  integral clause, not the etale presentation named by the primary record.

The existing proof docstring specifies the retained compactification, the open
factor from lem-sf-pf-open-base-change-square, the proper counit/mate square from
lem-sp-categorical-projection-mate-square using monoidality, and pasting by
lem-sf-pf-compactification-pasting. The node's detailed four-step proof additionally
tracks the pullback domain of L and computes κ by compositor associativity.
The proof and all existing declarations are left unchanged.

Edge cases checked at the statement level: n=1 is allowed, and m+1 covers every
positive reduction; zero K or L and empty schemes are not excluded; g=id,
identity-open compactifications, and proper f are allowed. K has no extra Tor
restriction. No finite-evaluation faithfulness hypothesis occurs. The existing
universe u is explicitly bound; no extra equality of site object and morphism
universes is imposed. No STATEMENT-DISPUTED finding or node correction.

Searches actually run using msearch.py NE with this item on 2026-10-28:

- LeanFinder, `Projection formula for completed integral constructible sheaves
  commutes with compact support base change in a Cartesian square`: 8 hits,
  including SheafOfModules pullback/free comparison identities, sheaf restriction
  identities and LightCondensed.ihomPoints_symm_comp; none states this equation.
- Loogle, `CategoryTheory.Adjunction, CategoryTheory.Functor.Monoidal`: 12 hits on
  monoidal adjunction units/counits and lifted monoid functors; no exact match.
- grep, `projection.*base[Cc]hange|base[Cc]hange.*projection` in CategoryTheory:
  0 Mathlib hits.
- LeanSearch, `Projection formula commutes with base change for completed
  integral constructible sheaves`: 8 hits on stable base-change properties,
  tensor base change and sheaf restrictions; no exact match.
- Project rg for `sixFunctorProjection_baseChange_integral`,
  `sixFunctorProjectionIntegralMu`, `sixFunctorProjectionExchange` in
  lean/Sheaf and lean/WeilConjectures found the exact theorem at line 523 and
  helper definitions at lines 474, 492 in ProjectionFormulaCoherence.
- rg for the item id and theorem name in lean/WeilConjectures,
  dag/lean_names_upstream.json, coord/repair-notes and coord/returns/NE.md found
  only the parent's resolved split/allocation note; no upstream duplicate or
  item-specific repair note. That note explicitly allocates this existing
  sorried declaration to this node. The server source read confirms the match.

## Second reading by NE

This is the dispatched worker's second pass; no other agent was started because
the brief prohibits it. Independent review remains the maintainer's delivery
review. With node and source open, I rechecked the exact direction of κ: `.inv`,
square transport in the direction Q.squareComm, `.hom`. The left exchange is at
K tensor U_fL, while the right exchange is at K and tensored with identity at
U_gL. The μ calls have the precise displayed arguments. The final primed
projection uses f' and c' of the same Q. Reading SixFunctorSpace and the square
record confirms no hidden separatedness condition on g or the structure maps.
Reading finiteTorConstructibleIntegral confirms the interval is independent of
the positive reduction index. No mismatch was found, and no statement change
was made. The existing attachment avoids duplicating any of these notions.
