## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent`.
All theorem proofs are `sorry`; definitions contain actual data or a choice from
an explicitly unique, generator-characterized universal property. The original
statement, proof and proof dependencies are unchanged. One definition dependency
supplies canonical geometric maps missing from the existing interface.

Hypotheses and clauses, read against the node and source paragraph 2:

- `N : ℕ`, `hN : 0 < N` render N ≥ 1. `A : Type (u+1)`, `[CommRing A]`,
  `[Finite A]`, `hA : (N : A) = 0` render precisely finite commutative coefficients
  annihilated by N, including the zero ring.
- `S,T : Scheme.{u}`, `[IsNoetherian S]`, `[IsNoetherian T]` use the existing
  locally Noetherian plus quasi-compact scheme convention, equivalent to a finite
  affine cover by spectra of Noetherian rings. `hS : IsUnit (N : Γ(S, ⊤))`
  is invertibility of N. Invertibility on T and on total spaces is derived using
  `affineTracePullbackInvertible`; it is not an extra hypothesis.
- `r,s : ℕ` include zero. `F,G : S.Modules` with
  `IsFiniteLocallyFreeOfRank` are exactly constant-rank locally free modules.
  `VectorBundleZeroSection.scheme` and `.π` are the existing Spec Sym construction.
- `DerivedCategoryModule A S` is the ordinary small-etale unbounded category of
  constant-ring module sheaves, not the pro-etale coefficient construction.
  `vectorIntegrationCoefficient` is the existing ordered tensor presentation of
  A_E(r)[2r], and `vectorBundleIntegration` is the actual glued integration.
- `vectorBundleIntegration_baseChange` quantifies over every `f : T ⟶ S`, with
  no flatness, separation or finite-type condition on f. The geometric source is
  the bundle of `(Scheme.Modules.tensorPullback f).obj F`.
  `VectorTraceGeometry.baseChange_isPullback` identifies it with E ×_S T.
  The first factor is the actual `rightDerivedLowerShriekBaseChangeMap`; the next
  factor is lower shriek of `vectorTraceCoefficientBaseChange.hom`, namely l.
  The left side finishes with the independently defined pulled-back integration.
  The right side pulls back the original integration and then uses the constant
  unit comparison. This writes exactly the node's base-change equation with the
  implicit identification f^*A_S = A_T made explicit.
- The direct sum uses the canonical product presentation `E(p^*F)` over E(G).
  `VectorTraceGeometry.sumIso` identifies it with E(F ⊕ G), fixing BOTH projections
  on generators. `vectorTraceQ` is the rank-r bundle projection; `vectorTraceH`
  is q followed by p. `vectorTraceSumIntegration` transports the actual integration
  of F ⊕ G along this isomorphism using normalized exchange; it is not defined by
  the desired multiplication equation or by an arbitrary map.
- `vectorTraceSumDecomposition` gives W_h ≅ q^*W_p tensor W_q. It uses the
  ordered Tate-power associator with the s base factors first, the pullback
  tensorator, and the existing normalized Tate pullback in the r fibre factors.
- `vectorBundleIntegration_directSum` has left side alpha(W_h) followed by t_h.
  Its right side is Rp_! of Rq_! of this coefficient comparison, inverse of the
  canonical coefficient-first `compactSupportProjectionMap`, tensor of 1_Wp with
  the actual t_q, and the right unit comparison, followed by t_p.
  `vectorTrace_projection_isIso` records the invertibility needed for this inverse,
  with the proper/open proof in its docstring. No projection is an arbitrary datum.
- `vectorBundleIntegration_compactificationTriangle` quantifies over every
  `c : Compactification p` and `e : Compactification (q ≫ c.i)` and identifies
  the triangle compositor followed by t_h with the specified global compositor
  followed by t_h. Together with directSum this gives the same multiplication
  equation for EVERY triangle, rather than merely one chosen compactification.
- `vectorBundleIntegration_swap` uses the actual map induced by the biproduct
  braiding, its Cartesian square over the identity, and the canonical coefficient
  comparison. It equates the two actual trace maps after coordinate permutation.
  Thus the two ordered multiplication formulas are unchanged by exchanging blocks.
- `vectorBundleIntegration_concentration_and_isIso` states every H^q of the trace
  source is zero for q ≠ 0 and that its ACTUAL trace is an isomorphism. Applying it
  to p, q, the sum and the base-changed module gives every source in the node.
- `vectorBundleIntegration_zero` identifies rank-zero integration with the
  identity adjunction trace via the canonical projection E(0) → S and the
  identity compact-support and inverse-image comparisons.
- `vectorBundleIntegration_empty` quantifies over every arrow of the trace's Hom
  type on an empty base and identifies it with the trace, expressing uniqueness.
  No intersection of frame opens is assumed affine anywhere.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: `scheme`, `π`,
  `algebraIso`, `antiEquivalence`, and its frame construction.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its re-exported
  coefficient API: `DerivedCategoryModule`, `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `etaleFiniteTwistPullback`,
  normalized finite Tate pullback; used through the existing
  `OrdinaryFiniteTwistTransport` and `vectorIntegrationBaseCoefficientPullback`.
- `Sheaf.AlgebraicGeometry.VectorBundleIntegration`: `vectorBundleIntegration`,
  `vectorIntegrationCoefficient`, `vectorIntegrationSource`; its charts module
  supplies `vectorIntegration_geometry` and ordered coefficients.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleCompactSupport_baseChange`,
  `unboundedEtaleLowerShriekId` and the normalization/coherence package.
  `vectorTraceExchangeIso` explicitly transports its exact-pullback exchange
  to the existing left-derived inverse-image presentation.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`:
  `isIso_proper_projection_formula_reordered`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  `derivedOpenImmersionLowerShriekProjectionIso`, specialized to ModuleCat A.
- `Sheaf.AlgebraicGeometry.ShriekTensorComposition`:
  `compactSupportProjectionMap`, the proper/open map with exact inverse image.
- `Sheaf.Paper.VectorPurityDirectSum`: `purityBundleMap`, `purityPowerAdd`,
  `purityCompactComposition`. These existing canonical constructions are reused.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  `exists_tensorPullbackAdjunction`. The canonical left-adjoint uniqueness iso
  transfers the existing rank theorem to the required tensorPullback model.
- The stated proof dependencies are imported, including affine top trace, linear
  invariance, compact projection/exchange, symmetric algebra, relative Spec,
  exact inverse image and degree-zero derived map gluing. The ordinary affine
  coefficient-counit normalization node has no Lean record yet, so its planned
  use is retained by name in the proof docstring and no nonexistent import is added.

Edge cases checked before finalizing: r=0, s=0, both zero; arbitrary rank-zero
module; empty S and T; zero coefficient ring, N=1; identity and arbitrary f;
nonaffine intersections of trivializing opens. Universes keep scheme universe u
and coefficient/module universe u+1, matching the existing ordinary-etale API.
No nonzero ring, nonempty base, positive-rank, boundedness or constructibility
assumption has been added. Every universe and variable is explicitly bound.

Searches actually run (the wrapper records them in searches.jsonl):

- leanfinder, “Integration trace of an algebraic vector bundle commutes with
  arbitrary base change and ordered direct sums”: LinearMap.trace_baseChange
  and topological trivialization results; no ordinary-etale integration match.
- loogle, `CategoryTheory.Adjunction, CategoryTheory.Sheaf`: sheafification and
  abstract adjunction declarations, not the specified vector integration equations.
- grep Mathlib, `vectorBundle.*trace|trace.*vectorBundle|compactSupport.*baseChange`:
  no hits.
- rg of both project source roots for vector integration/trace and the exact item
  identifier: the existing trace and several restricted/pro-etale statements,
  but none states this arbitrary finite-ring, arbitrary Noetherian-base package.
- The existing `VectorBundleThom` trace is the inverse pro-etale Thom map in a
  fixed finite-field setting; it is not this ordinary-etale trace statement.
- New geometry searches: leansearch “Symmetric algebra vector bundle canonical
  base change morphism and direct sum product” gave IsBaseChange.pi/directSum,
  SymmetricAlgebra.ι and module base-change operations; loogle
  `SymmetricAlgebra, IsBaseChange` and grep
  `VectorBundleZeroSection|symmetricAlgebra.*baseChange` gave no hits.
- `tools/blueprint_refs.py search 'vector bundle'` and DAG/source rg found the
  bundle definition and purity direct-sum maps. Those are reused, but do not
  supply the generator-normalized cross-base map and the canonical product,
  swap and zero comparisons needed here. No new duplicate total space is defined.

No statement correction or unresolved statement dispute.

## New nodes

`def-pur-vector-trace-geometry` records canonical maps between the EXISTING
Spec Sym total spaces: a map specified by its degree-one generators; base change
using the tensor-pullback adjunction unit; the direct-sum projections and unique
product isomorphism; block swap and rank zero. Source: the item's blueprint
ancestor `cor-pur-vector-bundle-purity`, proof paragraph 2, specifically pulled-back
frames, simultaneous sum frames and coordinate permutations. The searches above
found the underlying symmetric-algebra universal property, relative Spec and
same-base maps, all reused. They did not find this needed interface. Each helper
theorem is recorded among the node's declarations, its mathematical assertion is
in the definition node and its full proof plan is in its docstring. Definitions
choose only from uniqueness statements with concrete generator/projection equations.

## Second reading by Q118

A second pass by the same worker read the source paragraph, both modules and node
records. This is not an independent-agent review; the dispatcher brief prohibits
starting other agents and assigns independent review to the maintainer.

This pass found and repaired a concrete mismatch: the old draft used Mathlib
`Scheme.Modules.pullback`. Both modules now use the project's canonical
`Scheme.Modules.tensorPullback`, and rank transport is constructed from the
unique-left-adjoint comparison with the existing rank theorem. It also checked
that q's trace is the independently constructed integration of p^*F, and that t_h
is transported from the integration of F ⊕ G rather than defined as the product
of two traces. The swap compares the prescribed coordinate permutation; the
triangle statement retains both arbitrary compactifications. No hypothesis or
clause was removed. Base change is unrestricted in f. All zero and empty cases
remain present. Definitions have real data; all postponed assertions are named
and recorded. Final server-wrapper compilation and preflight are recorded below.

Validation: scompile.py compiled both delivered modules individually in dependency
order, cleanly (geometry 5.7 s, item 19.0 s in the sandbox and 16.8 s as its actual
module). The delivery dry run then passed preflight and compilation:
`OK (dry run): commit 0ab4d2082a5 passes the preflight and compiles; nothing pushed`.
Its initial failure was only the new node's combined `[id, id]` citation syntax;
this was repaired to separate `[id]` citations and the full dry run was repeated.
