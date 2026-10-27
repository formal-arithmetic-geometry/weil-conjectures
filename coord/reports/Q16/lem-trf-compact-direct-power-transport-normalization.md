## Worker report

Stage 2 statement of `lem-trf-compact-direct-power-transport-normalization`.
The sole theorem is
`WeilConjectures.TraceFormulaCoefficientConventions.compact_direct_power_transport_normalization`.
Its proof is `sorry`. The auxiliary definition `compactDirectPowerTransport` has real data:
it uses the dependency's specified `compactPowerTransport` followed by H of the published,
unit-normalized `pointPowerPullbackModel`. It introduces neither a chosen map nor a
recursively defined substitute for direct power transport.

Read the item's statement, all four proof steps, every statement-dependency node and
its recorded declaration, the relevant proof-dependency declarations, and the parent
blueprint proof in main-20261015, sec-trace-formula/sk-d-weil,
`lem-trf-frobenius-operator-compact-description.proof.md`. Its second sentence specifies
the scheme-variable base-change isomorphism. The supplied DAG expands this into the
normalization being stated here. The earlier worker's objection about re-splitting does
not apply: this delivery states the already split node and changes none of its proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite-field data p, a, q, k₀, k are `T.datum : FiniteFieldDatum`. Its fields
  `prime`, `exponent_pos`, `cardinality_eq`, `card_base` and `isAlgClosure` encode
  p prime, a ≥ 1, q = p^a, k₀ = F_q, and the fixed algebraic closure k.
- The prime ℓ ≠ p and fixed coefficient closure are `T.coefficients`, including
  `prime`, `different` and `isAlgClosure`. The specified finite extension in that
  closure is `T.extension`. `T.coefficientField` is the existing small model of it;
  `T.coefficientRing` is the recorded `Padic.coefficientExtensionRing` at `T.level`,
  using its valuation ring and chosen uniformizer. `T.level_pos` is n ≥ 1. No new
  coefficient ring, uniformizer, or algebraic closure is chosen in this delivery.
- `T.X₀ : Over (Spec (.of T.datum.k₀))` is the model scheme. Its stored
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` instances give precisely
  separated finite type. `T.geometricBaseChange` is X, `T.structureMap` is a_X,
  and the target of that structure map is s = Spec k.
- `c₀ : Compactification T.X₀.hom` is one fixed compactification of the model's
  structure map. Every transport uses that same parameter. The existing
  `frobeniusCohomologyCompactification` performs its geometric base change.
- `T.finiteGlobalCompactSections c₀` is H = Fib_s Ra_X!, represented by
  `sfIntrinsicCompactSupport` of this base-changed compactification followed by
  the derived exact point-sections functor. This is the ambient realization of
  the recorded finite point fibre, not a substitute cohomology functor.
- The input `M : T.boundedConstructible.FullSubcategory` is an arbitrary object
  of D^b_c(X,A). No Weil structure, map to M, or finite Tor-amplitude is a binder.
- The integer r ≥ 1 in the node is encoded by a natural-number predecessor:
  Lean's `r : ℕ` denotes the exponent r+1. Thus zero includes exponent one, and
  every positive exponent occurs. The coefficient level is independently any
  positive `T.level`.
- Geometric Frobenius g is `T.datum.geometricGaloisFrobenius T.X₀`, using the
  inverse q-power field Frobenius. `T.frobeniusPullbackPower r` is the actual
  ordinary constant-coefficient derived pullback along g^(r+1). It is P_(r+1),
  and `T.frobeniusPullbackPower 0` is T = P_1.
- The specified d_(r+1) is the existing `T.frobeniusPullbackPowerComparison r`.
  It has identity at index zero and is recursively built from the canonical
  pullback composition comparison, with no arbitrary natural isomorphism input.
  `trfPositiveFunctorPower (T.frobeniusPullbackPower 0) r` is exactly T^(r+1)
  with the node's successor convention. It is not replaced by a functor power
  with a different reassociation convention.
- `T.compactDirectPowerTransport c₀ M.obj r` is tau^(r+1) from the recorded
  `compactPowerTransport`, which forms point transport along h^(r+1) and then
  the fibre of the direct power-square exchange using c₀. The only added factor
  is H of `pointPowerPullbackModel`, identifying the dependency's intrinsic
  pullback presentation with the tensor-pullback presentation used by d_(r+1).
  The definition case-splits the positive coefficient level to call the existing
  n+1 API, covering all levels, including one.
- The already published `T.finiteGlobalCompactStep c₀` is the specified
  degree-one transport from `frobeniusCompactTransportFinite`, expressed in
  these same tensor coordinates with g^1 = g inserted.
- `T.finiteGlobalComparedTransport c₀ M.obj r` is S_(r+1,M). Its definition is
  `finiteGlobalRepeatedTransport` (exactly r+1 degree-one factors) followed by
  `H.map ((T.frobeniusPullbackPowerComparison r).inv.app M.obj)`.
- The first conjunct says P_(r+1)M lies in D^b_c; the second says T^(r+1)M does.
  The third conjunct is exactly S_(r+1,M) = tau^(r+1)_(c,M). The final two
  conjuncts assert that both maps are isomorphisms. Their endpoints are the
  actual H(M) and H(P_(r+1)M) in the derived coefficient-module category. The
  bounded finite-cohomology coefficient category is a full subcategory, so
  stating the equality and invertibility on these underlying derived objects
  expresses the same assertion, before applying any cohomology functor.

Dependency declarations reused (module followed by relevant declarations):

- `Sheaf.Paper.TraceFormulaCoefficientConventions`: the structure and its
  `coefficientField`, `coefficientRing`, `geometricBaseChange`, `boundedConstructible`.
- `Sheaf.SixFunctors.SchemeFrobenius`: `FiniteFieldDatum.geometricGaloisFrobenius`
  and `geometricGaloisDerivedPullback`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`
  and its category; the imported `Compactification` supplies c₀ itself.
- `Sheaf.TraceFormula.CompactFrobeniusTransportComposition`: `compactPowerTransport`,
  `compactPowerCohomology`, `compactPowerPullback`, `compactPowerPullbackStep` and
  `compact_frobenius_transport_composition`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`:
  `frobeniusCohomologyCompactification`, `frobeniusCompactTransportFinite` and
  `frobeniusCohomologyTransportFinite`.
- `Sheaf.Paper.FrobeniusPullbackComparisonCoherence`: `trfPositiveFunctorPower`,
  `frobeniusPullbackPower`, `frobeniusPullbackPowerComparison` and
  `frobenius_pullback_comparison_coherence`.
- `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator`: `finiteGlobalCompactSections`,
  `finiteGlobalCompactStep`, `finiteGlobalRepeatedTransport` and
  `finiteGlobalComparedTransport`. The already landed `def-trf-frobenius-operators`
  is added to stmt_deps to cite these definitions instead of copying them. Although
  that module also defines operators on Weil complexes, these four definitions
  take arbitrary ambient complexes, imposing no Weil or finite-Tor hypothesis here.
- `Sheaf.TraceFormula.PointTransportComposition`, publicly exposed by the compact
  composition dependency: `pointPowerPullbackModel`, the canonical presentation iso.
- Proof-only imports are the recorded modules for
  `FiniteFieldDatum.frobenius_square_cartesian`,
  `isomorphismFiniteDerivedPullback_termwise`, `NaturalTransport.compared_eq` and
  `frobeniusCohomologyTransport_isIso`. Their signatures and proof docstrings were
  read; the theorem docstring gives all four DAG proof steps and these inputs.

Edge cases checked: exponent one uses identity d₁ and precisely one transport;
coefficient level one is included in the successor branch; zero complexes and the
empty scheme are allowed; arbitrarily large positive exponents have the same
compactification; coefficients of nonzero torsion length are not assumed to be fields;
constructible complexes of infinite Tor amplitude and those with no Weil structure
are still permitted. The zero coefficient-level branch is eliminated only by the
existing `T.level_pos`, not by adding a restriction. All variables and the size universe
are bound explicitly; both autoImplicit options are false.

Searches actually run through msearch.py:

- LeanFinder, query: "Direct compact support Frobenius power transport equals repeated
  degree one transport under canonical derived pullback comparisons". Eight results,
  including `coe_iterateFrobeniusEquiv`, `iterateFrobeniusEquiv_one`,
  `iterateFrobeniusEquiv_apply`, `iterateFrobeniusEquiv_eq_pow`,
  `iterateFrobeniusEquiv_add`, `IsPurelyInseparable.iterateFrobeniusₛₗ`,
  `iterateFrobeniusEquiv_symm_add`. These are field/ring Frobenius statements;
  none is the derived compact-support normalization.
- Loogle, query: `"pullback", "Iso"`. Twelve results concern categorical pullback
  cones and comparison maps, including `Limits.pullbackComparison`; none states
  this cohomological transport identity.
- Mathlib grep, query: `frobenius.*transport|transport.*frobenius|compact.*baseChange`
  restricted to `AlgebraicGeometry`. One hit: QuasiCompact.lean, line 165,
  `quasiCompact_isStableUnderBaseChange`, unrelated to the asserted transport.
- LeanSearch, query: "Compactly supported derived cohomology transport along a Frobenius
  power equals iterated degree one transport". Eight results on ring Frobenius,
  perfection, Witt vectors and compactly supported derivatives, including
  `LinearMap.iterateFrobenius`, `RingHom.iterateFrobenius_comm` and
  `HasCompactSupport.iteratedFDeriv`; no exact match.
- Read-only rg searches of `lean/WeilConjectures`, `lean/Sheaf/TraceFormula` and
  `lean/Sheaf/Paper/Frobenius*` for compact-power transport and comparison names,
  and grep of the item id in `lean/WeilConjectures`. No whole-item declaration.
  The project search did find all the published constructions reused here. The parent
  `frobenius_operator_compact_description` restricts to strict Weil complexes and
  states an operator formula, so it is not an existing match for arbitrary M.

No statement correction or disputed statement. No new DAG nodes or dependency-module
repairs. Only the item's lean record and the addition of the existing definition node
to stmt_deps change. This is stage 2, not a repeated stage-1 split.

Validation: scompile.py compiled the delivered module in sandbox and final module
positions, in 19.4 s and 15.0 s, respectively. Both passed without errors or non-sorry
warnings. The source contains one postponed theorem and no postponed definition data.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
