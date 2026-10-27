## Worker report

The module states `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1KernelScalarNormalization`.
The node statement, proof and dependencies are unchanged. Its helper structures and
map definitions belong to this node and have real data. The only postponed proof is
the named main theorem, whose docstring includes all seven accepted proof steps.

Source read: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
"Reduction of the triangle identities" and "Levelwise check". This is an auxiliary
node of the unit, rather than a change to the unit statement.

Hypotheses and objects:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- The arbitrary base is `(S : Scheme.{u})` and `hS : IsUnit (l : Γ(S, ⊤))`.
  There is no Noetherian, finite-type, separated-base, or characteristic restriction.
- `SpTowerShriek.R l E n` is the actual quotient of the recorded integer ring by
  `(ell)^(n+1)`; `Arings` is its constant-sheaf system with quotient transitions.
  Index `n : ℕ` represents every positive paper level `n+1`, including level one.
- `Presentation l E S hS` uses the published ordinary derived category of strict
  semilinear towers, its section-normalized geometric calculus, and `TowerClasses`.
  It supplies `ProjectiveLine S`, `diagonalSurface S`, both Bool-indexed projections,
  the diagonal, and the positive supported `p.delta`. Its `C` and `domain` are the
  full bounded-below categories with retained `SpTowerShriek.Origin` witnesses;
  these are the published `FixedEtaleOriginWitness` coordinates. F and G are the
  existing `Presentation.F` and `Presentation.G`. The scalar assertion needs no
  object argument from these domains.

Every conclusion:

- `KernelSplittingData.splittingQ_hom` fixes the twisted q-splitting to the biproduct
  of the unit adjunct and the positive hyperplane Chern adjunct. `traceQ` identifies
  its inverse-second-projection trace with the recorded `p.trace`.
- `splittingProjection_hom` does the same for each product projection. Its hyperplane
  is `Scheme.Pic.map` of `hyperplanePic S` along the OTHER projection. This avoids
  confusing the absolute base hyperplane with the relative one for p_i.
- `CoefficientPullback` and `LinePullback` retain the existing section normalization
  on constants and pure root tensors, including the quotient/power transitions.
  `kernelShiftedLine` adds the canonical shift comparison. None is an arbitrary
  endpoint isomorphism or a mere existence choice.
- `exchange` is explicitly the corresponding proper mate `exchange` or
  `exchangeSwap`, followed by direct image of this shifted-line comparison.
  `sumComparison` is the biproduct comparison using the specified coefficient and
  line pullbacks. The two cases are written explicitly so that double Boolean
  negation causes no dependent-type identification problem.
- `KernelScalarNormalization.splitting_base_change`, `inverse_base_change`, and
  `trace_base_change` are the three requested equations of actual tower-derived
  morphisms, for BOTH values of `a : Bool`. The exchange and sum comparisons are
  also asserted invertible.
- `alpha_iso` says `sourceUnitAt` is the canonical composition isomorphism for
  p_i Delta = id. `KernelSplittingData.scalar` is exactly that source map followed
  by direct image of `p.delta` followed by the splitting trace. `scalar_identity`
  states both c_i = identity.
- `KernelFiniteNormalization.alpha`, `pushed_delta`, `trace`, and `composite` are
  actual `WordComparison` equations with the published unit/root/site-mate
  coordinates. Their endpoint comparisons are invertible, with their ordinary
  section and K-flat normalization inherited from `ProjectiveCoordinates`.
  `kernelFiniteScalar` uses `projectiveLineDiagonalAlpha`, `EtaleWords.delta`, and
  the finite trace from the unit/Chern splitting on P, transported through the
  canonical product chart. Its `finite_identity` gives both finite integral
  equations. `finiteNormalization` and `levels` quantify over EVERY positive level.
- The finite `delta` is the positive supported Cartier boundary constructed by
  `cartierReducedEtale`, so the sign is delta u = c1(O(Delta)); no arbitrary class
  or sign parameter is substituted. `cartier` provides its well-typed divisor.
- `degree_zero_lift` is the unique abelian tower endomorphism whose single-functor
  image is c_i. `degree_zero_detection` states componentwise equality detection
  only for these abelian coefficient-tower endomorphisms. There is no general
  derived-evaluation faithfulness assertion.

Recorded dependency declarations used (their signatures/docstrings were read):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the original coefficient integer
  ring imported through that module.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`:
  `AlgebraicGeometry.ProEtale.spCoefficientTowers`, `spEllIdeal`, and quotient system.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `sp_coefficient_towers_abelian`, `SpCoefficientTowersAbelian`, and exact evaluations.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, via `SpTowerShriek.Origin`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace`, with two homogeneous coordinates.
- `Sheaf.Paper.SmoothPurityTowerClasses`:
  `AlgebraicGeometry.ProEtale.TowerClasses`; its canonical unit, Chern, supported
  diagonal, projective splitting and trace constructions are reused unchanged.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and the recorded
  actual operations, composition and evaluation-mate interfaces it supplies.
- `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals`:
  `Etale.ArbitraryBaseFiniteP1Splitting`, its `trace`,
  `ordinaryFiniteP1DiagonalChartMap`, and `exists_arbitraryBaseFiniteP1Integrals`.
- Mathlib `Algebra.Homology.DerivedCategory.FullyFaithful`:
  `DerivedCategory.instFullSingleFunctor` and `instFaithfulSingleFunctor`, at zero.
- Proof dependency `Sheaf.Paper.TowerP1EtaleOriginComparisons`:
  `towerP1EtaleOriginComparisons`, with its canonical `ProjectiveCoordinates`,
  `WordComparison`, `sourceUnitAt`, and both proper-exchange mate formulas.
- Proof dependencies `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`
  (`ProjectiveSpace.twist`) and `Sheaf.Paper.TowerChernPullback`
  (`AlgebraicGeometry.ProEtale.tower_firstChern_pullback`).

The published foundational Presentation definitions live in
`SmoothPurityTowerP1Adjunction`; only those definitions, reexported by the comparison
module, are used. Its downstream `exists_towerP1Adjunction` theorem is not invoked.
A future proof-import insertion from that foundational module back to this module
would be an import cycle and must be omitted as prescribed by stage 2 rule 7.

Edge cases checked before writing: empty base schemes; non-Noetherian and
non-quasi-compact bases; both projections; positive level one (`n=0`); ramified E
(the finite ring is ell-power, not uniformizer-power with the same exponent);
and zero objects in the domain. The only degree-zero detection is between maps of
A_P, so no level-faithfulness assumption for arbitrary derived morphisms is needed.
No statement correction or dispute was found.

Searches actually run:

- msearch leanfinder: "Projective line tower splitting trace base change diagonal
  scalar equals identity". Eight hits, including `Algebra.normalizedTrace_self`,
  `Algebra.trace_self`, and `LinearMap.trace_baseChange`; these are algebra traces,
  not this projective-line tower statement.
- msearch loogle: `DerivedCategory.singleFunctor, Function.Bijective`.
  Zero hits. The existing fully faithful single-functor interfaces were read directly.
- msearch grep: `trace.*baseChange|diagonal.*trace`, Mathlib CategoryTheory.
  Zero hits.
- rg in both project source roots for kernel scalar normalization, tower P1
  normalization, and trace base change: found the existing P1 coordinate modules
  and unrelated algebra trace declarations, but no existing declaration of this node.
- grep for the exact node id under WeilConjectures: no hit.
- Full-name rg in dag/lean_names_upstream.json and both Lean roots for
  `KernelSplittingData`, `kernelShiftedLine`, and `towerP1KernelScalarNormalization`:
  no collision.

Validation: compiled through scompile.py and dry-run deliver2.py; see the final
compiler/preflight output for the completed validation. All writes were in the sandbox.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
