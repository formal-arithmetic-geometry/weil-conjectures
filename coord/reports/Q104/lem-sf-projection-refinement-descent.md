## Worker report

The module `Sheaf.SixFunctors.ProjectionRefinementDescent` states the complete finite
refinement/descent assertion as `WeilConjectures.ProjectionRefinementDescent.finite_descent`
and its intrinsic system clause as
`WeilConjectures.IntegralSystemRealization.projectionRefinementSystems`.
Both theorem proofs are `sorry`. All helper definitions have real data and merely specialize,
transport or restrict already recorded constructions; no new independent notion is introduced.
The DAG statement, dependencies and proof are unchanged; only `lean` is set.

Hypothesis and clause correspondence:

* The global finite field and algebraic closure are `D : FiniteFieldDatum`; the prime distinct
  from the characteristic is `C : D.CoefficientDatum`, including `C.different`. The finite
  extension is `E`, `[Field E]`, `[Algebra ℚ_[C.l] E]`, and
  `[FiniteDimensional ℚ_[C.l] E]`. The actual ring and uniformizer quotient are
  `Padic.coefficientExtensionRing C.l E (n+1)`, with its canonical universe lift
  `Coefficient C.l E n`. Indexing by `n : ℕ` and exponent `n+1` includes every positive
  exponent, including exponent one. `coefficientFinite` applies the recorded finiteness
  theorem; it is not an added hypothesis.
* `_S : SixFunctorOperationDatum D C E (n+1) (Nat.succ_pos n)` is the requested operation
  datum, not a datum assuming projection invertibility. It supplies the context; the finite
  maps themselves are the recorded canonical constructions and do not depend on an extra
  chosen projection or comparison.
* `X`, `Y` are `Scheme.{u}`, with `Over (Spec (.of D.k))`, `LocallyOfFiniteType` and
  `QuasiCompact` structure maps. `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f` and
  `QuasiCompact f` express the separated finite-type k-morphism. Neither structure map has
  an `IsSeparated` hypothesis.
* The ambient category `ProperOpenDerived (Coefficient ...) X` is precisely the ordinary
  fixed-scalar small pro-etale derived category. `boundedConstructible` is the inverse image
  of the recorded `intrinsicFiniteTorsionConstructible` under
  `Scheme.sfIntrinsicDerivedEquivalence`; `finiteTor` is the identical transport of the
  recorded `finiteTorConstructible`. Thus the full subcategories for `K` and `L` express
  exactly `D^b_c(X,A)` and `D^b_ctf(Y,A)`. No Tor condition is imposed on K, no alternate
  constructibility definition is used, and the full input categories retain every morphism.
* `tensorInput f K L` is the actual derived tensor of K with the recorded derived pullback
  of L. The first conjunct asserts its bounded constructibility and actual origin witnesses
  (up to isomorphism) for both K and this tensor. `RefinementFiniteLevelOrigin` retains the
  bounded-below etale object, its pro-etale image and its comparison isomorphism, exactly as
  in the recorded dependency. Those witnesses are conclusions, not assumed existence.
* A compactification is the existing `Compactification f`; `r : c.Refinement d` is the proper
  refinement with its two factorization equalities. No Cartesian assumption occurs.
  `image c` is the existing `rightDerivedLowerShriekOfCompactification`.
  `theta r K O e` is `image c` of `e.symm`, then precisely
  `refinementComparisonAtWitness` (the compositor followed by the proper image of the inverse
  proper/open comparison), then `image d` of `e`. This is the specified theta on the object K
  presented by its retained witness; it never substitutes an arbitrary comparison.
* `refinementLaw` is the displayed equation in Lean's left-to-right composition order:
  `PF_c ≫ theta_T.hom = (tensor.map theta_K.hom).app L ≫ PF_d`.
  It is asserted for every refinement and every pair of retained witnesses and identifying
  isomorphisms. The preceding existence conclusions prevent a vacuous witness domain.
  Each `PF` is the upstream `projectionMapOfCompactification` with exactly the counit
  projection/open-tensor/pullback-composition formula of `def-exchange-projection`.
* The existential `rho` is a family of natural isomorphisms of compactification functors on
  the full bounded constructible category. Its first equation normalizes each component to
  `theta_r.symm ≪≫ theta_s` for EVERY common refinement and both its arrows. Its second
  equation is the triple cocycle. This simultaneously specifies independence of the chosen
  common refinement and of the origin presentation.
* For every reference compactification `c₀`, `tau : source c₀ ⟶ target c₀` is an actual
  natural transformation on the product of the two full input categories. The last equation
  compares its component with `PF_c` for EVERY c using that same rho, at K and at its tensor.
  It expresses descent to the common compact-support functor and compactification
  independence. Because tau is a NatTrans on a product category, naturality is required in
  both K and L. At c=c₀ the cocycle and invertibility force rho to be identity and tau to be
  exactly the specified PF component; this does not allow an unrelated map.
* The second theorem states the local equality inside `System l E D` itself. It uses the
  actual `Operations`, `Realizations`, `z.properOpen.gamma`, `z.openComparisons.projection`,
  `z.compositors.square` and counit-defined `properProjection` of the recorded realization.
  Its geometry is the refinement square `(k,id,a,i)` with `k ≫ a = i`; setting
  `k=j₁`, `i=j₂`, `a` the proper refinement, and `N=P_p₂ L` gives exactly the local equation
  used in the finite calculation. The canonical identity-push, identity-pull and square
  identifications are retained explicitly, rather than implicitly identifying different
  objects. Both sides are system composites; neither evaluation nor restriction of scalars
  appears. The unbounded intrinsic equality requires no bounds on M,N; passage through the
  realization theorem retains that theorem's stated common-bound/origin domain. No claim
  of detection by finite evaluations or realization outside that domain is made.

Source checked: `literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/`
`fix-prop-projection-formula.proof.md` delegates refinement to `prop-sf-pf-coherence`.
The node gives the expanded local calculation; its nine proof steps are reproduced in the
finite theorem docstring, including identification of the clopen Gamma with the witnessed
proper/open map. The local Stacks sources were opened: `more-etale.tex`, labels
`lemma-shriek-proper-and-open` (0F7B) and `lemma-shriek-lqf-and-proper` (0F7G).
Neither assumes Cartesianity for this proper/open comparison.

Dependency declarations used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `.CoefficientDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the quotient is the imported
  `Padic.coefficientExtensionRing` with its recorded integer ring and uniformizer.
* `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData` and
  `ExchangeProjectionStage.projection` identify the prescribed finite specialization.
  The actual finite statement uses
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`:
  `AlgebraicGeometry.ProEtale.projectionMapOfCompactification`,
  `derivedTensorRightDerivedLowerShriek`,
  `rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar`.
* `Sheaf.Paper.QcqsCompactSupportRealization`:
  `WeilConjectures.sfQcqsCompactSupportRealization` fixes the nonseparated-base convention;
  its finite candidate is the existing `rightDerivedLowerShriekOfCompactification`.
* `Sheaf.Paper.FiniteTorAmplitudeSites` (and its public `FiniteTorAmplitude` import):
  `WeilConjectures.finiteTorConstructible`.
* `Sheaf.Paper.RefinementComparisonIsomorphism`:
  `AlgebraicGeometry.ProEtale.RefinementFiniteLevelOrigin`,
  `refinementFiniteLevelFixedObject`, `refinementComparisonAtWitness`.
* `Sheaf.SixFunctors.ProperOpenProjectionMate`:
  `AlgebraicGeometry.ProEtale.ProperOpenDerived`, `ProperOpenPull`, `ProperOpenTensor`,
  `properOpenProjectionMate`, and
  `WeilConjectures.IntegralSystemRealization.properOpenProjectionMateSystems`.
* `Sheaf.Paper.CompactificationCoherence`:
  `AlgebraicGeometry.ProEtale.compactification_coherence`.
* `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `WeilConjectures.IntegralSystemRealization.Realizations`, `ProperOpenCoherence.gamma`,
  `properProjection`, and the public `Operations`, `System`, `pull`, `calculus` interfaces.
* Canonical realization transport is `AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence`
  from `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`, already publicly imported
  by the recorded dependency closure. `boundedConstructible` uses the dependency's existing
  `intrinsicFiniteTorsionConstructible`; it does not redefine intrinsic constructibility.
* Every stated proof dependency's recorded module is included as a plain `import` unless
  it is also a statement dependency (then `public import`), preserving the stage-3 proof plan.

Searches actually run:

* `msearch.py ... leanfinder`: "Projection formula maps commute with compactification
  refinement comparisons and descend independently of compactification" returned eight
  unrelated profinite/LightProfinite projection lemmas; no matching statement.
* `msearch.py ... loogle`: `"projection", "refinement"` returned zero hits.
* `msearch.py ... grep`: `refinement.*[Pp]rojection|[Pp]rojection.*[Rr]efinement` in
  `CategoryTheory` returned zero hits.
* `msearch.py ... leansearch`: "Projection formula transformations respect compactification
  refinements for derived sheaves" returned eight unrelated sheafification, projective
  resolution, scheme-cover and profinite projection results; no matching statement.
* `rg` over `lean/WeilConjectures` and `lean/Sheaf`, including the exact node id, found
  `PfRefinementCompatibility`, `FixProjectionCompactificationComparison`,
  `ProjectionIntegralCoherenceRealization` and upstream etale projection refinement modules.
  Full signatures/docstrings were read: `pf_refinement_compatibility` assumes separated
  structure maps and supplied witnesses; `FixProjectionCompactification.comparison` has a
  finite common-refinement equation with supplied witnesses, but no domain-preparation
  conclusion or intrinsic system local identity. The upstream etale refinement theorem
  requires Cartesianity. None states this complete node. Their canonical operations and
  recorded theta are reused, not duplicated.
* `rg` in `dag/lean_names_upstream.json`, Mathlib and both project source roots found no
  collision for the new namespace or `projectionRefinementSystems`.

Edge cases checked semantically before drafting: identity refinement (theta becomes identity),
K=0, L=0, empty X, exponent one (`n=0` in the chosen indexing), and the non-Cartesian fold
refinement `pt ⊔ pt → pt`. The signatures exclude none of these. Over `R/t²`, K=`R/t` has
infinite Tor amplitude but is included: only L is in `finiteTor`. Nonseparated finite-type
structure maps are included. All site objects and coefficient categories preserve the
recorded universe u/u+1 convention; no universe equality is added. No statement dispute or
node correction was needed.

Validation: scompile.py compiled the complete module in sandbox and library module modes;
the first complete pass had only a long-line warning, repaired by wrapping that line.
Final clean compilation and delivery preflight are recorded below.

## Second reading by Q104

Self-check by the assigned worker (no second agent was started, as the dispatcher brief
explicitly forbids it); the maintainer supplies the independent review after delivery.
Read the node and final Lean side by side. Checked each clause listed above, the order of
composition in theta and PF, the rho normalization on both common-refinement legs, the
NatTrans domain (full bounded constructible times full finite Tor), and the system equation's
exact specialization at the identity vertical map. The first compilation exposed one
101-character line; it was wrapped. No mathematical hypothesis or clause changed.

Final validation: the complete module compiled cleanly in sandbox and library modes.
`deliver2.py Q104 lem-sf-projection-refinement-descent --no-push` returned
`OK (dry run): commit 15473867b1d passes the preflight and compiles; nothing pushed`.
The delivered node differs from its base only in `lean`; the signature matches the file
verbatim, every declaration is recorded, and there are exactly two postponed theorem proofs.
