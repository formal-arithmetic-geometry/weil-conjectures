## Worker report

The module states `AlgebraicGeometry.Etale.etaleClosedChartExceptionalPreservation` for
lem-pur-etale-closed-chart-exceptional-preservation. It contains one postponed theorem, with
all eight proof steps in its docstring, and four fully written helper definitions belonging
to this node. No independent notion, dependency module, or statement correction is needed.
The node's statement, dependencies, proof and other fields are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field of positive characteristic is `(k : Type u) [Field k] (p : ℕ) [CharP k p]`
  with `hp : 0 < p`. The distinct coefficient prime is `(ell : ℕ) [Fact ell.Prime]`
  and `hell : ell ≠ p`.
- The finite extension is `(E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]`
  `[FiniteDimensional (Padic ell) E]`. The level is `(n : ℕ) (hn : 1 ≤ n)` and the
  coefficient ring is exactly `Padic.coefficientExtensionRing ell E n`, not a new
  coefficient ring or a pro-etale model. E uses the established small-etale coefficient
  universe u+1; increasing the universe includes every finite extension.
- X and Y have `[X.Over (Spec (.of k))]` and its Y analogue, with separated,
  locally-of-finite-type and quasi-compact structure maps. Finite type means precisely
  the last two conditions. `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` is the k-morphism.
- U and V are affine schemes with `[IsAffine U] [IsAffine V]`; u and v are open
  immersions into X and Y. This is the usual presentation of affine open subschemes,
  invariant under their unique identification with the corresponding open ranges.
- `(r : ℕ)` includes zero. P is Mathlib's
  `AffineSpace (ULift.{u} (Fin r)) V`; pi is its first projection `P ↘ V`.
  The map i has `[IsClosedImmersion i]`. The chart identity is
  `h : u ≫ f = (i ≫ (P ↘ V)) ≫ v`. It also implies f(U) is contained in V, so a
  second set-inclusion hypothesis would add redundant data.
- `ClosedChartExceptionalPreservation` installs finiteness using the recorded positive-level
  theorem and obtains the Noetherian and compactification instances from the stated geometry.
  These are consequences, not additional theorem hypotheses. It concludes an annihilator
  `hA : (ell^n : A) = 0`, needed only to construct the recorded finite Tate twist.
- The ambient functor is the ordinary `rightDerivedLowerShriek`, defined from a compactification
  by the recorded `rightDerivedLowerShriekOfCompactification`. Its right adjoint is represented
  by an arbitrary F with `adjF : Rf_! ⊣ F`. This accounts for the noncanonical presentation of
  the Brown right adjoint. Existence is supplied by thm-amb-etale-exceptional-adjoint. The global
  chosen compactification and any fixed compactification in the node are identified by the
  existing canonical `rightDerivedLowerShriekIso`; transporting adjF along this iso gives the
  formulation for that fixed compactification.
- `closedChartTwistedPullback A N hA V r` is literally exact pi-pullback followed by right
  derived tensor with `singleFunctor 0 (Scheme.finiteEtaleTateTwist P N A hA r)` and the
  shift `2 * (r : ℤ)`. Thus the right functor in the isomorphism is exactly
  `v^* ⋙ pi^*(-)(r)[2r] ⋙ Ri!`. The left functor is `F ⋙ u^*`.
- The closed right adjoint is `(R(lowerStar (ModuleCat A) i)).rightAdjoint`, supplied by
  lem-exc-closed-ambient. Closed direct image is exact, so its R is its termwise descent,
  as in that dependency. No alternate closed-exceptional construction is introduced.
- `closedChartCompactSupportComparison` constructs lambda with actual compact-support
  compositors, the chart equality, and the canonical proper/open comparison maps.
  Its direction is `u_! ⋙ Rf_! ≅ (Ri_* ⋙ Rpi_!) ⋙ v_!` (Lean composes left to right).
- The universal purity-adjunction presentation is intentional. The assertion includes
  `Nonempty (Rpi_! ⊣ closedChartTwistedPullback ...)` and, for *every* such `adjπ`, a unique
  functor isomorphism e satisfying the pasted counit equation. In particular apply it to
  the integration-normalized adjunction of thm-amb-vector-bundle-purity. No arbitrary
  comparison iso is supplied as a hypothesis, and no arbitrary existential adjunction is
  substituted for the specified normalization: the equation holds for the specified
  adjunction because it holds for every adjunction presentation. This is the usual
  choice-independent formulation, as also used for adjF.
- The displayed equation is `lambda.hom.app (u^* F L) ≫ J.map (e.hom.app L) ≫
  epsilon^J.app L = epsilon^(Fu).app L`. `epsilon^J` is the counit of
  `(adjI.comp adjπ).comp adjV`, and `epsilon^(Fu)` is that of `adjU.comp adjF`.
  It is exactly proof step 4's equation, with a unique natural iso rather than objectwise
  choices. L ranges over all of `DerivedCategoryModule A Y` in this equation.
- The final clause separately quantifies L, assumes the recorded
  `DerivedCategory.isBoundedConstructible A Y L` and `∃ a b, hasTorAmplitudeIn A Y a b L`,
  and gives those same two properties for the literal right-hand expression on U.
  No condition on F(L), or even boundedness on L for the isomorphism clause, occurs.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the exact `coefficientExtensionRing`.
- def-weil-pbc-scheme-conventions is a convention-only record; its Mathlib Scheme,
  IsAffine, IsOpenImmersion, IsClosedImmersion, IsSeparated, LocallyOfFiniteType and
  QuasiCompact notions are used directly.
- def-sbc-affine-space is a Mathlib leaf:
  `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace` and its `over`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification` and `rightDerivedLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification` (the current upstream
  signature works for all compactifications with finite coefficients).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  the ordinary `DerivedCategoryModule` encoding.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `DerivedCategory.isBoundedConstructible` (the finite-value constructibility predicate).
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` and its upstream coefficient import:
  `DerivedCategory.hasTorAmplitudeIn` (not the alternate upstream finite-Tor predicate).
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion` and its selected right adjoint.
- `Sheaf.Targets.VectorBundlePurity`: `vectorBundlePurity`, the integration-normalized
  purity adjunction, on all ordinary unbounded inputs; the positive finite twist is the
  imported `Scheme.finiteEtaleTateTwist`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleLowerShriekCongr`.
- `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion`:
  `rightDerivedLowerShriekIsoOfIsOpenImmersion`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar`:
  `rightDerivedLowerShriekIsoRightDerivedLowerStar`.
- The recorded modules for every stated proof dependency are imported non-publicly unless
  already public for the statement. Mathlib leaves without modules remain available through
  these imports. In particular the closed-support Tor theorem is a proof import.

Edge checks: r=0 uses the zero-variable affine space, degree-zero constant Tate sheaf and
shift zero. n=1 remains included. Empty U and V are allowed affine schemes; there is no
Nonempty scheme hypothesis. The complement W may be empty, and its vanishing/constructibility
bounds are then automatic. Zero L and zero Tor intervals are permitted by the recorded
predicates. No separable-closedness of k, global cohomological dimension of k, or boundedness
of the ambient right-adjoint value has been inserted. Unbounded inputs are permitted in all
natural-isomorphism and counit binders. The geometry definition uses real existing proofs
and contains no sorry; only the named final theorem is postponed.

Searches for an existing exact statement:

- msearch LeanFinder, query “exceptional inverse image closed immersion affine space chart
  counit bounded constructible Tor amplitude”: eight affine-space/chart hits, no match.
- msearch Loogle, query “Adjunction.rightAdjointUniq, AlgebraicGeometry.Etale”: no hit
  (the service reported unknown identifier for the short qualified name).
- msearch Mathlib grep, query `exceptional|rightAdjointUniq` in
  CategoryTheory/Adjunction: found the general uniqueness-of-right-adjoints construction,
  not the geometric theorem.
- msearch LeanSearch, query “exceptional inverse image closed immersion affine space
  constructible Tor amplitude”: eight closed-immersion definitions/lemmas, no match.
- rg of WeilConjectures and Sheaf for closedChart, closed_chart and the item id found
  `preservationClauses_closedChart` in upstream Derived/PurityPreservation. That result
  uses its different constructibility predicate and a composite exceptional functor;
  it does not state the requested counit-normalized natural isomorphism or literal
  finite-Tate expression. Therefore it is not an existing exact match. The item-id
  search in WeilConjectures had no hit. Further rg searches located the existing
  ordinary Tate twists, unbounded compact-support compositors, proper/open normalizations
  and closed-support right adjoint used here; none is redefined.

Validation: scompile.py compiled both the sandbox and actual library module names cleanly
(24.1 s and 23.7 s). Every variable and universe is explicitly bound; autoImplicit is false.
No declaration other than the final theorem uses sorry. No STATEMENT-DISPUTED issue found.

## Second reading by NI

I reopened the node and the full module and checked the binders and expanded definitions.
This is a local second pass, not a claim of an independent agent review; the dispatch brief
prohibits starting other agents and assigns independent review to the maintainer.
I checked the coefficient level n, the literal pi projection, both functor directions,
the tensor-before-shift order and the sign 2r, the source of lambda at u^* F L, and both
pasted adjunctions in the counit equation. I also checked that the bounded-constructible
predicate is the dependency's finite-value version and that the preservation clause is
about Ri! of the expression, with no boundedness condition on F(L). The universal adjπ
binder includes the prescribed integration-normalized adjunction; its existence is an
asserted conclusion rather than a new hypothesis. No statement changes were needed.
The first compiler pass caught a dependent compactification transport and one unmatched
parenthesis; these were repaired using the existing unboundedEtaleLowerShriekCongr and
the correct grouping. The final file compiles cleanly.
