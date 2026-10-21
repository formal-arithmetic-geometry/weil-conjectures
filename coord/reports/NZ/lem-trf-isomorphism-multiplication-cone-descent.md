## Worker report

The module `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent` states
`WeilConjectures.isomorphismMultiplicationConeDescent`, with `sorry` as its only
proof. It specifies multiplication on the actual finite pullback towers, the
canonical product map on both coordinates of their entire shifted cones, and
the resulting natural isomorphism on the ordinary unbounded derived category.
Seven helper declarations expose existing functors/maps and the representative
normalization predicate for this same comparison. All definitions have real data;
none chooses an arbitrary comparison from a mere existence assertion.

Source read: the current blueprint
`main-20261015/blueprint/sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`,
(2)--(3), together with Stacks `sites-cohomology.tex`, lemma-derived-limit-is-ok
(0941), and `derived.tex`, definition-derived-limit (08TC). The theorem docstring
contains the node's ten-step proof, including the signed-coordinate conversion,
strict homotopy calculation, and localization/descent argument.

Hypotheses and objects are represented as follows.

* The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The imported coefficient
  construction supplies its canonical valuation ring, uniformizer, and quotients.
  The natural-number index `n` means exponent `n + 1`, so precisely all positive
  exponents occur.
* Schemes are `Scheme.{t}`; `t` and the coefficient universe `u` are independent.
  The small site is `W.ProEt`, with objects in `Type (t+1)` and morphisms in
  `Type t`. Module sections use the existing `max u (t+1)` universe. No equality
  between these universes or extra smallness assumption is imposed.
* Invertibility of the prime on each scheme is explicitly `_hX` and `_hY`:
  `∀ x, IsUnit (l : X.presheaf.stalk x)` and its analogue on `Y`.
* `(g : X ⟶ Y) [IsIso g]` is the scheme isomorphism. The imported
  `inverseImageFiniteCoefficientMap` and `inverseImageCompletedCoefficientMap`
  are the specified constant-section maps. The latter is the actual limit lift
  of the former, so its projection compatibility is built into the construction.
  `inverseImageIntegralModules` uses exactly the scalar action through its inverse.
* `S : CoefficientDerivedSystemCalculus l E Y` exposes the recorded derived
  reduction functor and its strict-system models. `r : IntegralComparisonRoosModel
  l E Y` exposes a normalized strict Roos identification. These are presentations
  of the functors/identifications named in the node, not an assumption of the
  desired comparison. The conclusion works for every such presentation and
  constructs its normalized representative comparison `rho`.
* A representative belongs to `(integralOperationsGoodComplex l E Y).FullSubcategory`.
  Its property is precisely K-flatness with independent coefficients and flatness
  of every term. `N : DerivedCategory (integralTowerModules l E Y)` is arbitrary,
  and `e : DerivedCategory.Q.obj P.obj ≅ N` permits every such resolution.
* `trfQuotientTowerFunctor` is exactly the strict tower assembled from
  `unrestrictedIntegralComplexFunctor` and `unrestrictedIntegralTransition`.
  Its levels are the finite reductions restricted to the completion. The other
  tower is the existing `integralOperationsPullbackTowerFunctor`, including its
  actual generator-normalized quotient transitions. No arbitrary transitions
  or independently chosen finite evaluations replace these systems.

Every conclusion is accounted for below.

* Additivity and exactness are the first three conjuncts: `.Additive`,
  `PreservesFiniteLimits`, and `PreservesFiniteColimits` for the same module
  inverse image. `trfQuotientProductComparison` is Mathlib's `piComparison` for
  the termwise inverse-image functor, and the next conjunct says it is invertible
  for the specified quotient towers. Its projection characterization belongs to
  the definition of `piComparison`.
* `j` is a natural isomorphism of functors from good representatives to strict
  towers of complexes. Its components are therefore completed-linear sheaf maps,
  commute with restrictions, differentials and every tower transition, have
  two-sided inverses, and are natural for every chain map between representatives.
* The first generator equation fixes `j` on the actual finite-pullback adjunction
  unit, restricted through `proEtaleIsoCommaArrow g U`, and sends it to `x`.
  This is an exact specification of multiplication: completed linearity sends
  a completed scalar multiple to its transported multiple through `c⁻¹`; the
  projection to each finite coefficient sheaf is locally surjective. Thus every
  finite tensor `x ⊗ a` is locally such a multiple, and this equation specifies
  `x ⊗ a ↦ c_n⁻¹(a)x`. This is also the generator convention already used by the
  dependency's actual strict pullback transition. It does not leave a choice
  of multiplication or assume a pointwise global scalar lift.
* The second equation explicitly fixes `j.inv` as the same adjunction-unit
  generator, namely `x ↦ x ⊗ 1`. Together with bundled linearity this also gives
  all its scalar formulas. Thus both directions use the canonical sheafified
  scalar-extension construction, rather than merely some isomorphic objects.
* `integralOperationsRoos` is the recorded `mappingCocone` of the actual
  `towerTransitionEndomorphism`, which is `1-s`. In the node's `(b,a)` coordinates
  it is `Cone(1-s)[-1]` with differential `(-db-(1-s)a, da)`.
* `eta` is a natural isomorphism of these entire complexes. The difference-square
  conjunct uses precisely `G.map (trfQuotientDifference ...) ≫ phi =
  phi ≫ trfInverseQuotientDifference ...`, with Lean's left-to-right composition.
* The next two equations specify `eta` through both actual cocone projections:
  `mappingCocone.fst` for the degree-zero `a` coordinate and `mappingCocone.snd`
  in degrees `(p+1,p)` for the shifted `b` coordinate. Both are exactly `phi` on
  the corresponding product. These two projections jointly determine the map,
  so neither off-diagonal entry is unconstrained. Under the normalized Roos
  identifications this is the canonical exact-product comparison: the dependency's
  signed convention is related by `(b,a) ↦ (a,-b)`, which preserves this diagonal
  map and the limit augmentation. The proof docstring records this identification.
* `TrfCompletionRoosNormalized ... rho` identifies the actual derived completion
  with the strict `H(D)` model. It tests every simultaneous strict system
  presentation satisfying `CoefficientReductionPresentation`, including all
  quotient transitions, and fixes its strict comparison on every original system
  section. Its final equation is total limit applied to `e`, followed by the
  existing normalized `integralComparisonRoosBridge`, then `H` of that strict
  tower isomorphism. This avoids reconstructing a limit map from separately
  specified derived evaluations.
* `Theta` has type `integralDerivedPullback l E g ≅ (S.reduction ⋙
  coefficientSequenceLimit l E Y) ⋙ inverseImageIntegralDerived l E g`.
  Its first representative equation is exactly the localization of
  `H(j) ≫ eta.inv`, after the canonical ambient-pullback, completion-Roos and
  exact-inverse-image comparisons. No coordinate assertion is made only after
  localization: all coordinate identities occur earlier as actual chain maps.
* The last equation quantifies every `N`, every good `P`, and every isomorphism
  `e : Q(P) ≅ N`; it expresses `Theta.app N` by that same strict map and the
  canonical comparison arrows. This is the asserted independence of resolutions.
  Naturality for every derived morphism, including inverses of quasi-isomorphisms,
  is part of the bundled natural isomorphism `Theta`, giving precisely the node's
  displayed naturality square.

Dependency declarations used (recorded entry points and their exported constructions):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and `Padic.coefficientExtensionRing`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.topology`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`,
  `completedIntegralCoefficientSheafUnrestricted`, `integralCoefficientSheafSystem`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
  Scheme-isomorphism and size-convention dependency nodes are conventions, not
  missing declarations; they are rendered by `[IsIso g]` and the explicit universes.
* `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `AlgebraicGeometry.Scheme.isoSectionwiseInverseImage_equivalence`,
  `isoSectionwiseModuleInverseImage`, `proEtaleIsoCommaArrow`.
* `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived`; its imported
  `inverseImageIntegralModules`, `inverseImageIntegralDerived`, and canonical
  coefficient maps provide the sectionwise and derived functors used here.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, used by `integralOperationsGoodComplex`.
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemCalculus`, `CoefficientReductionPresentation`,
  `coefficientSequenceLimit`, `coefficientSequenceRestriction`,
  `coefficientEvaluationSection`.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `WeilConjectures.IntegralOnSlice.completedTensor`; it exports the global
  ambient operations with their unchanged module types. The theorem uses
  `integralOperationsPullbackTowerFunctor`, `integralOperationsRoosFunctor`,
  `integralOperationsGoodComplex`, and `integralDerivedPullback`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, underlying the imported reductions.
* `Sheaf.CategoryTheory.StrictRoosComparison`:
  `CategoryTheory.strictRoosComparison`; and
  `Sheaf.Paper.ExactProductFunctorStrictLimit`:
  `CategoryTheory.exactProductFunctorStrictLimit`, supplying the normalized
  total-limit interpretation of the diagonal map.
* `Sheaf.Paper.IntegralOperationsWellDefined`:
  `WeilConjectures.integralOperationsWellDefined`, used through its canonical
  `integralDerivedPullbackComparison` and good-representative localization.
* Additional landed dependency `def-trf-integral-comparison-realization-models`,
  `Sheaf.Paper.IntegralComparisonRealizationModels`:
  `IntegralComparisonRoosModel`, `integralComparisonRoosBridge`, and
  `integralComparisonRestrictedSection`. This is the existing normalized
  total-limit model, reused rather than redefined. It has been added to
  `stmt_deps` under the explicit rule allowing an already landed node.
* Proof-only imports are the existing independent-coefficient K-flat resolution,
  pro-etale exact products, scalar-extension-through-ring-isomorphism, and
  site-derived-tensor descent modules. No new theorem is supplied for these.

Edge cases checked mathematically before delivery: the identity scheme map gives
the usual scalar multiplication and diagonal identity product comparison; `N=0`
gives zero quotient towers; exponent one is index zero and no invalid exponent-zero
case is inserted; the empty scheme gives the trivial sheaf categories without a
nonemptiness assumption. Arbitrary unbounded good representatives are permitted.
For a noncomplete object such as the uniformizer localization of the unit all
finite reductions vanish, so both completed sides vanish, as the node requires.
There is no constructibility, boundedness, or derived-completeness predicate.

Searches for an existing exact statement:

* `msearch.py ... leanfinder` queried "Exact inverse image along a scheme
  isomorphism commutes with the strict Roos complex of the finite quotient
  reduction tower by the multiplication isomorphism". Eight hits (including
  `Profinite.NobelingProof.succ_exact` and scheme pullback identities), no match.
* `msearch.py ... loogle` queried `CategoryTheory.Limits.piComparison,
  CochainComplex.mappingCone.map, CategoryTheory.Functor.mapDerivedCategory`:
  zero hits.
* `msearch.py ... grep` queried `piComparison|mappingCone.map` in `CategoryTheory`:
  25 supporting product/category hits, no exact completed coefficient statement.
* `msearch.py ... leansearch` queried "Exact additive functor preserves product
  mapping cone inverse limits": eight hits, including `Limits.isLimitOfPreserves`,
  `Functor.preservesFiniteBiproductsOfAdditive`, and `ExactFunctor`; only ingredients.
* `msearch.py ... grep` queried
  `multiplication.*cone.*descent|isomorphism.*multiplication` in `Algebra/Homology`:
  zero hits. The raw five responses are retained in the sandbox `searches.jsonl`.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` and the prescribed literal-id
  search found no exact declaration. Related principal-derived-tensor-cone,
  canonical-coefficient-pullback-reduction, isomorphism-derived-pullback, and
  isomorphism-derived-pullback-comparison-normalization declarations were read:
  they concern different coefficients, constructible restrictions, or the
  downstream parent comparison, not this entire strict-tower descent.
  The upstream-name table has no entry for this id. The blueprint ancestor search
  identifies `thm-trf-l-function-euler-product`, as in the node's source.

No statement correction, new DAG node, or dependency-record repair was needed.
No mathematical statement is disputed. The final module compiled cleanly through `scompile.py` in both its sandbox
and library module forms (30.9 s and 34.6 s); no warnings or errors were reported.
The helper-only diagnostic file was also checked and is not part of the delivery.

## Second reading by NZ

No second reading by another worker: the dispatched brief forbids starting other
agents, and the maintainer performs the independent review. I re-read the node
against the entire module. I restricted the strict natural isomorphisms to the
node's good representatives, and used the dependency's exact unit-generator
normalization with bundled linearity to avoid any unjustified global scalar lift.
Both cone-coordinate equations and every-resolution descent equation are retained.
