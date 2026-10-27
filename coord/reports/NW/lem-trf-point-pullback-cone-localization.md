## Worker report

The delivery states `WeilConjectures.PointPullbackCone.pointPullbackConeLocalization`
in `Sheaf.Paper.PointPullbackConeLocalization`. Its proof alone is `sorry`.
The six helper declarations contain real data and reuse the published functors,
full subcategories, strict towers, Roos construction and normalized comparisons.
No node statement, dependency list, proof plan or existing module is changed.
There are no new nodes or dependency repairs.

The previous worker's stale-dispatch diagnosis concerned the stage-1 split. The
Q13 PASS dated 2026-10-22 reviews that split, not a Lean statement: the base node
has no `lean` record and no `reviewed_lean`, and the Q13 report explicitly says
no Lean was written. This delivery performs the dispatched stage-2 task without
reopening or altering that split.

Hypothesis and clause correspondence:

- The finite-field datum is `(D : FiniteFieldDatum.{u})`, which contains the prime,
  positive exponent, cardinality, finite field and its algebraic closure.
  `(l : ℕ) [Fact l.Prime]` and `_hl : l ≠ D.p` are the excluded-characteristic
  prime. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` give the finite coefficient extension.
  The valuation ring, uniformizer ideal powers, positive quotients, their constant
  sheaves and their completed limit are the existing Padic and integral-coefficient
  constructions, not new parameters. Index `n : ℕ` denotes exponent `n+1`.
- The point is `Spec (.of D.k)`. Its site is `Scheme.ProEt.topology` (objects
  in `Type (u+1)`, morphisms in `Type u`). The completed ring is
  `completedIntegralCoefficientSheafUnrestricted`, and its modules are
  `integralTowerModules l E (Spec (.of D.k))`.
- The geometric Frobenius is `(frobeniusPointIso D).hom`, literally Spec of the
  inverse arithmetic field Frobenius. The helper is from the existing Frobenius
  point-transport module, and its field automorphism agrees with FrobeniusDetailed.
- Flat-term K-flat representatives are exactly the full subcategory of
  `integralOperationsGoodComplex`: its definition is
  `IsKFlatIndependentCoefficients P ∧ ∀ i, IsFlatOnSite (P.X i)`.
  No boundedness, completeness, Tor-amplitude or constructibility predicate occurs.
- `P_n`, `r_n`, reduction transitions, `C(P)` and its actual coefficient-induced
  transitions are the existing unrestricted reduction and
  `integralOperationsPullbackTowerFunctor` constructions. `target` composes this
  tower with termwise exact sections, then `integralOperationsRoosFunctor` and
  `CompletedStalk.moduleQ`. Thus it is exactly `[H(B(P))]`, on objects and maps.
  The auxiliary D(P) tower is not redefined because this localization statement
  only uses B(P). All levels retain the single integral scalar action through
  `pointIntegralSections` and the actual constant-to-completion map.
- `source` is inclusion, `CompletedStalk.sectionsComplex`, then
  `CompletedStalk.moduleQ`, hence `[Gamma P]` and `[Gamma h]`.
- H and H(f) are the existing `integralOperationsRoosFunctor`. Its
  `integralOperationsRoos` is `mappingCocone (1-s)`, with exactly the prescribed
  signed differential; `integralOperationsRoosMap` is diagonal on the two products.
  `CompletedStalk.sectionsRoos` is the uniquely normalized comparison on both
  `roosFirst` and `roosSecond`, and is used in `representativeComparison`.
- `goodHomotopy` is the full subcategory predicate on
  `HomotopyCategory (integralTowerModules ...) (.up ℤ)`, evaluated on its canonical
  underlying complex `.as`. `toHomotopy` is the restricted homotopy quotient.
  The first two conjunctions assert the exact functor factorizations through it.
  The next two say its pulled-back homotopy quasi-isomorphisms are inverted.
  `hInv` explicitly asserts inversion of every good chain quasi-isomorphism for
  both S and T, so all subsequent inverse-denominator formulas are typed.
- The ambient S-bar is `pointFibreIntegralAmbient`, the exact integral-section
  derived functor. T-bar is `integralDerivedPullback ... ⋙ pointFibreIntegralAmbient`.
  The target derived category uses `HasDerivedCategory.ofIsGrothendieckAbelian`,
  exactly the small-Hom localization of `CompletedStalk.moduleQ` and the point
  fibre; the sheaf derived category uses the existing standard localization.
  These are universe presentations, not new mathematical assumptions.
- A family natural for all chain maps is exactly
  `η : source D l E ⟶ target D l E` on the full good-complex subcategory.
  The first clause following `hInv` says `∀ η, ∃! ηbar`, without invertibility
  of η or of any of its components.
- For every N, every good P, and every quasi-isomorphism q:P→N,
  `ηbar.app (Q.obj N) ≫ (representativeComparison ... N P q).hom`
  equals `sectionsFactors.hom.app N ≫ inv (moduleQ.map (sectionsComplex.map q))
  ≫ η.app P`. Lean composes left to right, so this is precisely
  `b_q ηbar_[N] = η_P [Gamma(q)]⁻¹`, with the explicit existing exact-sections
  localization comparison inserted to identify the two presentations of Gamma N.
  `representativeComparison` applies completed pullback to `[q]` inverse, then
  the specified integral pullback comparison, exact-sections comparison and c_C.
  Its parameter g is specialized to the prescribed Frobenius in the theorem.
- The next clause gives the requested roof square for every good roof and every η:
  `η_P ≫ inv(T(a)) ≫ T(b) = inv(S(a)) ≫ S(b) ≫ η_P'`.
  The following clause asserts that equal ambient derived roofs have equal S
  fractions and equal T fractions, expressing presentation independence for both
  sides. The final clause supplies a good roof for every derived morphism between
  good representatives. These spell out the node's last two sentences, not a
  restriction to morphisms with selected chain lifts.
- Representative independence is contained in the unique ambient natural
  transformation and its formula for *all* q: transporting either right hand side
  back by its b_q gives the same ηbar component. No arbitrary choice of a cone map,
  a completion functor, or a natural isomorphism is introduced.

Dependency declarations read and used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, its coefficient field/ring
  interfaces and public finite-field/coefficient constructions. The present node
  uses its coefficient convention, not its auxiliary geometric scheme X₀.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`, `galoisMap`, and their explicit field action;
  `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso` is Spec gamma.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `Scheme.ProEt`, `Scheme.ProEt.topology`, `ProEt.mk`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its imported completion:
  `integralConstantToCompletionOfUniverses`,
  `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`, `integralCoefficientSheaf`,
  `integralCoefficientSheafTransition`, `integralTowerModules`.
- `Sheaf.Paper.PointProEtaleSectionsExact`:
  `AlgebraicGeometry.ProEtale.pointModuleSections`, `point_proEtale_sections_exact`;
  `Sheaf.Paper.CompletedIntegralCoefficientGerm`: `pointIntegralSections` with its
  canonical integral coefficient action; `FiniteCoefficientPoint`:
  `pointFibreIntegralAmbient` and exactness instances.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`. The recorded good predicate uses these, verbatim.
- `Sheaf.Paper.AdicCoefficientDatum`:
  `Scheme.completedReductionTower`, its strict reductions and coefficient projections;
  the actual coefficient-field specialization is the published unrestricted reduction
  tower reexported by `IntegralOperationsWellDefined`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived` and its public
  finite module pullback/comparison infrastructure. The target tower uses that
  infrastructure's actual `integralOperationsPullbackTransition`.
- `Sheaf.Paper.IntegralOperationsWellDefined`:
  `integralOperationsGoodComplex`, `integralOperationsPullbackTowerFunctor`,
  `integralOperationsRoosFunctor`, `integralOperationsRoos`,
  `integralOperationsTowerStep`, `integralOperationsPullbackOnGood`,
  `integralOperationsWellDefined`.
- `Sheaf.Paper.CompletedStalkReparametrizationCoherence`:
  `CompletedStalk.sectionsComplex`, `moduleQ`, `roosFirst`, `roosSecond`,
  `sectionsRoos_existsUnique`, `sectionsRoos` (the recorded comparison dependency).
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and its
  `SiteDerivedTensorDescentSpec`, in particular the first localization equivalence.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` reexports the ambient
  `integralDerivedPullback` and `integralDerivedPullbackComparison` from
  `Sheaf.Paper.IntegralDerivedOperations`; these are the recorded operations, and
  the slice module's auxiliary completed tensor is not substituted for pullback.
- Proof-only imports include `CategoryTheory.roosF_homotopy_functor`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`,
  `Localization.liftNatTrans`, `Localization.natTrans_ext`,
  `Localization.exists_rightFraction`, and the two homotopy quasi-isomorphism
  calculus-of-fractions instances of `DerivedCategory.Fractions`.
  The proof node `lem-trf-point-quotient-tower-homotopy` has no recorded module
  or Mathlib match yet; its planned use is retained in the proof docstring.

Edge cases checked before writing: zero and contractible representatives, η=0,
q=id, arbitrary N that is not good, identity roofs, and equal roofs with different
middle resolutions. All are allowed. Inverting q is justified by its quasi-isomorphism
and exact point sections, not by goodness of N. Both shifted and unshifted Roos
coordinates use the existing normalization. Negative degrees and unbounded complexes
are included. Coefficient and point data are placed in one common universe u, as in
the existing finite-field coefficient convention; no equality of site object and
morphism universes is imposed. All variable and universe binders are explicit and
`autoImplicit` is disabled. No statement dispute was found.

Searches for reuse, performed using the prescribed msearch wrapper:

- LeanFinder: “Natural maps from point sections to completed pullback Roos cones on
  flat term K flat complexes descend uniquely to the derived category”: eight hits,
  including `DerivedCategory.right_fac`, `left_fac`, cone lift formulas and unrelated
  flat-functor limit lemmas. No exact match.
- LeanSearch: “Natural transformations from sections of K flat representatives to
  completed pullback Roos cones extend uniquely to unbounded derived categories”:
  eight hits including `Functor.rightDerivedUnique`, `Quotient.natTrans_ext`,
  `NatTrans.rightDerived` and global-section restriction transformations. No exact match.
- Loogle: `CategoryTheory.Localization.liftNatTrans`: ten hits, including the generic
  lifting, its app formula, composition, identity and shifted versions. These implement
  the existing proof leaf; they do not identify these particular S,T and b_q.
- Mathlib grep: `liftNatTrans|natTrans_ext` in `CategoryTheory/Localization`: 25 hits,
  including Predicate.lean and generic adjunction/bifunctor uses. Read the full
  `liftNatTrans`, `liftNatTrans_app`, `natTrans_ext` signatures and docstrings.
- Project `rg`/`grep`: searched the item id, `pointPullbackConeLocalization`,
  point-section/pullback/cone localization and roof/descent patterns under
  `lean/WeilConjectures` and `lean/Sheaf`. No existing declaration states the whole
  node. The parent `PointTransportConeComparisonDescent` handles the special
  augmentation family coming from tower maps, not every chain-natural family, so
  it is not an exact reuse candidate. Its existing representative comparison uses
  the same four specified comparison factors used here.

Validation: compiled on the server with scompile.py. The initial diagnostic exposed
an implicit standard-localization Hom-universe mismatch; making the point target's
already prescribed Grothendieck small-Hom localization explicit fixes it without
restricting any coefficient or site universe. A source namespace/argument correction
for `DerivedCategory.isIso_Q_map_iff_quasiIso` was also made. The last preliminary
compile passed with one long-line warning, repaired before final preflight.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
