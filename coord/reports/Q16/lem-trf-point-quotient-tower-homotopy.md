## Worker report

Module: `Sheaf.Paper.PointQuotientTowerHomotopy`. All six statement declarations have
`sorry` proofs. Every definition has actual data, obtained by composing published
functors; no representative, arbitrary arrow, coefficient isomorphism, or derived
isomorphism is chosen from a bare existence assertion. The four exactness instances
and the localization instance expose existing structures by typeclass inference.
The node changes only in `lean`.

The previous worker's live-wins refusal concerned re-splitting the already merged
stage-1 node. This stage-2 packet states that reviewed node without re-splitting it.
The initial stage-2 dry run found no node file in the retained sandbox, which contained
only dispatcher marker files. This packet supplies the missing Lean, node, and report.

### Hypotheses and constructions

- The finite-field datum p,a,q,k0,k is `D : FiniteFieldDatum.{u}`. Its `k` is the fixed
  algebraic closure and `Spec (.of D.k)` is s. The coefficient prime is `l : ℕ` with
  `[Fact l.Prime]`; each theorem retains `_hl : l ≠ D.p`. The finite extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. These are
  the coefficient data used by the recorded trace-formula conventions; no choice of
  X0, finite constructibility, or boundedness is added to this point statement.
- The actual valuation ring, chosen uniformizer, and positive quotient rings are
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`, and
  `Padic.coefficientExtensionRing l E (n + 1)`. Index `n : ℕ` means the positive
  exponent n+1, including the first quotient. No exponent-zero quotient is used.
- The arbitrary automorphism is `(g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]`.
  It is not specialized to Frobenius. The small pro-etale site is `Scheme.ProEt`,
  with topology `ProEt.topology`, object universe u+1 and morphism universe u.
  Modules and their scalars live in u+1; `ULift.{u+1}` is the existing size convention,
  not an extra relation between site object and morphism universes.
- S_n is `integralCoefficientCommRingSheaf l E s n`; R is
  `completedIntegralCommRingSheafUnrestricted l E s`; its projection is
  `completedIntegralCommRingProjectionUnrestricted`. These are the actual constant
  finite sheaves and their completed limit, not a discrete constant integral ring.
  Quotient steps are the published `unrestrictedIntegralTransition`.
- P is `(integralOperationsGoodComplex l E s).FullSubcategory`. Reading its definition
  gives exactly `CochainComplex.IsKFlatIndependentCoefficients` and
  `∀ i, SheafOfModules.IsFlatOnSite (P.X i)`, with all chain maps and no boundedness
  condition. No new K-flat or flatness predicate is defined here.
- `sourceSheafTower` is the existing P_n and t_n diagram from
  `unrestrictedIntegralComplexFunctor` / `unrestrictedIntegralTransition`, transposed
  with `HomologicalComplex.functorEquivalence.inverse`. Thus every differential and
  transition remains in one strict diagram, computed on the single P.
- `targetSheafTower g` is `integralOperationsPullbackTowerFunctor l E g`, transposed
  by that same equivalence. Its levels are the published `integralOperationsPullbackLevel`
  = finite reduction, `integralOperationsLevelPullback`, and scalar restriction.
  The transition's published uniqueness formula is precisely the balanced map induced
  by G(t_n) and rho_n. The constant-section structure maps are
  `inverseImageFiniteCoefficientMap`; the inverse-image/pullback comparison dependency
  identifies these with the sectionwise G and tensor along c_n used in the node.
- Gamma is the existing `pointIntegralSections l E D.k`. It evaluates at the final
  small-site object and restricts scalars along the actual constant-to-completion
  section map. `sectionsTowers` applies it to the whole inverse system.
  The scalar category is `ModuleCat (ULift (Padic.coefficientExtensionIntegers l E))`,
  and strict towers are `ℕᵒᵖ ⥤` that category, the recorded reindexing of positive towers.
- `source` and `target g` compose the corresponding strict sheaf tower with termwise
  `sectionsTowers`. This defines exactly D and B, including D(f)_n and B(f)_n on maps.
  Their harmless extensions to all complexes are restricted to P in the statements.
  `sourceLevel` and `targetLevel` are their actual module-level component functors,
  retained to state the required formulas for arbitrary degree -1 homotopy components.

### Every conclusion

- `homotopical` asserts the abelian structure on A; each evaluation preserves finite
  limits and colimits, hence computes kernels and cokernels levelwise. Its natural
  homology-functor isomorphism states cohomology is levelwise in every integer degree.
  The next conjunct is `QuasiIso f ↔ ∀ n, QuasiIso (f at n)` for all tower-complex maps.
- The last three conjuncts of `homotopical` say the restrictions of D and B to the
  full category P are additive and both carry quasi-isomorphisms between its objects
  to quasi-isomorphisms. Neither the definition nor a statement assumes S_n flat over R.
- `homotopies` takes arbitrary P,P', maps f,f', and `h : Homotopy f f'`. It supplies
  homotopies H for D and B and requires, for every i,j,n,
  `(H.hom i j).app (op n) = sourceLevel.map (h.hom i j)` or its target counterpart.
  These are exactly Gamma(h tensor 1) and Gamma(g_n^*(h tensor 1)). Each `H.hom i j`
  is a natural transformation of towers, so compatibility with every transition is
  required by its type. Mathlib's `Homotopy f f'` means f=dh+hd+f'; in the node's
  language it is the specified homotopy from f' to f, with no reversed sign.
- `goodHomotopyRelation` relates precisely the maps of the full representative
  category whose underlying chain maps have a homotopy. `homotopyDescent` asserts
  the two functors from its quotient and natural factorization isomorphisms of QD
  and QB. This is the homotopy category of P, not the whole derived category or a
  category with only isomorphisms as arrows.
- `quotientAugmentation` supplies one strict natural transformation from the constant
  section complex to D(P). Each level is the image of `unrestrictedTowerUnit` under
  termwise Gamma; that published unit is characterized by x to 1 tensor x.
  `HEq` compares the two published presentations of this chain map without forcing
  Lean to expand their entire coefficient structures during type unification. It
  asserts equality of the specified maps, not only equality after localization or on
  cohomology. The natural-transformation type retains all augmentation squares.
- `coherentSource` quantifies over the uniquely normalized quotient equivalences q
  and completed comparison e of `IntegralCoefficientPresentation.comparison`.
  The two antecedents are exactly their quotient-representative formula and projection
  formula, not extra mathematical assumptions: existence and uniqueness of these
  maps are already asserted by that dependency. The level comparison is that
  dependency's `IntegralCoefficientPresentation.level` = e_n composed with kappa_n inverse.
- `presentedSheafTower e` restricts P along e.hom, applies
  `completedReductionComplexTowerFunctor s (pbcIntegralDatum l E)`, and restricts the
  entire resulting tower back along e.inv. `pbcIntegralDatum` is the published O_E,
  (uniformizer) specialization of the recorded `AdicCoefficientDatum`; it includes
  Noetherian, finite torsion residue, finite and perfect quotient hypotheses.
- `CoherentSourceComparison q e` asserts an isomorphism r between this complete
  transported complex of towers and `sourceSheafTower.obj P`. Its normalization sends
  every sheafified generator b tensor x to e_n(b) tensor x, at every level, degree,
  site object and section. The domain and codomain are whole strict diagrams, so r
  includes the differential and all transition squares. This is not a family of
  separately chosen isomorphisms after evaluation.
- `coherentSections e` is restriction of N along e.hom, the actual derived coherent
  functor `completedReductionTower`, restriction of its entire tower along e.inv,
  then the derived exact sections functor on towers. The second half of
  `CoherentSourceComparison` supplies gamma from this object to Q(D(P)), with its hom
  required to be the displayed composite: exact scalar-restriction factorization,
  the actual `completedReductionTowerComplexCounit`, the tower-restriction
  factorization, Q(r), and the exact tower-sections factorization. Consequently the
  canonical comparison itself, rather than just existence of an arbitrary iso, is
  required invertible. The pure-tensor normalization also retains the quotient units.
- `evaluation` states the finite-evaluation corollary: Q of D(P) at n is exact derived
  Gamma of the restricted `scalarReductionDerivedExtension` of [P]. Thus it is sections
  of N tensor^L S_n. The theorem accompanies, and does not replace, the coherent
  whole-diagram comparison.
- B(P)'s asserted representative is the actual `targetSheafTower` and its exact
  `sectionsTowers` image: finite pullback is applied to the very P_n used for D(P),
  with the existing coefficient-induced transitions. The construction never replaces
  this diagram by separate derived evaluations or by an independently chosen model.

### Dependency declarations read and used

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, its coefficient-field and ring
  conventions; the relevant data are the underlying `FiniteFieldDatum` and Padic API.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology` and
  `ProEt.mk`. The scheme-properties node is explicitly a convention with no declaration;
  here the only requested property is Mathlib `IsIso g`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, reexporting the recorded finite sheaves,
  completion and projections. `pointIntegralSections` uses their constant scalar map.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`. Both occur in the reused `integralOperationsGoodComplex`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` and its public underlying module:
  `inverseImageFiniteCoefficientMap`, `inverseImageFiniteComparisonComplex`,
  `integralOperationsLevelPullback`, and the recorded pullback tower/transition API.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`; the quotient/pullback APIs use the same
  sheafified tensor. `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` supplies every scalar restriction.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `pointModuleSections` and
  `point_proEtale_sections_exact`; the existing constant-integral scalar wrapper is
  `pointIntegralSections` from `Sheaf.Paper.CompletedIntegralCoefficientGerm`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`, with `NatTrans`
  as tower maps. `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, Q,
  Qh; `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategory`
  and `mapDerivedCategoryFactors`.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`,
  `completedReductionComplexTowerFunctor`, `reductionTensorSection`,
  `completedReductionProjection`, `completedReductionTowerComplexCounit`.
- `Sheaf.Paper.IntegralCoefficientPresentationComparison`:
  `IntegralCoefficientPresentation.comparison` and `.level`, with the published
  `pbcIntegralDatum`, `pbcAdicRings`, `pbcAdicCompletion`, `pbcRestrict`, `pbcDerivedRestrict`.
- Proof imports: `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`, and the exact-functor
  and functor-category Mathlib imports. The abelian tower dependency is the Mathlib
  `Abelian.functorCategoryAbelian`, not an unstated project theorem.
- Reordering reuses `HomologicalComplex.functorEquivalence` in
  `WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv`; it has
  actual degreewise inverse data and identity comparison isomorphisms. No second
  reordering, K-flatness, coefficient, or reduction-tower definition was introduced.

### Edge cases

Checked P=0 and zero maps/homotopies; g=identity (not excluded); n=0 means the first
positive quotient; unbounded complexes; nonflat quotients S_n; arbitrary component
maps h that are not chain maps; equal and nonconsecutive tower indices; and the empty
site object. Natural transformations impose all transition squares, including identities.
The balanced generator formulas determine sheaf maps locally even where a site object
is empty; no global pure-tensor-generation assumption is imposed. There is no finite
constructibility or derived-completeness assumption on P. Canonical coefficient transport
is used because the Cont-presentation completion is not definitionally the detailed one.

### Searches

- `msearch.py ... leanfinder`: "Additive quotient tensor and exact sections functors on
  strict inverse towers of K-flat sheaf complexes preserve quasi-isomorphisms and homotopies".
  Eight generic homotopy/localization hits, especially
  `Functor.instLiftingHomotopyCategoryIntUpDerivedCategoryQhQuasiIsoCompMapHomotopyCategoryMapDerivedCategory`
  and exact-functor `mapHomologicalComplexUpToQuasiIso` factorizations. None gives this
  canonical coefficient-specific whole-diagram statement.
- `msearch.py ... loogle`: "Functor.mapHomotopyCategory, HomologicalComplex.quasiIso,
  CategoryTheory.Functor.ofOpSequence". No hits; service reported unknown unqualified
  `Functor.mapHomotopyCategory`. The fully qualified source declaration was read directly.
- `msearch.py ... grep`: "mapHomotopyCategory|complexOfFunctorsToFunctorToComplex|mapHomotopy"
  in `Algebra/Homology`. Twenty-five generic homotopy and localization hits; no exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id: no declaration.
  Searches for quotient tower/point transport/homotopicality found
  `PointTransportStrictQuotient`, `IntegralOperationsWellDefined`, and the generic
  functor equivalence. The first is the consumer's Frobenius-specific strict-transport
  theorem, not this arbitrary-automorphism homotopy/coherent-source statement; it was
  not imported, avoiding a downstream dependency. The latter two supply reusable
  constructions, which were used rather than duplicated.
- Further source searches for `pointIntegralSections`, `mapHomotopy`, scalar restriction,
  coherent reduction counits, and functor reordering located the exact published
  constructions listed above. The stage-1 node's recorded searches were read as well.

No new nodes, dependency replacements, statement correction, or STATEMENT-DISPUTED fault.
All helpers belong to the constructions and comparison explicitly named in this node
and are listed in `lean.declarations`.

### Validation

Compiled the delivered module through `scompile.py` in both sandbox and library module
modes against the live published server build: clean, no errors or warnings, about seven
seconds per mode under the unchanged 60-second limit. An earlier attempt at the strict
augmentation's equality triggered expensive type unification of two existing presentations;
using the explicit heterogeneous equality removed that elaboration expansion. No timeout
or heartbeat limit was increased. All six theorem proofs remain `sorry` as stage 2 requires.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
