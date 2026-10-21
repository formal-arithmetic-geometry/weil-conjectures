## Worker report

The module `Sheaf.Paper.ConstructibleRationalHomComparison` states
`AlgebraicGeometry.Scheme.constructibleRationalHomComparison`, with `sorry` as its
entire proof. It constructs the restricted coefficient-linear structure
`rationalRealizationLocalizedLinear` and defines the specialization
`ConstructibleRationalHomComparison` of the dependency's existing comparison predicate.
These are helpers of this node, not new mathematical notions. There are no new nodes,
dependency repairs, or changes to the item's informal statement or dependency lists.

Source read: Bhatt--Scholze, *The pro-etale topology for schemes*, the local PDF,
pp. 61--62, Lemma 6.8.12 and Proposition 6.8.14(2). Lemma 6.8.12 gives continuity
on uniformly bounded-below sums after shifting; the proposition uses it for full
faithfulness. The node restricts to finite coefficient extensions and the prescribed
noetherian, finite-dimensional base.

Hypothesis and object correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E of Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`.
- A=O_E and its chosen uniformizer: the existing `PbcIntegralRing l E` and
  `pbcUniformizer l E`. This is the standard ULift of the valuation ring into the
  small site's coefficient universe, not a different coefficient ring.
- Scheme and its three hypotheses: `(X : Scheme.{u}) [IsNoetherian X]`,
  `[Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]`, and
  `[Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]`. The latter is invertibility
  in every local ring, not a condition on an identity morphism.
- Small pro-etale site: the site used by the existing `pbcModules`,
  `pbcAdicCompletion`, and the recorded realization is `Scheme.ProEt.topology X`.
  Its object universe remains u+1 and morphism universe u.
- B_X: `pbcAdicCompletion X (pbcIntegralDatum l E)`, the published completed
  coefficient ring. `R.integralIso` is its quotient-normalized identification
  with continuous integral functions. `R.localizationIso` and its normalization
  identify its sheaf localization with `rationalCoefficientSheaf l X E`.
- Module sheaves and ordinary ambient derived categories: `pbcModules` is the
  existing sheaf-module category and `PbcCompletedDerived` its derived category.
  The rational target is literally
  `DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))`.
- C_X: `PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)`. This is the
  published full subcategory with derived completion, uniform constructible
  reductions, and compatible etale-origin witnesses. The comparison predicate
  uses its defining `PbcIsBoundedConstructibleComplete` predicate on ambient objects.
- Q and raw R_X: the source of `R.J` is the recorded `PbcRationalCategory` with
  its recorded `pbcRationalization`. This is raw localization, without a Karoubi
  envelope. No alternative category is constructed.
- Rational constructibility and the specified J,F: `(R : RationalModuleRealization
  l E X)` retains all the dependency's coefficient, locally closed restriction,
  constructibility, object, and fraction normalizations. In particular F is
  exactly `pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion)` and J is `R.J`.
  The theorem quantifies over every such normalized realization; existence is
  already the dependency theorem `rationalModuleRealizationFunctor`.

Conclusion correspondence, including every clause:

- Every K in C_X is quantified in the first conjunct, without a continuity
  hypothesis on K.
- Every small countable family: `(I : Type (u + 1)) [Countable I]` and
  `M : I → PbcCompletedDerived X (pbcIntegralDatum l E)`. There is no Nonempty
  assumption and no fixed indexing by the natural numbers.
- The common cohomological lower bound is exactly
  `(∃ n : ℤ, ∀ i : I, (M i).IsGE n)`. No upper bound on the family is imposed.
- Every integer degree is `∀ q : ℤ`.
- The ambient coproduct is an arbitrary `(s : Cofan M)` with `IsColimit s`.
  The direct sum of Hom modules is mapped by `DirectSum.toModule`; its ith
  component is `Linear.rightComp` with `(shiftFunctor _ q).map (s.inj i)`.
  `Function.Bijective` says precisely that this specified linear map is an
  isomorphism. No completion of the coproduct or alternate coproduct category
  is used.
- For every K,L in C_X and q, `ConstructibleRationalHomComparison` instantiates
  `scalarLocalizationHomComparison` with BOTH predicates equal to actual
  integral membership. It therefore supplies localized-ring linear equivalences
  `Hom(K,L[q])[1/varpi] ≃ Hom(FK,FL[q])` for exactly those objects.
- `rationalRealizationLocalizedLinear` uses `R.moduleLinear` and the existing
  derived E-linear instance, restricting scalars along the actual
  `pbcRationalCoefficientEquiv l E : Localization.Away (pbcUniformizer l E) ≃+* E`.
  Thus the target action is the normalized constant field action, not an arbitrary
  module structure. The predicate's source is the existing `LocalizedModule.Away`
  fraction quotient, with its canonical localized module structure.
- The predicate's first equation fixes EVERY fraction `f/varpi^n` to
  `invSelf(varpi)^n • (F.map f ≫ (F.commShiftIso q).hom.app L)`. Restriction
  along the coefficient equivalence is exactly `varpi^(-n) F(f)` over E.
- Its next equation is contravariant/covariant naturality in K,L on fractions.
- Its identity equation includes the canonical degree-zero shift isomorphism.
- Its composition equation includes the sum of the two shifts and the power
  `varpi^(n+m)`, so covers shifted composition as well as ordinary composition.
- Its last equation is compatibility with simultaneous shifts of source and
  target, explicitly using `shiftFunctorComm` and `F.commShiftIso`.
- The existential CommShift structure belongs to this fixed derived scalar-extension
  functor. No replacement functor or arbitrary isomorphism of Hom modules is used;
  all comparison isomorphisms have the required normalized formula.
- The last two conjuncts are literally `R.J.Full ∧ R.J.Faithful`, into the ambient
  D(E_X). The first conjunct verifies the coproduct-Hom input rather than assuming
  it; the proof docstring explains its passage through the abstract comparison.

Dependency declarations used (names are in `AlgebraicGeometry.Scheme` unless qualified):

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `FiniteLocallyClosedStratification`, through the recorded realization's
  rational constructibility clause.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, underlying the existing scalar tensors.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, through the realization's cohomology clause.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported coefficient constructions.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`, with the
  published completed coefficient and reduction constructions used in membership.
- `Sheaf.Paper.IntegralUniformCoefficient` and its published supporting module
  `Sheaf.Paper.BoundedConstructibleComplete`: `PbcIntegralRing`, `pbcIntegralDatum`,
  `pbcUniformizer`, `PbcBoundedConstructibleComplete`,
  `PbcIsBoundedConstructibleComplete`. We use the latter's original lifted
  finite-extension specialization, as the realization itself does.
- `Sheaf.Paper.ContinuousConstructibleModule`:
  `AlgebraicGeometry.ProEtale.IsContinuousConstructible`, retained through the
  existing coefficient and constructibility framework.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`,
  and the canonical completed coefficient-linear structures.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  using Mathlib's exact sheaf-module notion.
- `Sheaf.Paper.RationalModuleRealizationFunctor`: `RationalModuleRealization`,
  `rationalModuleRealizationFunctor`, all its normalized fields. The imported
  scalar-extension interface also gives `pbcRationalCoefficientEquiv`.
- `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness`:
  `integralConstructible_boundedBelow_compactness` (proof import).
- `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`:
  `CategoryTheory.scalarLocalizationHomComparison`,
  `CategoryTheory.scalarLocalization_derivedHom`,
  `CategoryTheory.scalarLocalizationHomEquiv`.
- `Sheaf.Paper.IntegralConstructibleHomSums`: `integralConstructible_hom_sums`
  (proof import).
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectCharacterization`, `integralStratifiedPerfectClosure`
  (proof import).

All statement-dependency records and the relevant declarations/docstrings were read.
The local example `CompactObject.lean` has been withdrawn and contains no declarations;
its node record was read. Some published module sources are unavailable through
`scompile.py --source`, including the realization and the compactness module. Their
interfaces are nevertheless present in the live published build: a direct import
probe compiled successfully and printed the expected full types of
`RationalModuleRealization` and `pbcRationalCoefficientEquiv`. The complete local
realization source and its normalized structure fields were read as well. No substitute
definition or dependency module was introduced for this source-lookup discrepancy.

Edge cases checked: empty countable family, finite families, K=0 or L=0,
negative degrees and negative lower bounds, empty X, torsion integral objects
whose rational images vanish, n=0 fractions (denominator one), degree-zero
identity shifts, and composition with arbitrary denominator powers. There is no
hypothesis that integral cohomology modules are flat or projective, no bound on
cohomology above for M, and no assertion about families unbounded below. The field
and scheme use the published universe convention; the site's unequal object and
morphism universes are retained.

Searches actually run through the required wrapper, logged in `searches.jsonl`:

- LeanFinder: "Constructible adic complexes commute with bounded below direct sums
  of shifted Hom and rational scalar extension is fully faithful". Eight hits,
  including derived-category linearity and singleFunctor full-faithfulness; no
  exact constructible completed-coefficient comparison.
- Loogle: `DerivedCategory, Localization`. Zero hits.
- Mathlib grep: `constructible.*[Hh]om|[Hh]om.*constructible|localiz.*[Hh]om`.
  Twenty-five hits, including ordinary algebraic module localization and generic
  homology-localization constructions, no exact statement.
- `rg` with constructible/Hom and rational/full-faithfulness patterns in both
  `lean/WeilConjectures` and `lean/Sheaf`. Found the generic scalar comparison,
  Hom-sums dependency and unrelated constructible Hom or rationalization lemmas;
  none combines this node's verified compactness and actual ambient comparison.
- `grep -rn lem-per-constructible-rational-hom-comparison lean/WeilConjectures`
  returned no matches. Name checks found no existing declarations under the
  three names introduced here.

No STATEMENT-DISPUTED issue was found. The only initial compiler warning concerned
class-definition reducibility of the explicit scalar structure; this was repaired
with `@[instance_reducible]`, without changing its data.

## Second reading by Q22

This is the dispatcher's required author self-check; independent review belongs to
the maintainer. I reopened the node and delivered module and checked the two theorem
conjuncts separately. The first quantifies actual integral objects and all countable
families with a common lower bound, and its map uses exactly the shifted coprojections.
The second expands the imported five-clause comparison predicate, retaining the
fraction formula and every compatibility law, then separately asserts Full and
Faithful for the same J specified in the dependency. The target coefficient action
is pinned to the realization's normalized field action by the explicit restriction
of scalars. I checked the completed/full-subcategory definitions, including the
etale-origin predicate, rather than replacing membership by mere boundedness.
No informal statement correction or omitted clause was found. Helpers have real
data; the only postponed theorem is the item itself with its four-step proof docstring.
