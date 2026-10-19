## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralModelsStacks` states
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.integral_models_stacks`.
Its only postponed proof is this theorem. The other declarations construct the
coefficient maps, the sectionwise small-site transport, the restriction functor,
and the Stacks object predicate introduced in the node. They introduce no assumed
comparison map, arbitrary functor, completed-object hypothesis, or data chosen from
a mere existence assertion. The node's mathematical statement is unchanged.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is
  `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Its integer ring, chosen uniformizer and first
  quotient are the existing `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionIdeal ... 1`, and `Padic.coefficientExtensionRing ... 1`.
  The spectral norm is the canonical extended absolute value used by these objects.
- `(X : Scheme.{u}) [IsNoetherian X]` is the Noetherian-scheme hypothesis. There is
  no finite-field base datum, characteristic restriction, dimension bound,
  invertibility of l, or separatedness hypothesis. Taking a common universe for E
  and X loses no objects: both can be placed in their common larger universe.
- `integersObj l E` abbreviates the already recorded `(sfbCondensedIntegers l E).X`.
  `condensedRingObj (integersObj l E) X` is its pulled-back completed coefficient
  ring. The integral-limit dependency identifies it with the finite-quotient limit.
- `discreteSheaf` and `discreteObj` are abbreviations for ordinary constant
  CommRingCat sheafification followed by forgetting to RingCat and Ab, on the
  pro-etale point. Their pullbacks to X are the constant coefficient ring.
  `constantToContinuous` is the sheafification adjunct of the ring homomorphisms
  sending a scalar to its constant continuous function; `scalarPointMap` forgets
  to the abelian ring object, and `scalarMap` applies the actual site inverse image.
  Thus the coefficient map is the one in the node, with no map supplied as a binder.
- `restriction` is `(Mod.comap (scalarMap ...)).mapDerivedCategory`: ordinary exact
  scalar restriction applied termwise and descended to the unbounded derived
  category. `Mod.comap` leaves underlying abelian sheaves and maps unchanged.
  This is the internal-module presentation of the recorded
  `SheafOfModules.restrictScalars`, rather than a private restriction construction.
- `residueMap` applies the constant sheaf functor and site inverse image to the
  actual `Ideal.Quotient.mk` for the first coefficient ideal. The residue object
  in `stacksConstructible` is
  `(Mod.extendScalars (residueMap ...)).leftDerivedFunctor.obj L`.
  This is relative derived reduction over the constant integer ring. It is not
  ordinary quotient cohomology, an underived tensor, or tensor over the integers.
- The first conjunct in `stacksConstructible` is
  `ConstantCompletion.IsComplete (smallMap X (residueMap ...))
  (smallDerivedObject X _ L)`. `IsComplete` is the recorded
  `IsLocallyDerivedRingedIdealComplete`, for the kernel ideal of the first quotient.
  That ideal is precisely the uniformizer ideal. It tests local internal Hom from
  localization on every slice and imposes no boundedness condition.
- `sectionMap` uses the recorded section-ring reconstruction on the actual
  commutative monoid morphism. `smallRing` and `smallMap` precompose with
  `AsSmall.down`, with the induced topology. `smallModules` is the recorded
  section-module equivalence followed by this same sectionwise transport.
  `smallDerivedObject` applies this exact functor to a localization representative
  and then applies the standard Q. The object is determined up to the equality
  used downstream (derived isomorphism); it is not chosen from an unproved mere
  existence theorem. This transport retains the full original site's covers.
  Original site objects have universe u+1 and morphisms u; no equality of those
  universes has been imposed. The coefficient-sized small model is exactly the
  already published `coefficientProEtaleSiteModel.{u,u}`.
- The second conjunct quantifies every integer n and applies the existing
  `IsConstantModelConstructible` to H^n of the reduction. For this discrete finite
  residue field it is constructible cohomology. Such sheaves are classical by the
  stated etale/pro-etale comparison: the source's parenthetical etale origin is
  retained by this intrinsic constructibility condition, not replaced by arbitrary
  lisse sheaves or a definition using the theorem being stated.
- The third conjunct is the existing `DerivedCategory.finiteTorAmplitude` of the
  reduction: one finite interval for tensor tests against every degree-zero module
  sheaf. On Noetherian X the recorded local/global Tor theorem identifies this with
  Stacks 09C1's locally finite Tor dimension. The helper is used here only in the
  Noetherian context. Finite Tor amplitude itself forces boundedness, including
  after widening bounds to an ordered interval; no extra boundedness assumption
  on L has been inserted.
- `∀ K, constantModelBoundedConstructible ... K ↔ stacksConstructible ... (Res K)`
  is the two-sided membership criterion for *arbitrary* completed-coefficient K.
  The boundedness and constructibility on its left are precisely the final
  paragraph of the recorded `sk-def-sfb-constructible`. The generic ring-object
  bounded predicate of `sk-def-sfb-bounded-constructible` is imported as recorded;
  it is not substituted for the source's constant-model constructibility.
- The second main conjunct supplies an equivalence between the two full
  subcategories. The natural isomorphism
  `e.functor ⋙ stacksConstructible.ι ≅ constantModelBoundedConstructible.ι ⋙ restriction`
  explicitly identifies its functor with the restriction of the specified Res.
  Thus the statement does not merely assert an unrelated equivalence of categories.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`:
  `sfbCondensedIntegers`, `sfb_integral_coefficient_limit`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; the same operation is used in its existing
  internal presentation `CategoryTheory.Mod.comap` (Mathlib Monoidal.Mod).
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`, re-exporting
  `AlgebraicGeometry.ProEtale.boundedConstructible`, `BoundedConstructible` and
  `mem_boundedConstructible_iff`; the Noetherian weak-Serre triangulation is not
  needed to form the full subcategory here.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`,
  `ConstantModelBoundedConstructible`.
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`:
  `IsLocallyDerivedRingedIdealComplete`, through
  `Sheaf.Paper.ConstantCompletionEquivalence`:
  `ConstantCompletion.IsComplete`, `Mod`, `Q`, `D`, `equivalence`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedHom`, and its exported relative derived tensor structure.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRingSheaf`, `commMonToRing`, `sectionModuleEquivalence`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`:
  `comparison_additive`, `internal_section_tensor_comparison`; this identifies the
  actual relative tensors, exactness, flatness and K-flatness across presentations.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `realization_forget_preservesSheafification_instance` supplies the existing
  canonical `constantCommuteCompose` coefficient comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`:
  `coefficientProEtaleSiteModel`, `coefficientProEtaleModelTopology`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.extendScalars`, its generic `leftDerivedFunctor`, exactness of `Mod.comap`.
- Proof imports: `RestrictionLocalCompleteness`, `ExtensionIntegersDvr`, and
  `ProEtaleTorLocalGlobal`. The four proof dependencies with no published Lean
  statement (constant-coefficient integral criterion, constructible comparison,
  finite-Tor comparison, and cohomological adic criterion) are retained as the
  natural-language proof plan, not replaced by invented assumptions.

Edge cases checked: the empty scheme and zero complex satisfy the predicates with
zero residue and an arbitrary widened ordered Tor interval; the full-subcategory
formulation retains their ordinary morphisms. Torsion integer modules are allowed:
the reduction is derived and may have both H^-1 and H^0. The quantified K can be
unbounded and incomplete; completeness is an output condition, not an assumption.
The extension E=Q_l is included. No invertibility of l on X or finite Krull
dimension of X is used. All residue tensor tests range over every module sheaf.

Searches for an existing declaration:

1. `msearch.py ... leanfinder` with
   "Restriction of scalars from completed l-adic coefficients identifies bounded
   constructible complexes with adically complete constant coefficient complexes":
   eight results about BDeRhamPlus and ordinary AdicCompletion constructions; no match.
2. `msearch.py ... loogle '"Constructible", "Derived"'`: zero hits.
3. `msearch.py ... grep 'adic.*constructible|constructible.*adic'`: zero Mathlib hits.
4. `msearch.py ... leansearch` with "Restriction of scalars from completed l-adic
   coefficients to the constant sheaf induces an equivalence on bounded constructible
   derived categories": eight ordinary restriction-of-scalars results, including
   `SheafOfModules.restrictScalars`; none is the category comparison.
5. `rg` in upstream WeilConjectures and the project's lean/Sheaf for adic/constructible,
   integral restriction and completed coefficient comparison; upstream exact-node-id
   search has no hit. Existing complete integral categories impose completeness and
   reductions by definition (`sfIntegralConstructible`), so they are not the required
   bounded-cohomology predicate for arbitrary K. Reused the existing constant-model
   definition, actual continuous-function coefficients and internal/section equivalence.
6. Read the blueprint's exact detailed lemma and the local Stacks 09C1 and 09C2 text.
   The global Tor convention is justified by the already recorded local/global lemma.

No statement correction, new independent definition node, or dependency replacement
is required. Helpers implement notions introduced in this very detailed statement.
The added statement dependencies are existing published nodes for the presentations
and derived scalar operations used in the signature; their records are unchanged.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
