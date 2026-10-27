## Worker report

Stage 2: the delivery states `WeilConjectures.bounded_projective_tensor_complete` in
`Sheaf.Paper.BoundedProjectiveTensorComplete`. Its one theorem has proof `sorry`.
There are no new definitions, dependency repairs, statement corrections, or additional axioms.
The natural-language statement and accepted eight-step split are retained verbatim.

### Hypotheses and objects

- Prime: `(l : ℕ) [Fact l.Prime]`.
- Finite extension: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The coefficient dependency supplies the valuation ring,
  its chosen uniformizer and its positive-power quotient rings. No separate ring or
  arbitrary tower is substituted.
- Scheme: `(T : AlgebraicGeometry.Scheme.{t}) [CompactSpace T]
  [QuasiSeparatedSpace T]` means precisely qcqs. Invertibility is
  `∀ x : T, IsUnit (l : T.residueField x)`, equivalent to invertibility on T.
  No nonemptiness, finite type, Noetherian, or finite-field structure on T is assumed.
- The actual small pro-etale site is `IntegralOnSlice.Site T none`, with topology
  `IntegralOnSlice.topology T none`; its object universe is t+1 and its Hom universe is t.
- `IntegralOnSlice.ring l E T none` is the commutative version of the existing inverse
  limit `completedIntegralCoefficientSheafUnrestricted l E T`. Its RingCat version is
  `rings l E T none`; the underlying completed sheaf is unchanged.
- `Mod l E T none`, `Cx l E T none`, and `D l E T none` are the recorded module sheaves,
  their integer cochain complexes and their unbounded derived category. The module
  universe is max u (t+1); the canonical standard localization is the dependency's.
  The universes t and u remain independent.
- C_T is exactly `IntegralOnSlice.completion l E T none`, not an assumed endofunctor.
  Reading its definition shows it is the descent of `roosGood` on K-flat flat-term
  representatives, with the specified `completionComparison`. Its `tower` uses
  termwise actual quotient extension followed by `SheafOfModules.restrictScalars`.
  Its `transition_existsUnique` fixes each reduction by s tensor x -> rho(s) tensor x.
  Lean level n corresponds to the paper's exponent n+1.
- eta is exactly `IntegralOnSlice.completionUnit l E T none`. The dependency's
  `completionUnit_existsUnique` fixes it on all good representatives by
  `eta.app (Q P) >> completionComparison.hom.app P = Q.map (roosUnit P)`.
  `roosUnit` is the actual mapping-cocone lift of the product of quotient units and
  the ZERO shifted-product cochain. Naturality is part of its NatTrans type.

### Clauses of the conclusion

1. Additivity is `(completion l E T none).Additive`.
2. Exactness is the existence of its coherent `CommShift ℤ` structure with
   `.IsTriangulated`. `NatTrans.CommShift (completionUnit ...) ℤ` records compatibility
   of the specified unit with these shifts, as checked in proof step 5. The unit's
   naturality is already built into the existing definition.
3. The coefficient unit in degree zero is
   `(DerivedCategory.singleFunctor (Mod ...) 0).obj (SheafOfModules.unit (rings ...))`.
   The displayed `IsIso` applies to eta at precisely this object.
4. An arbitrary bounded P is `P : Cx ...` with
   `∃ a b : ℤ, ∀ k, k < a ∨ b < k -> IsZero (P.X k)`.
   Each term's finite-free summand condition is explicit:
   `∃ r : ℕ, ∃ i : P.X k -> product (Fin r) B,
   ∃ p : product (Fin r) B -> P.X k, i >> p = identity`.
   The products are finite sums in this abelian category. Both maps are sheaf-linear
   maps in `Mod`, not maps of constant coefficient modules. No condition on the
   differentials beyond the cochain-complex axioms is imposed.
5. The conclusion for P includes `∀ k, SheafOfModules.IsFlatOnSite (P.X k)`,
   `CochainComplex.IsKFlatIndependentCoefficients P`, and `IsIso (eta.app (Q.obj P))`.
   Thus the universally quantified P clause also supplies these results for Q.
6. Q has exactly the same boundedness and sheaf-retract hypotheses, with independently
   quantified bounds and ranks.
7. V is bound with the equality
   `V = (coefficientTotalTensor (topology T none) (ring ...)).obj (P,Q)`.
   This merely gives a name to the existing direct-sum total tensor; every pair P,Q
   has this V, so the equality excludes no case. The imported definition is the
   uncurry of `map₂HomologicalComplex` for the sheaf tensor, hence uses coproducts
   and the cochain Koszul differential, not products along an infinite diagonal.
8. The conclusion repeats boundedness and explicit finite-free splittings for V,
   termwise flatness for V, and K-flatness for Q and V (P is already asserted above).
9. `Nonempty (DerivedCategory.Q.obj V ≅ (siteDerivedTensorIndependentCoefficients
   (topology T none) (ring ...)).obj (Q.obj P,Q.obj Q))` states the ordinary DERIVED
   tensor representative isomorphism. It uses the tensor supplied by the recorded
   site-derived-tensor descent, rather than completed tensor or a cohomology-only
   identification.
10. The final `IsIso` is eta at `DerivedCategory.Q.obj V` itself. Completeness for Q
    follows as for every P from the universally quantified preceding clause.

The theorem docstring contains all eight proof steps, with their dependency IDs:
finite-sheaf retract flatness and tensor splittings; bounded-flat K-flatness; exact
Roos calculus before deriving; descent from good representatives with actual quotient
maps; unit/triangle compatibility; the completed free-cell limit; the retract inverse;
and descending brutal truncation. No constant projective R-module complex is chosen.

### Recorded dependency declarations read and used

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the public coefficient-extension
  constructions `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing` and `coefficientExtensionTransition`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, with its scheme `QuasiSeparatedSpace` convention.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and its topology.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`, and its public completed
  coefficient sheaf and quotient system constructions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  literally Mathlib `SheafOfModules` with its existing abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, its `Q` and
  its standard size convention.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`; this
  provides the total-derived interpretation with the natural Roos triangle.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `WeilConjectures.IntegralOnSlice.completedTensor`, and especially its owning-node
  declarations `ring`, `rings`, `Mod`, `Cx`, `D`, `tower`, `completion`,
  `completionComparison`, `roosUnit` and `completionUnit`. Their full normalization
  signatures and docstrings were read; this theorem uses the completion and its unit,
  not the completed tensor as a substitute for the ordinary tensor.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the total
  tensor underlying the cited alias.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and its
  normalized chosen `siteDerivedTensorIndependentCoefficients`.
- Already landed `def-coef-ringed-tensor-hom-model` is added to stmt_deps solely to
  cite `WeilConjectures.coefficientTotalTensor` in
  `Sheaf.Paper.CoefficientRingedTensorHomModel`. Its definition was read in full:
  it is the existing cochain total tensor, not a new notion. No node is created.

All recorded proof-dependency modules are imported as plain imports, unless already
public statement dependencies. The Mathlib-only proof leaves use their recorded
localization, calculus-of-fractions, triangulated, and short-exact-sequence modules.

### Edge cases and source reading

Before writing I checked the empty scheme, zero ranks, zero complexes, single-degree
finite-free modules, sheaf retracts which are not constant, and the two-term complex
[B --varpi--> B]. Empty T makes invertibility on points vacuous legitimately, not the
completion assertion: its module category is zero. Rank zero is allowed by `Fin 0`;
no positive-rank or nonzero-complex hypothesis appears. The bounds need not be ordered;
if a>b the condition forces every term to be zero, as it should. The tensor is bounded
because two finite support intervals add, and all off-diagonal summands vanish. The
arbitrary differential case is handled by brutal truncation, not by extension of a
sheaf differential to a constant free complex. No case requires t=u.

Read Bhatt--Scholze Lemma 6.5.5 and its finite-projective devissage (PDF pp.49--50),
plus Stacks `proetale.tex`, label lemma-naive-completion (099M), and
`sites-cohomology.tex`, label lemma-derived-limit-is-ok (0941). The node is the
already reviewed explicit sheaf-retract refinement of that devissage. No counterexample
or statement fault was found.

### Searches and validation

The following searches were actually run using msearch.py for this group/item:

- leanfinder: "The quotient tower derived completion functor on proetale completed
  coefficient sheaves is additive exact and fixes bounded complexes of finite free
  sheaf summands". Eight hits, including Condensed.profiniteSolid,
  Condensed.profiniteFree and BDeRhamPlus; none states this theorem.
- loogle: `"completion", "IsIso"`. Zero hits.
- grep of Mathlib: `derived.?complet|bounded.*projective.*tensor`. Zero hits.
- leansearch: "Derived completion by a quotient tower fixes bounded complexes of
  summands of finite free completed coefficient sheaves". Eight hits, including
  DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, HasDerivedCategory.standard and
  AdicCompletion. None identifies the normalized quotient-Roos unit for these sheaves.

Direct rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for bounded
projective tensors, completion functors and units, finite retracts and the proposed
name were also made; the upstream directory was searched for this exact node ID.
The ordinary ModuleCat perfect-tensor Roos theorem has constant projective models;
the upstream completed-exchange completion has a different coefficient encoding.
Neither states the item. Existing IntegralOnSlice constructions are reused instead.
The proposed declaration name has no existing match. No search service failed.

Compiler repair: specify all universes on the flatness/K-flatness/tensor APIs and
remove universe-ambiguous generic sheafification instance search, following the
existing IntegralOnSlice module. This only selects the canonical existing instances;
it adds no mathematical hypothesis or definition. The first complete compile passed
with one line-length warning, which was then fixed. Final compile and delivery dry-run
results are recorded below when complete.

Final scompile.py: both sandbox and named module passed without errors or warnings.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
