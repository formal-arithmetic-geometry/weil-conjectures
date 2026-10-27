## Worker report

The module `Sheaf.AlgebraicGeometry.AffineRelativeStalkResolutionIso` states
`AlgebraicGeometry.exists_affineRelativeStalkResolutionIso`. It has one postponed proof,
the whole proof of that theorem, and twelve concrete helper definitions/abbreviations.
Every helper specializes existing constructions for the objects of this node; no new
independent mathematical notion or dependency module is introduced. The source is Stacks
Project, `perfect.tex`, Tag 0DHY, `lemma-tor-dimension-rel-affine`, whose opening proof
identifies `(f⁻¹ O_S)_x = R_p` and `E_x = M_q`. The tensor and skyscraper expansions follow
the six reviewed proof steps of this DAG node. All six steps are included in the theorem
docstring with their dependency names and scalar normalizations.

The statement is unchanged. The sole statement-dependency addition is the already landed
`lem-weil-pbc-site-derived-tensor-descent`. It supplies the actual derived tensor object
`siteDerivedTensorIndependentCoefficients`: the existing vanishing predicate in
`def-trf-ringed-complex-derived-tensor-vanishing` alone does not name that object.
No statement correction, disputed assertion, new node, or dependency repair is needed.

Hypothesis and clause correspondence (helper names below are in
`AlgebraicGeometry.AffineRelativeStalk`):

- Arbitrary commutative rings and ring homomorphism: `{R A : Type u} [CommRing R]
  [CommRing A] (φ : R →+* A)`. The scheme morphism is literally
  `Spec.map (CommRingCat.ofHom φ)` throughout the helper definitions, from `Spec A`
  to `Spec R`. There is no flatness, finite type, Noetherian or nontriviality assumption.
- Arbitrary unbounded complex: `M : CochainComplex (ModuleCat.{u} A) ℤ`. No support,
  boundedness, termwise flatness or K-flatness hypothesis is placed on M.
- Termwise associated sheaf: `restrictedTilde` applies the existing `tilde.functor`
  by `Functor.mapHomologicalComplex`, with its published `tilde.map_zero` witness.
  Its differentials are the tilde maps of the differentials of M.
- The inverse-image ring B and its actual structure map α: `ringedSpace φ` has the
  same carrier as `Spec A` and the sheaf `TopCat.Sheaf.inverseImageRing` of `O_Spec R`.
  `restrictedTilde` then applies `SheafOfModules.restrictScalars` along
  `Scheme.Modules.tensorPullbackRingMap`, after the standard CommRingCat-to-RingCat
  coefficient conversion. It never extends scalars to O_Spec A in place of B.
- A point q and its inverse-image prime p: `x : PrimeSpectrum A` and
  `(PrimeSpectrum.comap φ x).asIdeal`. This is the prime at the point f(x).
- The affine germ isomorphism j is `(Spec.stalkIso (.of R) (PrimeSpectrum.comap φ x)).symm`.
  The inverse-image stalk map k in `inverseImageStalkMap` is precisely
  `stalkPullbackHom` followed by the stalk of `toSheafify`, as fixed by the reviewed
  proof. Both are the known stalk isomorphisms of Tags 008H/007Z.
  `scalarMap` is the underlying ring homomorphism of their composite `k j`.
  No arbitrary witness from `exists_inverseImageStructure_stalk_iso` is chosen:
  its compatibility equation alone would not determine k.
- S_x on modules is `stalkFunctor`, the recorded module stalk functor followed by
  `ModuleCat.restrictScalars (scalarMap φ x)`. `complexStalkFunctor` applies these two
  functors termwise. The existing named zero-preservation instance is passed explicitly
  to the stalk's `mapHomologicalComplex`, without introducing a local instance.
- The object `M_q` in D(R_p) is `localizedComplex φ x M`: the Mathlib
  `ModuleCat.localizedModuleFunctor x.asIdeal.primeCompl` termwise, followed by scalar
  restriction along `Localization.localRingHom p q φ rfl`. The localized module uses
  Mathlib's canonically equivalent `Shrink (LocalizedModule …)` small model; the
  differential and fraction maps are the existing localization maps, not an arbitrary
  replacement complex.
- The first asserted isomorphism is the existential `θ`, from
  `DerivedCategory.Q.obj ((complexStalkFunctor φ x).obj (restrictedTilde φ M))` to
  `DerivedCategory.Q.obj (localizedComplex φ x M)`. This is an isomorphism in the
  unbounded derived category itself, with no replacement by per-degree cohomology.
- Every K-flat resolution: the universal binders `P` and `u : P ⟶ restrictedTilde φ M`
  and `CochainComplex.IsKFlatResolutionIndependentCoefficients u` mean exactly a
  quasi-isomorphism with K-flat source over B. The asserted
  `IsIso (DerivedCategory.Q.map ((complexStalkFunctor φ x).map u) ≫ θ.hom)` is exactly
  the stated composite θ_x after Q(S_x u). No flatness of R_p → A_q is assumed.
- S_x on derived categories: the existential functor `S` and the natural isomorphism
  `DerivedCategory.Q ⋙ S ≅ complexStalkFunctor φ x ⋙ DerivedCategory.Q` specify the
  functor induced by exact stalk and scalar transport. This localization
  characterization determines it up to natural isomorphism and imposes no additional
  mathematical hypothesis. It avoids relying on private exactness instances of the
  module-stalk proof module. The same S is used in every tensor clause.
- An arbitrary base module sheaf is `G : RingedSpace.Modules (Spec (.of R)).toRingedSpace`.
  `inverseImage φ G` is the recorded `TopCat.Sheaf.inverseImageModule`, whose scalar
  action is multiplication of local representatives before sheafification.
  `tensorWithInverseImage` is the actual published
  `SheafOfModules.siteDerivedTensorIndependentCoefficients` on
  `(Q(restrictedTilde φ M), Q((HomologicalComplex.single … 0).obj (inverseImage φ G)))`.
  This uses a K-flat derived tensor, including for unbounded M.
- The right-hand tensor is `localizedTensor φ x M ((baseStalkFunctor φ x).obj G)`.
  `baseStalkFunctor` takes the actual stalk G_f(x) and restricts along j.
  `localizedTensor` uses the existing K-flat monoidal tensor on the module derived
  category, with its second factor the `DerivedCategory.singleFunctor … 0` image.
  Thus G_f(x) is in degree zero with exactly the R_p action specified in the node.
- Every R_p-module is `L : ModuleCat.{u} (Localization.AtPrime p)`.
  `skyscraper φ x L` restricts L along `Spec.stalkIso.hom = j⁻¹`, then applies
  `SheafOfModules.ringedModuleSkyscraperFunctor` on Spec R at f(x).
  The last three conjuncts give respectively `G_f(x) ≅ L`,
  `(f⁻¹G)_x ≅ L` after restriction along e_x, and the specialized derived tensor
  isomorphism with right side `Q(M_q) ⊗ᴸ L[0]`.
- The only additional typeclass parameters are the two chosen derived localizations
  `HasDerivedCategory.{wB}` and `HasDerivedCategory.{wT}`. Their morphism universes are
  independent. These are the standard size convention for D(B) and D(R_p), not ring
  or complex restrictions. The site is the existing u-small site of opens and the
  coefficients are in u; no extra universe equality is imposed on derived categories.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `AlgebraicGeometry.exists_affineQCohDerivedEquivalence`; its termwise functor is the
  existing `AlgebraicGeometry.tilde.functor` from `Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes the
  recorded `Scheme.Modules.tensorPullbackRingMap` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. This is the α used here.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`, `RingedSpace.Modules`, and
  `moduleStalkFunctor_preservesZeroMorphisms`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`;
  `Mathlib.Algebra.Category.ModuleCat.Localization`:
  `ModuleCat.localizedModuleFunctor`, whose object is `Shrink (LocalizedModule …)`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and
  `CochainComplex.IsKFlatResolutionIndependentCoefficients`.
- `WeilConjectures.Topology.InverseImageModule`: `TopCat.Sheaf.inverseImageRing` and
  `TopCat.Sheaf.inverseImageModule`, including the canonical section action.
- `WeilConjectures.Topology.RingedModuleSkyscraper`:
  `SheafOfModules.ringedModuleSkyscraperFunctor`, with its actual membership-function
  sections and germ scalar action.
- `Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes`:
  `CochainComplex.sheafDerivedTensorVanishes` is retained as the recorded definition
  of K-flat tensor vanishing; the statement uses the actual tensor object from the
  additionally cited landed node instead of replacing an isomorphism by vanishing.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`; the module derived monoidal tensor is the
  existing K-flat-derived construction exposed by
  `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory` and
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `AlgebraicGeometry.tilde.toStalk` and its
  `IsLocalizedModule` instance, the exact Mathlib match of the recorded localization node.
- `WeilConjectures.AlgebraicGeometry.InverseImageStructureStalkIso`:
  `Scheme.exists_inverseImageStructure_stalk_iso`; the actual k is fixed explicitly
  rather than selected by this existence statement alone.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, characterized by K-flat
  representatives and the unique extension property of its recorded theorem.

The stated proof dependencies are imported without `public` where they are not already
statement dependencies: `relative_inverseImage_stalk_restriction_iso` from
`WeilConjectures.AlgebraicGeometry.RelativeInverseImageStalkRestriction`;
`module_stalk_exact` from `WeilConjectures.Algebra.Homology.ModuleStalkExact`;
`Functor.mapDerivedCategoryFactors` from Mathlib's derived `ExactFunctor`;
`exists_isKFlatResolutionIndependentCoefficients` from the matching Sheaf resolution module;
`isKFlat_iff_stalk_isKFlat` from `Sheaf.Algebra.Homology.KFlatStalkCriterion`;
`exists_inverseImage_stalk_comparison_natural` from
`WeilConjectures.Algebra.Homology.InverseImageStalkScalarTransportNaturality`;
`ringed_kFlat_single_tensor_comparison` from the matching Sheaf module;
`CochainComplex.exists_stalk_tensor_complex_iso` from
`WeilConjectures.Algebra.Homology.StalkTensorComplex`; and
`DerivedCategory.QObjTensorQObjIsoOfKFlatLeft` from
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`.
The Mathlib pullback/sheafification stalk isomorphisms and affine stalk-map formula are
also exposed by the imported modules.

Edge cases checked against the definitions and the source proof:

- Zero ring A: its spectrum has no x, so the pointwise statement is vacuous, as required.
- Zero complex M, zero sheaf G and zero module L: all constructions exist and the
  comparisons specialize to zero objects without a nonzero hypothesis.
- Identity ring map: p=q, j and k supply the ordinary affine stalk localization.
- Nonflat Z → Z/2: restriction is over B, and K-flatness is transported across the
  ring isomorphism R_p ≅ B_x; no assertion transfers K-flatness along R_p → A_q.
- Nonclosed f(x), for example the generic point of an integral affine scheme: the
  skyscraper stalk comparison is at the defining point and uses all its neighborhoods,
  so it does not require closedness.
- Arbitrarily unbounded complexes and arbitrary integer degrees remain present; the
  second tensor factor alone is put in degree zero, exactly as the node says.
- A morphism into its own K-flat complex may be the identity resolution; the universal
  resolution clause includes it, with no requirement to choose one preferred resolution.

Searches for reuse (2026-10-24):

- `msearch.py` LeanFinder query: `derived affine stalk inverse image base skyscraper
  tensor comparison arbitrary complex localization`. Eight hits: a newer Mathlib
  `ModuleCat.Tilde.stalkIso_inv`, skyscraper adjunction lemmas, smooth-sheaf comparisons,
  and an open-immersion restriction stalk iso. None states this composite relative
  derived tensor/skyscraper comparison; the installed Tilde source has `tilde.toStalk`
  and its localization instance, which are used through the existing dependency.
- `msearch.py` LeanSearch query: `affine derived stalk inverse image tensor localization
  skyscraper`. Eight hits including `ModuleCat.Tilde.stalkIso`, `StructureSheaf.stalkIso`,
  and skyscraper adjunction results. No exact match for the full statement.
- `msearch.py` Loogle query: `AlgebraicGeometry.tilde.toStalk, ModuleCat.localization,
  Localization.localRingHom`. Zero hits; the service reports unknown identifier
  `ModuleCat.localization`. The subsequent source grep found the correct existing name.
- `msearch.py` Mathlib grep query `localization.*[Ff]unctor|def.*[Ll]ocaliz|stalk.*[Tt]ensor`
  in `Algebra/Category/ModuleCat`: six hits, giving `localizedModule`,
  `localizedModuleMkLinearMap`, `localizedModuleMap`, and `localizedModuleFunctor`.
  The full functor source was read and reused; no localization functor was copied.
- Repository `rg` searches for affine/relative stalk and localized functor names in
  both `lean/WeilConjectures` and `lean/Sheaf` found affine base-change coordinate
  comparisons and relative tensor homology comparisons. They do not contain this
  statement with all three requested conclusions. The upstream exact
  `relative_inverseImage_stalk_restriction_iso` is retained as a proof dependency.
- Required upstream blueprint-id grep for `lem-trf-affine-relative-stalk-resolution-iso`
  returned no declaration. The proposed `AffineRelativeStalk` helper namespace and
  `exists_affineRelativeStalkResolutionIso` had no match in the two source roots,
  Mathlib, or `dag/lean_names_upstream.json`.

Validation: prescribed `scompile.py Q80 lem-trf-affine-relative-stalk-resolution-iso`
compiled the single file in both sandbox and library-module modes, cleanly (21.7 s and
13.0 s in the final compile). All variables and universes are explicitly bound;
no file-local notation, local instance, private definition, or chosen arbitrary map is used.
All definitions have actual data. The sole `sorry` is the public main theorem.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
