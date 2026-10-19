## Worker report

The item is stated by `CategoryTheory.ringed_presentation_transport` in
`Sheaf.CategoryTheory.RingedPresentationTransport`. The theorem has `sorry` as its
proof. Its conclusion packages the individual comparisons in structures, rather
than replacing any comparison by a hypothesis. All helper definitions contain
actual data: existing module categories, the standard derived localization,
the recorded derived internal Hom, actual termwise exact functor localization,
section multiplication and the existing element-site restriction. Nothing is
selected from an uncharacterized existence theorem.

The source places read are Stacks `sites-modules.tex`, lemma
`morphism-ringed-topoi-comes-from-morphism-ringed-sites` (03CR), including its final
equivalence case; and `algebraization.tex`, lemma
`pushforward-derived-complete` (099J), including its opening presentation reduction.
The node supplies the detailed nine-step refinement. All nine steps are reproduced
in the theorem's proof docstring, with their dependency ids.

The hypotheses and clauses correspond as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Two small site presentations | `C D : Type u`, `[SmallCategory C]`, `[SmallCategory D]`, and Grothendieck topologies `J K` |
| Sheaves of commutative rings | `R : Sheaf J CommRingCat.{u}` and `S : Sheaf K CommRingCat.{u}`; the paper's primed ring is `S` |
| Specified ringed-topos morphism | `e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S)`, the recorded definition, including its underlying geometric adjunction and induced module pushforward |
| Underlying geometric morphism is an equivalence | `[e.inverse.IsEquivalence]`; inverse image has the specified right adjoint `e.direct` |
| Structural ring map is an isomorphism | `[IsIso e.ringMap]`; this is the actual structural map of `e` |
| Module adjunction is an exact equivalence | `whole.transport.modules` is an equivalence; `whole.pushforward` identifies its inverse with `e.modules`; `whole.underlying` and `whole.structural` identify inverse image and the rank-one ring map with those of `e` |
| Exactness and additivity in both directions | `transport.forward` and `transport.backward`, each with `additive`, `finiteLimits` and `finiteColimits` |
| Termwise application on unbounded derived categories | `presentationDerivedMap` is exactly Mathlib's `mapDerivedCategory`; `RingedPresentationFunctor.termwise` retains the natural `Q` factorization through actual termwise application |
| Mutually inverse derived functors | `derivedUnit` and `derivedCounit` identify their two composites with identity functors |
| Preserve K-injective complexes | `kInjective` on both functors: arbitrary integer-indexed cochain complexes, no boundedness condition |
| Every sheaf of sets, and its inverse image | `sliceMorphism A`, `sliceTransport A`, for every `A : Sheaf K (Type u)`; the other slice is over exactly `e.inverse.obj A` |
| Induced equivalence on slice topoi | `sliceTopos` identifies inverse image with the original equivalence applied to arrows, through the recorded fibre equivalences; `sliceInverseEquivalence` asserts it is an equivalence |
| Restricted rings and their structural isomorphism | `presentationElementRing` is the commutative version of the recorded `elementRing`; `sliceRingIsIso`, `sliceSets` and `sliceStructural` retain the original ring map after restriction |
| Same exact, derived and K-injective properties on slices | `sliceTransport A` has the same `RingedPresentationAt` interface as `whole` |
| Slicing a site object uses its sheafified representable | `RingedPresentationRestrictions.siteObject` compares `R.over U` with the element ring over `(presheafToSheaf J (Type u)).obj (yoneda.obj U)`, and compares the actual two module restrictions |
| Commute with restrictions | `restrictionModules` and `restrictionDerived` give natural isomorphisms for restriction from the whole topos |
| Commute with every further restriction | `furtherModules` and `furtherDerived` quantify over every sheaf map `b : B ⟶ A`, using exactly `e.inverse.map b` on the other side; `relocalization` and `derivedRelocalization` give the iterated restriction comparisons |
| Commute with derived internal Hom | `RingedPresentationFunctor.internalHom` is a natural isomorphism of bifunctors using the dependency's `derivedInternalHomOfUniverses`, contravariant in its first variable and covariant in its second; it occurs on both equivalence directions, all slices and restrictions |
| Commute with localization at a section | `RingedPresentationFunctor.localization` uses actual `ringedSectionLocalizationOfUniverses`; its premise identifies the transported multiplication endomorphism, and its conclusion is a module isomorphism commuting with `ringedSectionLocalizationUnitOfUniverses` |
| Every ideal subsheaf | `localTests` quantifies over every module `I` and monomorphism `ι : I ⟶ unit`; no finite generation is assumed |
| Transported ideal is exactly pullback | The new inclusion is explicitly `whole.transport.modules.functor.map ι ≫ whole.transport.forward.unit.hom` |
| Every unbounded derived object | `N : PresentationDerived S` in `localTests` |
| Both families of tests on all objects and all ideal sections | `presentationComplete` is a transparent application of the landed `IsLocallyDerivedRingedIdealComplete`; unfolding gives the exact `∀ U f`, image-of-`ι` membership, and `IsZero (RHom(R_U[1/f], N|_U))` tests in the node |
| If and only if, with pullback of N | The field `localTests` is `↔`, and its right side evaluates the actual termwise-derived forward functor on `N` |

The chosen derived model has morphisms in `u + 1`, obtained from
`HasDerivedCategory.standard (PresentationModules R)`. This is a concrete model
of the full unbounded derived category, with no extra hypothesis. All site,
coefficient and sheaf sizes here follow the node's recorded small-site convention;
`u` is arbitrary. The standard instances are installed only inside definition
bodies, never as new global or file-local instances. There are no `let` binders
in statement signatures, no auto-bound variables, and no file-local notation.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction` (tensor adjunction proof input).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (the dependency is a Mathlib match and has no Lean record).
- `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`:
  `CategoryTheory.exists_localizedSheavesOverRepresentable` (proof input for site objects).
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `CategoryTheory.ringedSectionLocalizationOfUniverses` and
  `CategoryTheory.ringedSectionLocalizationUnitOfUniverses` (the recorded module publicly
  retains its earlier interfaces).
- `Sheaf.CategoryTheory.RingedIdealGenerators`:
  `CategoryTheory.IsRingedIdealGeneratingList` supplies the recorded convention of an
  ideal as a module monomorphism into the ring; generation is not assumed here.
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`:
  `CategoryTheory.elementProjection`, `elementTopology`, `elementRing`,
  `elementSheafPullback`, `elementModulePullback`, `elementMap`,
  `elementModulePullbackOver`, `RingedSheafSliceAdjunctionData`,
  `ringed_sheaf_slice_adjunction` (dependency repair described below).
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  (proof input for the Hom comparison).
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CategoryTheory.ringedDerived_closed_symmetric_monoidal` (proof input).
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`:
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes` (proof input).
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj` (through the Hom-complex dependencies).
- `Sheaf.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex` (through derived Hom).
- `Sheaf.CategoryTheory.LocalCoefficientLocalization`:
  `CategoryTheory.localCoefficientRings` and `localCoefficientLocalization` (the latter is
  the colimit description in proof step 7).
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`:
  `CategoryTheory.IsLocallyDerivedRingedIdealComplete`. Its already landed node is added
  to `stmt_deps` because the last clause uses precisely this existing predicate.
  The landed local-coefficient-localization node, already a proof dependency, is also
  added to `stmt_deps` for its transparent underlying-ring abbreviation.

Edge cases checked mathematically before and while writing:

- Identity equivalence: the comparisons can be the canonical identity comparisons.
- Empty site, empty element site, empty covers and the initial sheaf: zero module/derived
  categories and vacuous test families cause no missing hypothesis.
- Terminal sheaf and infinite sheaves: element sites have all the indicated objects;
  the infinite case detects the repaired adjunction-direction error.
- Non-subcanonical sites: the code explicitly sheafifies the representable.
- Zero ring and zero object: every relevant category or test is zero as appropriate.
- Scalar zero: its localization is zero; scalar one or a unit: localization is the ring.
- Zero ideal: the only scalar test is zero, hence every N satisfies it.
- Unit ideal: the scalar-one tests force local vanishing, preserved by the equivalence.
- Arbitrary ideal and unbounded N: no finite generation, flatness, injective terms or
  boundedness has been assumed.
- All global scalars on every element site, and all maps `B ⟶ A`, are quantified,
  rather than just scalars on representables or maps induced by site morphisms.

Searches for an existing statement:

- `msearch.py` LeanFinder, query "An equivalence of ringed topoi gives an exact equivalence
  of module sheaves and unbounded derived categories commuting with internal Hom and
  localizations": eight results, including `mapDerivedCategory`, its factorization and
  shift/linearity instances. None states transport of a ringed-topos equivalence and its
  slices and local tests.
- `msearch.py` Loogle, query `"SheafOfModules", "Equivalence"`: three results,
  `SheafOfModules.pushforwardPushforwardEquivalence` and its two component formulas.
  This is an equivalence of presented site categories, not the arbitrary geometric
  equivalence in this item.
- `msearch.py` grep, query `equiv.*ringed|ringed.*equiv` in Mathlib `CategoryTheory`:
  no results.
- `msearch.py` LeanSearch, query "Equivalence of ringed topoi transports module sheaves
  derived internal Hom scalar localization and local derived completeness": eight results,
  including the site-functor pullback adjunction, unit-Hom equivalence and ordinary module
  localization. No result states this item.
- `rg` in the upstream library and `lean/Sheaf` for ringed equivalences, presentation
  transport and the exact node id found neighbouring flat coefficient-change equivalences
  and citations to this item, without its declaration. `grep -rn` for the exact id in the
  upstream `WeilConjectures` source returned no match. The neighbouring
  `flat_ringed_ideal_complete_equivalence` concerns a coefficient change on a fixed site
  with a flatness and quotient-isomorphism hypothesis, not an equivalence of topoi.
- Searches for the dependency data and `localization_modules` found only the owning
  dependency file in the published side sources and no upstream copy or external users.

No correction to the item's mathematical statement was needed. No new independent
notion or new DAG node is introduced. The helper structures only package this node's
multiple conclusions, and the abbreviations reuse existing definitions.

## Dependency modules

`lem-weil-pbc-ringed-sheaf-slice-adjunction` retains its existing owning module
`Sheaf.CategoryTheory.RingedSheafSliceAdjunction`. Its published structure incorrectly
had `localization_modules : localization.modules ⊣ pullback`. In the point topos,
for an infinite sheaf A, restriction is the diagonal functor, direct image is the
product functor, and extension by zero is the direct sum functor. The product functor
is not left adjoint to the diagonal: it does not preserve coproducts (the diagonal
family of copies of Z gives the direct-sum-to-product comparison). Thus the former
field was false, not merely inconvenient. The dependency's natural-language node says
that restriction is module pullback and has an exact left adjoint; it does not assert
that reversed module-direct-image adjunction.

The field is repaired to `pullback ⊣ localization.modules`, the usual module adjunction.
Its field docstring and the theorem's step 3 now say this direction explicitly. The
existing element sites, maps, fibre equivalence, restricted rings, formulas,
`extensionByZero ⊣ pullback`, exactness and relocalization are retained. Only this
node's `lean` record changes, with a §1(B) note; no natural statement is corrected.
The modules are compiled separately, in dependency order, by `scompile.py`. The
consumer `RingedPresentationTransport.sourceSlices` / `.targetSlices` uses the repaired
data and compiles with it. A search found no existing external projection users.

`lem-weil-pbc-localized-sheaves-over-representable` also retains its owning module
`Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`. Its recorded declaration
accepted only a `Precoverage` with `HasIsos`, stability under composition/base change,
and `HasPullbacks`. That interface cannot be applied to the general Grothendieck topology
of this item without extra assumptions on the presentation. In particular, using the
precoverage of all covering presieves would demand categorical pullbacks for its covering
arrows; these are not part of the node. The natural-language node explicitly rules out
an existence-of-all-fibre-products assumption.

The repaired signature takes `(J : GrothendieckTopology C) (U : C)` directly. Small-site
sheafification is inferred canonically. Every conclusion is retained verbatim except for
replacing `J.toGrothendieck` by `J`: the disjoint-union presheaf, its projection, its
restrictions and arrow action, the equivalence after sheafification, the fibre inverse,
and its restrictions and arrow action. The proof docstring now explicitly says that
covering refinements use pullback sieves rather than categorical fibre products. This is
exactly Stacks 00Y1 and the disjoint-union formula of `lemma-describe-j-shriek`; both source
passages were opened. Its node changes only in `lean`, with a §1(B) note. Searching the
side and upstream Lean found no external applications of this declaration. The primary
consumer is still stated on arbitrary `J K` and explicitly uses sheafified representables;
no pullback instance was added to it.

## Validation

The prescribed `scompile.py NF lem-weil-pbc-ringed-presentation-transport` compiled the
repaired dependency and its consumer separately, cleanly, in dependency order. The
initial full consumer compile took 27.1 seconds and the dependency 5.3 seconds, within
the unchanged 60-second limits. The only new theorem proof is `sorry`; the copied
dependency's already postponed proofs remain `sorry`. Final delivery preflight and
compilation are run by the prescribed `deliver2.py` wrapper.

The first complete dry run passed server preflight and per-file compilation. The final
module also lists the already transitive Mathlib module/derived/K-injective imports and
the Hom-complex proof imports directly, to make every dependency's module explicit.
Exact-name searches found no collision; the similarly named `presentationDerivedMap`
in `AlgebraicGeometry.Etale` has a different full name and different purpose.

A final dependency review found and repaired the representable-slice precoverage
restriction described above. This adds a third module and its lean-only dependency node
record to the complete packet. The final dry run includes all three modules.
The generalized representable-slice dependency compiled cleanly on its own through
`scompile.py` (6.8 seconds for the library file); its signature has no precoverage or
categorical-pullback hypotheses.

The complete three-module dry run passed server preflight and all per-file compiles.
The two retained direct-sum identity/composition helper docstrings were also expanded
with their summand calculations; their signatures and postponed proofs are unchanged.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
