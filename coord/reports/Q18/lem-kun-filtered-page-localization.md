## Worker report

This repairs immutable returned head `3bffe6b5a5e0`. The saved packet initially
passed the required dry run at `0448118032`, but the required mathematical
self-check confirmed that it retained the returned defects. The valid cokernel
transition and normalized page-functor construction are retained. The stationary
image, comparisons and full descent statement are repaired. The saved node and
current shared main have identical fields outside `lean`; this delivery updates
only `lean` and the owning module. The delivery wrapper rebases the packet on
current `newtargets-dag`.

`CategoryTheory.filteredPageLocalization` states `Nonempty
(FilteredPageLocalizationData R)`. This is an existence statement for the entire
specified, normalized descent package, rather than existence of arbitrary
unnormalized isomorphisms. All of the package's definitions have real data.
The postponed theorems are `finiteFilteredPageTransition_projection` (the
node's Step 1), `finiteFilteredCohomologyImage_succ_le` (Step 5, needed by
the filtration definition), and `filteredPageLocalization` (all eleven steps).
All three are listed in `lean.declarations`; each has a source and proof docstring. Every other helper
also has its own source and blueprint docstring.

Hypothesis and clause correspondence:

- **Commutative ring and unbounded finite filtered complexes:** `(R : Type u)
  [CommRing R]` and `CochainComplex.FiniteFilteredModuleComplex R` use the
  recorded uniformly finite filtration category. No condition on cochain degrees
  or extra size assumption is imposed. `finiteFilteredOrdinaryDerivedCategory`
  explicitly uses `HasDerivedCategory.standard`, so ordinary derived cohomology
  requires no additional instance binder. All universes are explicitly named.
- **H_f, W, D_f and quotient functors:** the recorded
  `FiniteFilteredModuleHomotopy`, `finiteFilteredModuleQuasiIso`,
  `finiteFilteredModuleHomotopyQuotient`, their actual `Localization` and `Q`
  occur in `finiteFilteredModuleDerivedCategory`,
  `finiteFilteredModuleLocalizationFunctor` and `finiteFilteredDerivedQuotient`.
- **Canonical phi:** `finiteFilteredPageTransition` is the actual cokernel
  descent of the inclusion from step `a` into step `a-t+1`.
  `finiteFilteredPageTransition_projection` specifies its projection equation.
- **Specified normalized S:** `finiteFilteredPageFunctor`,
  `finiteFilteredPageFirstIso` and `finiteFilteredPageImageIso` project S, e1 and
  eI from the SAME invocation of
  `boundedFilteredComplex_pageFunctor_normalized`. Its normalized successor
  isomorphisms are the actual `.iso` fields of this S, not new witnesses.
- **I and its successive quotient:** `finiteFilteredCohomologyImage` is
  `imageSubobject (homologyMap (step a).arrow n)`.
  `finiteFilteredCohomologyFiltration` constructs the decreasing filtration with
  exactly these steps. `finiteFilteredCohomology` is the functor to the existing
  `FilteredObject (ModuleCat R)`, using `imageSubobjectMap` for restrictions.
  Its `gradedPiece a` is the cokernel of `I^(a+1) -> I^a`.
- **Descent including maps on H, I and I quotients:** `Sbar,eS` and `Hbar,eH`
  give functorial descent through the actual composite quotient. The target of
  `Hbar n` is the filtered-object CATEGORY, so each localized morphism preserves
  every image step. Its canonical step and quotient maps are the existing
  `FilteredObject.restrictionSteps` and `FilteredObject.gradedMapSteps`.
  `finiteFilteredDescendedMap` transports these maps to the cochain endpoints by
  the descent natural isomorphism. Functor laws and naturality, not free maps,
  govern all these maps.
- **Filtered homotopy invariance:** `homotopy_invariance` gives equality of
  spectral-sequence morphisms, of ordinary cohomology maps, of filtered
  cohomology morphisms, of every image-step restriction, and of every image
  quotient map. Equality of spectral-sequence morphisms gives equality on each
  positive page.
- **Every w in W:** `quasiIso_representatives` applies to EVERY chain
  representative whose homotopy class belongs to W, and asserts `QuasiIso` on
  the underlying complex and every `restrictionSteps f.hom a`; it also asserts
  `IsIso` on H, the filtered H object, every image step and every quotient.
  Every W morphism has a representative by its recorded definition.
  `quasiIso_pages` additionally quantifies over W itself in H_f and asserts
  isomorphisms of spectral sequences and of each positive page.
- **Ordinary derived cohomology:** `omega,eOmega` descend the actual forgetful
  functor to the recorded Mathlib `DerivedCategory`. `ordinaryCohomology`
  identifies descended H with `omega` followed by the existing
  `DerivedCategory.homologyFunctor`. `ordinary_normalization` equates the
  cochain comparison with `eOmega`, the standard
  `DerivedCategory.homologyFunctorFactors` and `eH`; this excludes incompatible
  arbitrary identifications. Naturality of this iso gives the equality of maps
  for all filtered derived morphisms.
- **Page-one naturality:** `gradedDerived,gradedComparison,graded_chain` give
  the descended graded functor with its actual chain representative action.
  `page_one` is its cohomology square for ANY D_f morphism, using the chosen e1.
  `page_one_chain` explicitly has component
  `homologyMap (FilteredObject.gradedMapSteps f.hom a) (a+b)`.
- **Correct stationary image:** `finiteFilteredAmbientQuotient R U a` is
  `cokernel (step (a+1)).arrow`, hence U/F^(a+1), and
  `finiteFilteredAmbientMap` is `step a .arrow` followed by this quotient.
  `finiteFilteredQuotientImage` takes its cohomology image. It no longer uses
  `complexQuotientπ a (a+1)`, which lands in gr^a.
- **First CANONICAL stationary isomorphism:** `bound` and
  `stationary_window` choose sufficiently large filtration indices.
  `comparison` supplies one coherent family of
  `FilteredPageStationaryComparison`. Its `core_normalization` requires the
  page-to-image map, followed by the monic image inclusion, to equal the
  CHOSEN core eI, its image inclusion, and the cohomology map of the canonical
  `finiteFilteredWindowToAmbient`. Thus it is the core comparison, not an
  unconstrained iso. Bidegrees `(a,b)` cover `(a,n-a)` by `b=n-a`.
- **Second NORMALIZED isomorphism and inverse:** `imageToGraded` targets the
  actual cokernel quotient of I. `representative_forward` equates its composite
  with `factorThruImage H(ambientMap)` to
  `factorThruImageSubobject H(step inclusion)` followed by the cokernel
  projection. `representative_inverse` gives the reverse equation.
  These equations are on H^n(F^a); precomposition with the epic cohomology
  projection from its cycles is exactly the stated x-to-[x] representative
  rule. The maps out of H^n(F^a) are epic onto both quotient objects, so the
  equations determine both maps uniquely.
- **Both squares for all D_f morphisms:** `imageDerived,imageComparison` give
  a FUNCTOR on D_f whose chain-map action is forced by `image_chain`: after the
  monic image inclusion it equals cohomology of the actual cokernel-induced
  `finiteFilteredAmbientQuotientMap`. Hence its transported map is the induced
  image map and is fixed on the localization, with no free `quotientMap`.
  `stationary_naturality` and `stationary_graded_naturality` quantify over ANY
  `alpha : Q(U) -> Q(V)` and use this same functor map, the SAME chosen
  comparison family, and the induced `gradedMapSteps` of descended H. The bound
  requires stationarity of the endpoints only, not of any roof representative.
- **Adjacent stationary pages:** `successor_agreement` equates the map from
  page-t cycles through `iCycles` and the t comparison with the map through
  `homologyπ`, the ACTUAL normalized `.iso t (t+1)` of S, and the t+1
  comparison. `successor_graded_agreement` equates the normalized second isos
  at adjacent pages. Together these are both adjacent comparison agreements.

Dependency declarations read and used:

- `Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy`:
  `CochainComplex.FiniteFilteredModuleComplex`, `FiniteFilteredModuleHomotopy`,
  `finiteFilteredModuleHomotopyRel`, `finiteFilteredModuleHomotopyQuotient`,
  `finiteFilteredModuleQuasiIso`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `DerivedCategory.homologyFunctorFactors`.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`:
  `CategoryTheory.DecreasingFiltration` with `F` and `F_succ_le`.
  Its source was read through `scompile.py --source`, because the older local
  source checkout lacks that published module.
- `Sheaf.CategoryTheory.Filtration`: the compatible existing
  `FilteredObject` category and `DecreasingFiltration.gradedPiece`;
  `Sheaf.CategoryTheory.FiniteFiltrationInduction`:
  `FilteredObject.restrictionSteps`, `FilteredObject.gradedMapSteps`.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `DecreasingFiltration.complexQuotient`, `complexQuotientπ`.
- `Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized`:
  `boundedFilteredComplex_pageFunctor_normalized`; its full signature and
  docstring, including the shared eZ and representative clauses, were read.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`:
  `SpectralSequence`, `CohomologicalSpectralSequence`, page and successor data.
- Proof-only imports: `Sheaf.CategoryTheory.DegreewiseFilteredAcyclic`,
  `Sheaf.Algebra.Homology.FilteredQuasiIsoFractions`,
  `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`, and
  `Mathlib.CategoryTheory.Localization.CalculusOfFractions`. The normalized
  dependency already imports the bounded page core, and the localization
  construction/calculus imports the localization universal property.

Edge-case checks:

1. Returned counterexample: U=(R --id--> R), F^0=U, F^1=(0->R), F^2=0,
   a=n=1. The repaired target is H^1(U/F^2)=H^1(U)=0, so its image and
   I^1/I^2 are both zero. The erroneous image R in H^1(gr^1 U) is excluded.
2. Zero complex and zero ring: all image, quotient and page objects are zero;
   the normalization equations still make sense. No nonzero-ring assumption.
3. Outside the filtration interval: for a at or above the zero bound, I^a=0;
   below the whole bound, I^a=I^(a+1)=H, so stationary quotients vanish.
4. t=1: the transition is the identity of gr^a. The chosen first-page comparison
   is retained with its naturality; stationarity is asserted here only when
   the object's bound permits it.
5. Complexes unbounded in both cochain directions: the only bounds are on
   filtration indices. For fixed (a,b) the required window is eventually whole
   on the left and zero on the right, uniformly in cochain degree.
6. A general derived roof need not have a middle object stationary at the
   endpoints' index. The final naturality fields nevertheless cover every
   derived morphism at every index beyond the TWO endpoint bounds; Step 10 of
   the proof explicitly raises the roof index then descends via Step 9.
7. Normalization is essential: changing a stationary comparison by multiplication
   by -1 generally violates `core_normalization` or `representative_forward`.
   There is no universal quantification over arbitrary cU,cV with adjustable
   intervening maps.

Searches retained and refreshed:

- Saved `msearch.py ... leanfinder "filtered spectral sequence page localization
  and image filtration through graded quasi-isomorphisms"`: generic derived
  and quasi-isomorphism results only.
- Refreshed `msearch.py ... leanfinder "Filtered cohomology image filtration of
  finite filtered complexes and stationary pages descends to filtered derived
  category"`: eight generic derived-category bounded-representative results;
  no exact statement or definition of this descent package.
- Saved `msearch.py ... loogle "MorphismProperty.Localization,
  CohomologicalSpectralSequence, homologyMap"`: no hits. Refreshed Loogle query
  `factorThruImageSubobject, homologyMap, cokernel.map`: no hits (service does
  not recognize `factorThruImageSubobject`). The actual declaration was read
  in Mathlib's `CategoryTheory/Subobject/Limits.lean` instead.
- Saved Mathlib grep `FilteredPage|filtered.*localization|image.*filtration`:
  no matching theorem. Refreshed `msearch.py ... grep
  'FilteredPageStationary|filteredPageLocalization|finiteFilteredCohomology'
  Mathlib/Algebra/Homology`: zero hits.
- `rg` of `WeilConjectures/` and shared `lean/Sheaf/` for
  `FilteredPageStationaryComparison|finiteFilteredQuotientImage|
  filteredPageLocalization`: no matches before this sandbox repair. Existing
  categorical image maps, cokernels, derived cohomology and filtered maps were
  reused rather than redefined.

No natural-language statement correction, dependency repair, new node or
STATEMENT-DISPUTED flag is needed: the source node already specifies the right
ambient quotient and every repaired clause. The sole direct citer is
`lem-kun-bounded-tensor-tor-spectral-sequence`; its natural-language dependency
is unchanged. This delivery does not edit that citer.

## Repair self-check by Q18

This is the author's self-check; independent review is performed by the
maintainer, as the remote-worker brief requires. Every point of the return was
checked against the node and module:

- H3 wrong image: now the ambient quotient, with the counterexample checked.
- H3/H5 arbitrary isos: first comparison fixed by core eI; second comparison
  fixed in both directions on representatives; induced image maps fixed by a
  functor and its chain action. No old stationary-naturality structure remains.
- H3 missing clauses: H/I/quotient descent and homotopy invariance, all W
  quasi-isomorphism and isomorphism clauses, ordinary derived identification,
  page-one naturality, all derived morphisms, and adjacent successor agreement
  all appear as the fields listed above.
- H4 derived category: actual `DerivedCategory`, `Q`, ordinary H and its
  comparison now occur in types and normalization equations.
- H8: each helper has a source/blueprint docstring, including the projection
  theorem. The main theorem has eleven numbered proof steps with their nodes.

Validation results are recorded below after the final compile and dry run.

Validation: the final module passed both per-file checks run by `scompile.py`
through the delivery dry run, with no errors or warnings. The dry run printed
`OK (dry run): commit 2d830f1e95 passes the preflight and compiles; nothing pushed`.
The self-check also verified no lines over 100 characters, no auto-bound
variables, no private/local notation or scratch commands, exactly three named
`sorry` theorems, all 28 top-level declarations recorded, an exact verbatim main
theorem signature, and `lean` as the sole changed natural-language-node field.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
