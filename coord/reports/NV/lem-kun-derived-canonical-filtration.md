## Worker report

This repairs the independent stage-2 return for immutable head `0f082c1dd697`:
“The theorem signature does not specify T on representative objects/maps or
compatible representative independence required by the node.” The retained packet's
initial `deliver2.py --no-push` passed at `aa5d791540`, confirming that this was a
statement defect rather than a mechanical failure. The existing filtration and
quotient clauses have been retained. The final existential has been repaired, rather
than resubmitted unchanged. Only the item's `lean` field changes; no mathematical
statement, dependency node, or target is changed.

The module `Sheaf.Algebra.Homology.DerivedCanonicalFiltration` states
`DerivedCategory.exists_derivedCanonicalFiltration`. Every theorem proof remains
`sorry`, as required for stage 2. There are no new definitions or new nodes.

Hypothesis and clause correspondence:

- The commutative ring is `(R : Type u) [CommRing R]`. The localization size is
  `[HasDerivedCategory.{w} (ModuleCat.{u} R)]`; `w` remains independent of `u`.
  `DerivedCategory.Bounded (ModuleCat R)` is the recorded full subcategory of
  objects with bounded cohomology, not a category of chosen termwise representatives.
- The target is `(finiteFilteredModuleQuasiIso R).Localization`. The functor used
  on representatives is exactly `finiteFilteredModuleHomotopyQuotient R ⋙
  (finiteFilteredModuleQuasiIso R).Q`, so it takes filtered chain maps first to
  their filtered homotopy classes and then to the prescribed localization.
- Good upper truncation is specified by `(F K).step i =
  Subobject.mk (K.ιTruncLE (-i))`. The finite-bound conjunct gives `a < b`, top
  step `a`, and bottom step `b` whenever `K` vanishes outside a finite interval.
  `hfinite` supplies the corresponding proof of the existing `IsFinite` predicate
  for every bounded termwise complex.
- The two-term graded quotient is the existential `M,e,e₀,e₁`. The degrees are
  `-i-1,-i`; all other terms are zero. `e₀` identifies the first term with the
  cokernel of the kernel inclusion, hence the image of the incoming differential;
  `e₁` identifies the second with `K.cycles (-i)`. The monomorphism and differential
  equation specify the image-to-kernel inclusion. The equation using
  `K.homologyπ (-i)` specifies the cycle-quotient map `pi K i`, and its `QuasiIso`
  conjunct makes it the required comparison to shifted cohomology.
- The next three conjuncts supply filtered lifts of chain maps, their commutation
  with `pi`, filtration-preserving lifts of the supplied homotopy components,
  and graded quasi-isomorphisms for quasi-isomorphisms. These use the existing
  `FilteredObject.HomPreservingSteps` and `gradedMapSteps` interfaces.
- `T` has source the bounded derived category and target the specified finite
  filtered localization. `eOmega : T ⋙ omega ≅ Bounded.ι` and `eGr i` give the
  two natural isomorphisms in the node, with the latter's target exactly
  `H^{-i}(-)` followed by the degree-zero single functor and shift by `i`.
- **All representative objects, repaired:** `rep` is a single family of
  isomorphisms `T.obj C ≅ Q_W(q(K,F K))`, universally quantified over every
  bounded termwise `K` and every `eC : C.1 ≅ Q.obj K`. This replaces the old
  existential assertion about just one representative per object. The separate
  bounded-representative existence conjunct ensures every `C` has such objects.
- **Representative maps, repaired:** for every filtered chain map `f` of bounded
  representatives and every pair of identifications `eC,eC'`, the equation for
  `T.map (ObjectProperty.homMk (eC.hom ≫ Q.map f.hom ≫ eC'.inv))` says, after
  conjugation by these same `rep` isomorphisms, that its value is precisely
  `(q ⋙ Q_W).map (ObjectProperty.homMk f)`. The earlier chain-map conjunct
  guarantees that every ordinary chain map has this filtered lift.
- `omega` and `gr` are specified on all finite filtered representatives, including
  maps: `eForget P` identifies the underlying object with `Q(P.obj.obj)`, and
  `eGrade i P` identifies the grade with `Q(P.obj.filtration.gradedPiece i)`.
  Their two naturality equations require their maps to be exactly the ordinary
  derived images of the underlying chain map and of `gradedMapSteps`.
- **Comparisons on representatives, repaired:** the forgetful normalization is
  `eOmega.hom.app C ≫ eC.hom = omega.map (rep ...).hom ≫ (eForget ...).hom`.
  The graded normalization equates `eGr` transported using `eC` and
  `homologyFunctorFactors` with `gr.map (rep ...).hom`, then `eGrade`, then
  `Q.map (pi K i)`, then the inverse of the canonical
  `singleFunctors.shiftIso i (-i) 0 (add_neg_cancel i)`. Thus the comparison is
  the specified cycle quotient; it is not an unrelated natural isomorphism.
- **Compatible representative independence, repaired:** for every bounded roof
  `K ← M → L`, every derived `f` represented by that roof after `eC,eC'`, and
  every filtered lift of its legs `s,g`, the roof conjunct gives invertibility
  of `(q ⋙ Q_W).map s` and the exact equation
  `rep_K.inv ≫ T.map f ≫ rep_L.hom = (Q_W q(s))⁻¹ ≫ Q_W q(g)`.
  The same fixed `rep` family occurs in the map, roof, and normalization equations.
  In particular, with `C = C'` and `f = 𝟙 C`, this determines the transition
  `rep_K.inv ≫ rep_L.hom` between any two bounded representatives by every roof
  inducing their identification in `D(R)`. Two such roofs give the same morphism.
  The two normalization equations require these transitions to preserve both the
  underlying identification and the specified graded quotient comparison.
  Applying this to any family of bounded representatives gives a natural
  isomorphism with `T` compatible with the formulas. No functorial choice of
  termwise representatives is hypothesized.
- The two final equations cover every derived morphism and state its underlying
  map is the original map and its graded map is `H^{-i}(f)[i]` under these same
  normalized comparisons.

Dependency declarations read and used:

- `Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy`:
  `CochainComplex.FiniteFilteredModuleComplex`, `FiniteFilteredModuleHomotopy`,
  `finiteFilteredModuleHomotopyQuotient`, and `finiteFilteredModuleQuasiIso`.
- `Sheaf.Algebra.Homology.FilteredTensorLocalization`:
  `CochainComplex.filteredTensor_localization`; its forgetting/graded descent
  interfaces specify their representative objects and maps. Our `eForget` and
  `eGrade` express their resulting representative identifications directly.
- `Sheaf.Algebra.Homology.CanonicalTruncationFiltration`:
  `CochainComplex.exists_canonicalTruncationFiltration`.
- `Sheaf.Algebra.Homology.BoundedDerivedRoofs`:
  `DerivedCategory.boundedDerivedRoofs`, including bounded common refinements in
  the homotopy category. No calculus of fractions for strict ordinary chain maps
  is assumed.
- `Sheaf.Algebra.Homology.FilteredQuasiIsoFractions` (proof import):
  `CochainComplex.finiteFilteredModuleQuasiIso_fractions`.
- Filtration/subquotient dependencies: recorded upstream
  `CategoryTheory.DecreasingFiltration` in
  `WeilConjectures.CategoryTheory.Abelian.Filtration`, and the compatibility
  `FilteredObject.HomPreservingSteps`/`gradedMapSteps` and graded quotient through
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
  `Sheaf.CategoryTheory.FiniteFiltrationInduction`.
- Mathlib dependencies: `DerivedCategory`, `HasDerivedCategory`, `Q`,
  `DerivedCategory.Bounded`, `Bounded.ι`, and `DerivedCategory.TStructure.t` in
  the recorded `DerivedCategory.Basic` and `DerivedCategory.TStructure` modules.
  The canonical comparison and shift signatures used in the repair were read in
  `DerivedCategory.HomologySequence` (`homologyFunctorFactors`),
  `DerivedCategory.Basic` (`singleFunctors`, `singleFunctorIsoCompQ`), and
  `CategoryTheory.Shift.SingleFunctors` (`SingleFunctors.shiftIso`).

Sources reread: local Stacks `more-algebra.tex`, Tag 0H7Z,
`lemma-kunneth-spectral-sequence` (the displayed canonical filtration);
`homology.tex`, Tag 0118, `section-truncations`; and `derived.tex`, Tag 05S6,
`lemma-filtered-bounded-derived`. The node explicitly includes simultaneous
representative functoriality and independence as the extension being stated.

Edge cases checked: zero complexes and one-term complexes have admissible bounds;
`i` ranges over all integers, including zero and both signs; all bounded intervals
can be enlarged, so `a < b` does not exclude the zero object. `rep` includes
arbitrary identifications `eC`, including nonidentity automorphisms and different
bounded models of the same object. The roof clause includes identity morphisms,
identity denominators, and all bounded refinements; no representative or roof is
selected in its hypotheses. The comparisons use canonical homology and shift
isomorphisms, so they also cover acyclic graded pieces. No nonzero, finite
presentation, projectivity, or flatness assumption on `R` or `K` is added.

Searches retained from the saved packet: `msearch.py leanfinder` for canonical
truncation filtration and bounded derived filtered localization returned individual
Mathlib truncation functors only; `msearch.py loogle` for `"trunc", "Functor"`
returned the individual truncation functors; `msearch.py grep` for
`canonical.*filtrat|trunc.*filtered|filtered.*trunc` returned only an unrelated
probability filtration. The saved node contains the actual search outputs.
The project's dependency modules were the only matches from the retained `rg`
searches over `WeilConjectures` and `lean/Sheaf`. In this repair, `rg` for
`theorem exists_derivedCanonicalFiltration` over Mathlib, upstream
`WeilConjectures`, and the shared `lean/Sheaf`, and `rg` for this node id over
upstream `WeilConjectures`, found no existing declaration. Direct source searches
located the canonical `homologyFunctorFactors` and `SingleFunctors.shiftIso`
instead of introducing duplicate constructions.

Validation: the repaired module passed both sandbox and library per-file checks
through `scompile.py`. No warning remained. Line lengths are at most 100,
`autoImplicit` is false, all universes are bound, and the node's `lean.statement`
is extracted verbatim from the theorem signature. A comparison with the current
shared node found only the authorized `lean` field changed.

## Second reading by NV

I reread the repaired declaration against every clause of the unchanged node.
The commutative ring and `D^b(R)` binders remain unchanged. The target is the same
filtered homotopy localization, and the representative functor is exactly its two
canonical quotient functors. The retained first six conjuncts give good truncation,
finite filtration, the two-term graded quotient, map naturality, filtered homotopy,
and graded quasi-isomorphism invariance. The old final object assertion was only
existential, despite the saved report incorrectly describing it as universal.
It has now actually been replaced by the universal `rep` family. Its chain-map
square refers to `T.map` itself and the localized image of that same chain map.
The new roof equation refers to `T.map f` for every bounded roof, including the
identity roofs that express transitions between representatives. The same `rep`
occurs in both normalization equations, which explicitly use `eC` and the specified
`pi K i`; thus representative independence also preserves the comparisons.
`eForget` and `eGrade` have map equations, so their names do not stand for arbitrary
object identifications. The final naturality equations retain all derived maps.
No extra hypotheses or notions were introduced and no statement correction is
needed. The revised signature fixes the entire returned point rather than merely
changing its explanatory prose.

## H3 repair

The returned review identified that the homotopy conclusion supplied unrelated degreewise lifts and did not assert a coherent filtration-preserving chain-homotopy equation. The homotopy conjunct is now strengthened exactly at that clause: for each filtration index `i`, it supplies subcomplex chain maps `hf_i` and `hg_i`, a single `h_i : Homotopy hf_i hg_i`, equations identifying their composites with the original `f` and `g` through the filtration arrows, and, for every pair of degrees `n,m`, the coherent component equation
`((F K).step i).arrow.f n ≫ h.hom n m = h_i.hom n m ≫ ((F L).step i).arrow.f m`.
This quantifies one homotopy object over all degree components and therefore rules out the unrelated-lift interpretation. The original `hf` and `hg` filtered lifts remain explicit and are connected to `f` and `g` by their `hom` equations.

The repaired file was recompiled with `scompile.py` successfully. The node's `lean.statement` was regenerated verbatim from the theorem signature on 2026-10-18; no other node field was changed.
