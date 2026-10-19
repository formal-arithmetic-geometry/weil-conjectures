## Worker report

Repair of returned head fa75fd2745b3 (H1 and H2). The retained sandbox contained only launcher brief markers and no delivered node, module or report. I rebuilt the packet from the current shared node. Its split_report.summary and all other stage-1 fields are preserved verbatim; this delivery changes only lean on the item and the localized-site dependency. No citations.json is required or claimed. There are no new nodes and no statement correction.

The module Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete states CategoryTheory.isLocallyDerivedRingedIdealComplete_derivedInternalHom with the sole postponed proof `sorry`. Source: literature/stacks-project/algebraization.tex, lemma-derived-complete-internal-hom (Tag 099A), read together with definition-derived-complete (0999). The source allows arbitrary unbounded K and complete N and supplies exactly the asserted conclusion. Both the module and theorem docstrings cite the source and blueprint node. The theorem docstring includes all four DAG proof steps, naming restriction, derived currying, localization coefficient extension and orthogonality, and the final completeness criterion.

Hypothesis and clause correspondence:

- A site small in the module universe is `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`. Modules and coefficient sections have universe u; w is the chosen universe of derived morphisms.
- The sheaf of commutative rings is `(O : Sheaf J CommRingCat.{u})`. Applying sheafCompose with forget₂ CommRingCat RingCat only forgets commutativity for the existing module-sheaf API.
- The ideal subsheaf is a module sheaf I and an inclusion `ι : I ⟶ SheafOfModules.unit ...` with `[Mono ι]`. This is the existing ideal-subsheaf presentation, not finite generation, flatness or any condition on the ideal's generators. A submodule of the rank-one module over a commutative ring sheaf is an ideal. No finite-type predicate appears.
- The unbounded D(O) is `ringedSiteDerived O`, the existing transparent abbreviation of `DerivedCategory (ringedSiteModules ...)`. The HasDerivedCategory binders on C and each C/U specify the localization size needed by the recorded completeness predicate, rather than a mathematical boundedness or resolution hypothesis.
- Both `K N : ringedSiteDerived O` are arbitrary objects. The only property of N is `(hN : IsLocallyDerivedRingedIdealComplete O I ι N)`; no property of K is assumed.
- The derived internal Hom H(K,N) is exactly `((derivedInternalHomOfUniverses.{u, u, u, w} J O).obj (op K, N))`, the current dependency's recorded functor, with its site and module universes specialized to the small-site setting. Its first input is contravariant.
- The conclusion is `IsLocallyDerivedRingedIdealComplete O I ι` applied to that object. Unfolding the shared predicate, both hypothesis and conclusion quantify over every U and every f in the sectionwise image of ι, require IsZero of derived Hom from the degree-zero sheafified localization on C/U, and use the shared exact derived slice restriction.
- There are no boundedness, finite-generation, finite-type-ideal, flatness, nonemptiness, nonzero-ring or characteristic assumptions.

Dependency declarations read and used:

- def-weil-sheaf-of-modules-category: Sheaf.CategoryTheory.RingedSiteModules, CategoryTheory.ringedSiteModules, transparently Mathlib SheafOfModules. Read its full signature and module docstring and Mathlib's underlying sheaf/module and morphism structures.
- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic, DerivedCategory and HasDerivedCategory, with localization of integer-indexed cochain complexes at quasi-isomorphisms. Read their source signatures and documentation.
- def-pur-derived-internal-hom: Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses, CategoryTheory.derivedInternalHomOfUniverses. Read the full construction, comparison and representative-independence signatures/docstrings; it is the K-injective Hom-complex localization, with no freely chosen bifunctor.
- def-pur-localized-ringed-site: Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous, SheafOfModules.overFunctor, over, Hom.over, overMap, overFunctorMap; and Mathlib.CategoryTheory.Sites.Over, CategoryTheory.GrothendieckTopology.over and CategoryTheory.Sheaf.over. Read their actual source definitions and docstrings. The dependency record is completed below.
- def-weil-pbc-locally-derived-ringed-ideal-complete: Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete, CategoryTheory.IsLocallyDerivedRingedIdealComplete. Read its full definition: tests every local ideal section, using ringedDerivedRestriction, ringedSectionLocalization and derivedInternalHom. The existing ringedSiteDerived and ideal-presentation interfaces were also read in RingedDerivedRestriction and RingedIdealGenerators.
- def-weil-pbc-ringed-site-section-localization: Sheaf.CategoryTheory.RingedSiteLocalization, CategoryTheory.ringedSiteSectionLocalization. Read its telescope construction and compatibility theorem; no definition is copied here.

Proof imports include the available recorded modules Sheaf.Algebra.Homology.RingedInternalHomExactRestriction and Sheaf.Paper.EtaleDerivedScalarTensor, the latter publicly reexporting the general ring-sheaf change-of-rings interface. The proof-only lem-sf-ringed-localization-rhom-orthogonality has no recorded module on the read base, so there is no module to import; the proof docstring names its exact role. No new declaration is needed to type the item because this is only a proof dependency.

Edge cases checked against the source and definitions: K=0 and N=0 give zero derived Hom; the empty site leaves the universal completeness test vacuous for both input and output; I=0 tests localization at zero, which is the zero sheaf, and imposes no unintended condition; I=O includes the unit section, so completeness forces N=0, consistent with the conclusion. Zero coefficient rings are allowed. Arbitrary infinitely generated ideals and complexes unbounded in both directions remain admitted. No STATEMENT-DISPUTED remains.

Searches, all repeated for this repair:

- msearch.py leansearch: `Derived internal Hom into a locally derived ideal complete object on a ringed site is locally derived complete`. Eight hits: HasDerivedCategory.standard and ordinary IsAdicComplete/AdicCompletion infrastructure; no ringed-site derived-Hom completeness theorem.
- msearch.py leanfinder: the same query. Eight hits on sheaf differentials, condensed modules, local cohomology and sheaf abelian/quasicoherent structures; no matching theorem.
- msearch.py loogle: `AdicCompletion, LinearMap`. Twelve ordinary adic-completion maps and properties; no matching theorem.
- msearch.py grep across Mathlib: `derivedComplete|DerivedComplete|derived.complete|derived_complete`. No hits.
- rg in the upstream WeilConjectures source and the shared lean/Sheaf: `IsLocallyDerivedRingedIdealComplete|ringed.*[Cc]omplete|rhom.*[Cc]omplete`. The side library contains the predicate and its consumers, but no internal-Hom preservation statement. Upstream contains no matching theorem. grep of the item's blueprint id in upstream gives no hits.
- rg of the chosen declaration name in Mathlib, upstream, lean/Sheaf and dag/lean_names_upstream.json gives no collision.

## Dependency modules

`def-pur-localized-ringed-site`: its lean record was null although its mathlib_match already identified the exact Mathlib construction. Under §1(B), I supply an existing:true record for SheafOfModules.overFunctor and list the topology, sheaf, object, morphism and successive-restriction declarations. J.over U uses Sieve.overEquiv to obtain exactly the induced covering sieves; Sheaf.over is pullback along the slice forgetful functor; overFunctor acts on modules and morphisms by sectionwise restriction; overMap and overFunctorMap give relocalization and the sectionwise identity comparison. This requires no replacement module and introduces no duplicate definition. Only lean is changed, with an explanatory note.

## Second reading by NO

I performed a second pass myself with the node, source Tag 099A and complete Lean module open; no separate agent was started. This is the author's second reading, with the maintainer supplying the independent review.

I compared the full quantified statement, not only its title. C is small in u, O is commutative, and I with its monic inclusion is exactly an ideal subsheaf. The Mono binder expresses the subsheaf condition already present in the node; it imposes no additional mathematical condition. K and N belong to the full integer-indexed derived category, and hN asserts precisely the shared completeness predicate. The conclusion applies that same predicate, with the same O, I and ι, to the recorded derivedInternalHomOfUniverses evaluated at (op K,N). No other premise restricts K or N. All universes and term variables are explicitly declared, and there are no local notations, copied definitions or non-sorry proofs.

I checked that the old small-site derivedInternalHom inside the completeness predicate and the currently recorded derivedInternalHomOfUniverses in the conclusion are the respective established definitions, both constructed from the same Hom complex and K-injective replacement; representative independence makes their interpretation the same RHom. I did not replace the conclusion by an arbitrary bifunctor, an arbitrary map or an assumed isomorphism. The new declaration is only the requested theorem.

I re-read the localized-site dependency's entire informal statement against the existing Mathlib definitions: induced covers, restriction of ordinary sheaves and ring sheaves, module objects, module morphisms and successive localization are all covered by the listed declarations. The record repair does not restrict to schemes or topological spaces.

The concrete defects fixed from the return are the absent module, absent item lean record, absent localized-site binding, absent source/proof docstrings, absent worker and second-reading reports, and the unauthorized summary edit. The summary is preserved from current main, no stage-1 fields are changed, and the item statement needs no correction. The lean.statement was extracted verbatim from the theorem keyword up to :=.

Validation: scompile.py compiled the delivered module cleanly both as an isolated sandbox file (49.8 s) and under its library module name (56.0 s), within the unchanged 60-second per-file limit. Neither run reported an error or unexpected warning. A JSON comparison against current main found only lean changed on each of the two node files. A source scan found no line longer than 100 characters. Delivery preflight and the existing-declaration probes are run through deliver2.py.
