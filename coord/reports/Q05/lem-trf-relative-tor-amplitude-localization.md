## Worker report

The module Sheaf.Algebra.Homology.RelativeTorAmplitudeLocalization states
CochainComplex.relative_tensor_homology_vanish_iff_prime_localizations, with its only proof
`by sorry`. It states exactly conditions (1) and (2) of Stacks Tag 0B67 after renaming
the source's base A to R and its algebra B to A. The source was read in
literature/stacks-project/more-algebra.tex, lemma-tor-amplitude-localization, lines 17183–17208.
The node's statement, proof and dependency fields are unchanged; only `lean` is added.
No new definition or dependency module is needed.

Hypotheses and clauses, in order:

- Commutative rings and their homomorphism: `{R A : Type u} [CommRing R] [CommRing A]`
  and `(φ : R →+* A)`. There is no flatness, injectivity, finiteness, or nonzero assumption.
- Arbitrary complex of A-modules: `(K : CochainComplex (ModuleCat.{u} A) ℤ)` with no
  strict or cohomological bounds and no condition on its terms.
- Integers a ≤ b: `(a b : ℤ) (hab : a ≤ b)`.
- Chosen unbounded derived categories: `[HasDerivedCategory.{w} (ModuleCat.{u} R)]` and
  the dependent family of the same instances over `Localization.AtPrime (q.asIdeal.comap φ)`.
  These are localization choices, not mathematical restrictions. The ambient universe u
  contains the rings, the complex terms, and all test modules; w is independent.
  Any given collection of rings and modules can be put in this common ambient universe.
- The original relative complex is `((ModuleCat.restrictScalars φ).mapHomologicalComplex
  (.up ℤ)).obj K`, so its tensor base really is R, not A.
- Condition (1) is the left side of `↔`: `∀ (N : ModuleCat.{u} R) (i : ℤ)`, followed by
  `(i < a ∨ b < i) → IsZero ...`. N is put in degree zero by
  `(DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N`. The tensor is `⊗` in
  `DerivedCategory (ModuleCat.{u} R)`; `DerivedCategory.homologyFunctor ... i` and
  `IsZero` express exactly H^i = 0.
- Every prime of A is quantified as `q : PrimeSpectrum A`; contraction p is literally
  `q.asIdeal.comap φ`. There is no maximal-prime restriction.
- Termwise localization K_q is obtained by applying
  `ModuleCat.localizedModuleFunctor q.asIdeal.primeCompl` through
  `mapHomologicalComplex (.up ℤ)`. This is the existing exact functor built from the
  recorded `LocalizedModule`, using its canonical size-equivalent `Shrink`.
- Scalars are restricted along the actual canonical homomorphism
  `Localization.localRingHom (q.asIdeal.comap φ) q.asIdeal φ rfl`.
  Its fraction formula is r/t ↦ φ(r)/φ(t), as localRingHom_mk' confirms.
  Composition with `ModuleCat.restrictScalars` precedes `mapHomologicalComplex`,
  so both the terms and differentials have precisely this R_p-action.
- Condition (2) is the right side: for every q and every
  `L : ModuleCat.{u} (Localization.AtPrime (q.asIdeal.comap φ))`, and every degree
  outside [a,b], the displayed cohomology is zero. L is again placed in degree zero,
  and this tensor belongs to D(R_p), not D(A_q).
- The equivalence sign asserts both implications and adds no further conclusions.

Dependency declarations read and used:

- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q`; its cohomology is
  `DerivedCategory.homologyFunctor` from HomologySequence.lean.
- def-pc-module-kflat-complex:
  WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat,
  `CategoryTheory.MorphismProperty.kFlat`. The tensor on the derived category is the
  existing K-flat derived monoidal structure, imported through FlatModel and
  HasMonoidalDerivedCategory. No K-flat hypothesis is imposed on K itself.
- def-weil-pbc-module-localization: Mathlib.Algebra.Module.LocalizedModule.Basic,
  `LocalizedModule`, used through `ModuleCat.localizedModuleFunctor` in
  Mathlib.Algebra.Category.ModuleCat.Localization; its full implementation and
  docstrings were read, including its Shrink model and exactness instances.
- Proof dependencies with recorded modules are imported: FlatModel supplies
  `CochainComplex.exists_quasiIso_flat_kFlat` and
  `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft`; KFlatModuleBaseChange supplies
  `CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat`;
  BifunctorShift supplies `CochainComplex.mapBifunctor` through the tensor machinery;
  LocalizedModule.Exact supplies `LocalizedModule.map_exact` through Localization;
  ShortComplex.PreservesHomology supplies `CategoryTheory.Functor.homologyFunctorIso`;
  Ideal.Maximal supplies `Ideal.exists_le_maximal`. The theorem docstring carries
  all seven steps of the node's proof, including its two-resolution argument,
  explicit fraction comparison, omitted forward implication, and annihilator argument.

Edge cases checked against the source and the expanded proof:

- A is the zero ring: PrimeSpectrum A is empty, so (2) is vacuous; every A-module,
  including each term of K, is zero, so (1) holds. No `Nontrivial` binder is present.
- R is the zero ring: a unital ring map forces A to be zero too; both sides hold.
- Zero complex and zero test module: all displayed cohomology objects are zero.
- a = b: precisely degrees i < a or a < i are excluded; negative integers are allowed.
- Identity map: the displayed canonical map is the usual local-ring identity, so the
  statement specializes to the standard prime-local criterion.
- Nonflat maps and unbounded complexes are retained. The proof resolves over R and
  over R_p, and never treats an A-K-flat complex as R-K-flat.

Searches for an existing statement (performed before writing):

- msearch.py leanfinder: “Relative Tor amplitude of an unbounded complex is detected by
  localization at all primes of an algebra and their contracted base primes”. Eight hits:
  DerivedCategory.isGE_Q_obj_iff, isLE_Q_obj_iff, related instances and isGE/isLE_iff.
  They express cohomological bounds only, not this relative localization equivalence.
- msearch.py loogle: `ModuleCat.restrictScalars, Localization.localRingHom`: zero hits.
- msearch.py leansearch: “Tor amplitude of a complex is detected at all prime localizations”.
  Eight hits including LocalizedModule.AtPrime, RingHom.OfLocalizationPrime,
  OfLocalizationMaximal and Module.support; none states the derived equivalence.
- msearch.py grep: `torAmplitude|TorAmplitude|Tor.*localiz`, subdirectory Algebra:
  ordinary module localization and categorical localization hits, no relative theorem.
- rg over upstream WeilConjectures and project lean/Sheaf for
  `torAmplitude|TorAmplitude|relativeTor|relative_tor`: existing generic absolute
  DerivedCategory.torAmplitudeIn, scheme relative Tor predicates, and bounded-model
  theorems; no relative prime-localization equivalence. Read the full definition of
  DerivedCategory.torAmplitudeIn and used the same existing derived tensor directly,
  rather than introducing a second amplitude predicate.
- rg upstream for `torAmplitude.*[Ll]ocal|[Ll]ocal.*torAmplitude`: no matching statement.
- grep -rn of the item's blueprint id in WeilConjectures: no hits.
- rg for the proposed theorem name in Mathlib, upstream, lean/Sheaf and
  dag/lean_names_upstream.json: no hits.

Validation: scompile.py compiled the sandbox and final module separately, both cleanly,
within the 60-second file limit (2.2 and 2.4 seconds). An initial exploratory choice of
independent ring/module universes could not synthesize the upstream derived monoidal
instance, whose flat-resolution instance uses one ambient universe; the final statement
uses that ordinary common ambient convention and independently quantifies w. No new
hypothesis or typeclass obligation concerning flatness was added.
No statement dispute or node correction was found.

## Second reading by Q05

This is the worker's own second pass, not an independent review; the maintainer performs
the independent review. Reopened the complete node and the final Lean signature, and
matched each clause above. The left tensor is over R after φ-restriction; the right
first localizes at the A-prime, then restricts through the canonical R_p → A_q map.
Both test modules are arbitrary over the stated base and are placed in degree zero.
Both vanishings use the same two strict inequalities and the same a,b; the quantifier
ranges over all primes. No term-flatness, finiteness or boundedness binder is present.
All universes and variables are explicit. Each postponed proof is the single named
theorem, with the source and seven-step proof in its docstring. No new node, dependency
repair or statement correction needed a second check. This pass found no mismatch
and made no changes.
