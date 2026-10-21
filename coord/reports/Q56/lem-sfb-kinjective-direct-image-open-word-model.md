## Worker report

The module `Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel` states the three
clauses of the node using the actual internal module categories and their existing
section-ring equivalences. Its namespace is
`AlgebraicGeometry.ProEtale.KInjectiveWords`. Every theorem proof is `sorry`;
the definitions have actual data. In particular the only chosen transformation is
chosen from a theorem giving its unique evaluation characterization.

Hypothesis and clause correspondence:

- The coefficient input is the existing unbundled condensed-ring encoding
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]`. It admits arbitrary commutative condensed rings, without a
  topological presentation. The public import reexports `Profinite.CondensedRing`.
- A scheme is `Scheme.{u}`; its site is the recorded `Scheme.ProEt.topology T`,
  with site objects in `u+1`, morphisms in `u`, and coefficients in `u+1`.
  `Modules Λ T` abbreviates precisely
  `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)`.
  This changes no universes or size convention.
- The given letters are `CondensedRing.lowerStar Λ a` and
  `CondensedRing.upperStar Λ j`, with `IsOpenImmersion j` explicitly supplied in
  `Word.restrict`. These are the supplied module functors, with their supplied
  adjunctions. The coefficient-isomorphism assumption is already an instance
  `isIso_condensedPullbackHom` for every morphism with these point-pulled
  coefficients. No additional premise or arbitrary coefficient identification is used.
- `Word` has empty words, single letters of both kinds, and finite composition
  with arbitrary parentheses. `Word.ordinary` interprets them on modules;
  `Word.derived` replaces pushforwards by `rightDerivedFunctor` and restrictions
  by the existing exact `mapDerivedCategory`. Quantification over all such words
  gives any finite collection with one and the same input resolution; it imposes
  no bound on its length and needs no choice of a resolution for each word.
- Clause (i), existence: `resolutions` quantifies over every unbounded cochain
  complex and gives a quasi-isomorphism to an `IsKInjective` complex.
  Preservation: `Word.preservesKInjectives` uses the existing
  `Functor.PreservesKInjectiveComplexes` predicate. Each one-letter word is
  included, as are all composites and the empty word.
- The section-ring assertion of (i) is rendered by `Word.sectionwise`, the
  canonical `Word.sectionComparison`, and `sectionwise_representatives`.
  The comparison is built from the existing unit-normalized lower/upper
  comparisons and functor associators/unitors. The theorem identifies
  K-injectivity and quasi-isomorphisms through the actual section-ring
  equivalence on complexes. Thus the resolution and word models are the same
  through the canonical comparisons, as the node's proof explicitly explains.
- Clause (ii), evaluations: `EvaluationNormalized` fixes exactly the inverse
  derived-unit evaluation for a direct image and `mapDerivedCategoryFactors`
  for an exact restriction. Its composition equation uses the two evaluations
  and the actual `mapHomologicalComplexCompIso` through `compositeEvaluation`.
  `evaluations_existsUnique` states existence and uniqueness of this entire
  family; `Word.evaluation` selects that uniquely specified family. Thus the
  choice determines all data up to equality, as required for a definition
  relying on a postponed theorem. It is not an arbitrary existence choice. `Word.resolutionEvaluation a` first
  applies the derived word to `Q(a)` and then evaluates at I. No monomorphism
  premise is imposed on a. The empty word uses the identity factorization,
  hence gives Q(a) under its canonical identification.
- `word_map_computation` states existence and uniqueness of the homotopy
  class t whose localized value is `(Qa)^{-1} ≫ h ≫ Qb`, using the recorded
  `kInjectiveResolutionHomTarget` to include the Q/Qh presentation isomorphisms.
  Its second conjunct is `e_a.inv ≫ w.derived.map h ≫ e_b.hom = Q(wt)`,
  with `kInjectiveHomotopyImage` giving degreewise application to the class.
  The order is Lean's left-to-right composition convention.
- `Word.transition` is `e_a.symm ≪≫ e_b`.
  `transition_computation_and_cocycle` states its image-of-u formula and the
  three-resolution cocycle. The required unique u is supplied by
  `word_map_computation` with h the identity. Transitions are isomorphisms
  by their actual `Iso` type.
- Clause (iii), `descent_existsUnique` gives a unique transformation between
  the actual derived words. `IsEvaluationLift` writes exactly
  `e_w,a.inv ≫ δ.app (QN) ≫ e_v,a.hom = Q(theta_I)` and requires it for
  **every** N, I, and K-injective quasi-isomorphism a. `Word.cell` selects
  this uniquely specified transformation; `cell_evaluation` records its
  normalization. This quantification states resolution independence.
- `homotopic_representatives` states independence under `Homotopy t t'`.
  Computation on a homotopy-category arrow in `word_map_computation` also
  ensures that the result depends only on its homotopy class.
- `Expression` contains arbitrary cells, identity transformations, vertical
  composition, input and output whiskering, associators and unitors in both
  directions. Its ordinary and derived interpretations use the corresponding
  actual functor operations. `word_diagram_descent` says the interpretation of
  every expression is the normalized descent of its ordinary transformation,
  that equal ordinary expressions give equal derived expressions, and that
  `IsIso θ` implies `IsIso (Word.cell Λ θ)`. This explicitly covers identities,
  composition, both whiskerings, finite diagram equalities, and all canonical
  associators, including words containing empty words.
- All complexes are indexed by Z and all derived categories are the unbounded
  `DerivedCategory`. There is no boundedness, constructibility, support, or
  exactness-of-direct-image premise.

Dependencies read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt` and `ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `coefficientRing`, `condensedRingObj`, and `condensedPullbackHom`, including
  its canonical invertibility instance.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `CondensedRing.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `openImmersionLowerShriek`, its exactness, and its specified adjunction to upperStar.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, read in full:
  its arbitrary-resolution universal pair is already recorded by
  `sk-def-sfb-derived-categories`. This module is reexported by the map-computation
  dependency. For the actual Grothendieck module categories the word uses the
  existing upstream universal pair `rightDerivedFunctor`, with
  `rightDerivedFunctorObjQIso` fixing its inverse-unit normalization; it does not
  introduce another derived functor.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, `CochainComplex.IsKInjective`;
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, `IsKInjective.Qh_map_bijective`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
  `InternalAbelianSheafModule.sectionModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`, the actual `ring`,
  `equivalence`, `lowerStar`, `upperStar`, `lowerComparison`, `upperComparison`,
  and `internal_module_operations_transport`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`,
  `CondensedRing.module_pullback_additive_exact`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`,
  `Adjunction.preservesKInjectiveComplexes` and the preservation class.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`,
  `Functor.kInjectiveDerivedMapComputation`, `kInjectiveResolutionHomTarget`, and
  `kInjectiveHomotopyImage`.

Source and edge cases:

I read Stacks `derived.tex` at `lemma-adjoint-preserve-K-injectives` (08BJ),
`lemma-K-injective-defined` (070Y), and their surrounding homotopy/localization
statements; `sites-cohomology.tex`, `section-unbounded` (07A5); and
`injectives.tex`, `theorem-K-injective-embedding-grothendieck` (079P).
Empty words have their canonical identity evaluation. Empty open immersions and
empty schemes are admitted without nonemptiness hypotheses. Zero and acyclic
complexes are admitted. Identity morphisms, all parenthesizations, noninvertible
cells, maps represented only in the derived category, and resolution maps that
are not monomorphisms are included. For a three-resolution transition the
orientation e_a^{-1}e_b followed by e_b^{-1}e_c cancels to e_a^{-1}e_c.
No statement correction or disputed mathematical assertion was needed.

Searches actually run via `msearch.py` for Q56 and this item:

- LeanFinder: “Finite words of sheaf direct images and open restrictions preserve
  K injectives and descend natural transformation diagrams to unbounded derived
  categories”. Eight hits, concerning locally injective maps and sheaf lifting;
  none state this theorem.
- Loogle: `"rightDerivedNatTrans", "mapDerivedCategory"`. Zero hits.
- Mathlib grep: `Word|word` in `Algebra/Homology/DerivedCategory`. Zero hits.
- LeanSearch: “K injective resolutions compute finite composites of direct images
  and open restrictions and all natural transformation pasting diagrams”. Eight
  hits, concerning ordinary injective resolutions and their K-injectivity;
  none state this theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `directImageOpenWord|DirectImageOpenWord`: no existing declaration.
- Broader `rg` searches of both project source roots for word and K-injective
  interfaces found the generic one-letter derivation/composition interfaces,
  `ExactDerivedTransformationPasting` (all letters exact, hence not applicable
  to these direct images), and a different compact-support word family.
  None defines this mixed-word construction or states its descent assertion.

## Second reading by Q56

I reread the node against the module after drafting, checking each clause above.
This is a worker cross-check; no separate agent was started, as the dispatch brief
forbids it, and the maintainer performs the independent review.
I checked the evaluation orientation against Lean's left-to-right composition,
the exact-induced interpretation for restriction letters, arbitrary-resolution
rather than monomorphic-resolution hypotheses, normalization of the chosen
transformation, empty-word unitors, and the two directions of whiskering.
The module retains the actual internal module categories and sectionwise
comparisons throughout. No new definition or dependency node is needed: the
helper declarations describe only the words, evaluations, and diagram expressions
already quantified in this item's own statement.

Validation: `scompile.py` compiled the whole module in the sandbox and under its
real module name, cleanly, in 36.6 s and 33.6 s respectively (60 s limit).
The temporary diagnostic prefix module was removed. All theorem proofs, including
the named additivity theorem used by the additive-functor instance, are postponed and carry this node’s source/proof docstrings.

Preflight repair: moved the postponed additivity proof to
`Word.ordinary_additive_of_letters`; the instance body is now a reference to that
named theorem. This keeps every definition/instance body free of `sorry`.
