## Worker report

The module `Sheaf.CategoryTheory.DerivedCoefficientSequenceRealization` renders the
whole node as the scalar-realization construction together with its normalization,
finite-chain coherence, naturality and componentwise inverse statements. The namespace
is `CategoryTheory.DerivedCoefficientSequence`. Every new theorem has proof `sorry`
and a source and natural-language proof in its docstring. Definitions have actual data.
The ordinary compositor is selected from an existence-and-uniqueness theorem which
specifies its hom as the identity on every underlying section; its isomorphism is
therefore determined, rather than chosen from an unconstrained Nonempty.

The previous sandbox contained only dispatcher marker files. There was no Lean module,
node copy or report to repair. The current node is stage-1 split/reviewed by Q149 and
has no Lean record. This delivery adds the stage-2 record and module, without changing
the statement, dependencies or split proof. There is no repair-notes file or NZ return
entry for this item in the supplied read clone.

Hypotheses and clauses, in the order of the node:

- A small site is presented by `C : Type u`, `[Category.{v} C]` and
  `J : GrothendieckTopology C`. The sheafification and locally-bijective instances in
  the Scalars and Realization sections are the existing Mathlib hypotheses for the
  abelian module category; on a site small in the coefficient/module universe they
  hold. Object and morphism universes of the site remain independent. No equality of
  site universes is imposed. The covering-site dependency is imported; this construction
  uses its associated Grothendieck topology and does not depend on a chosen coverage.
- `R : Sheaf J CommRingCat.{r}` and `B : ℕ → Sheaf J CommRingCat.{r}` are the ring
  sheaves. As in the recorded inverse-system convention, Lean index `n` labels the
  positive level `n+1`. Thus `q : ∀ n, B (n+1) ⟶ B n`, `π : ∀ n, R ⟶ B n`, and
  `hπ : ∀ n, π (n+1) ≫ q n = π n` are exactly the maps and compatibility in the node.
- `Modules` transparently uses `CategoryTheory.ringedSiteModules` of the existing
  ring-sheaf presentation, forgetting commutativity by Mathlib `sheafCompose`.
  `[HasDerivedCategory.{w} (Modules R)]` and the levelwise analogous instances specify
  the chosen morphism universe for the ordinary unbounded derived categories.
- `restriction f` is precisely `SheafOfModules.restrictScalars` on the underlying ring
  morphism. The exactness instances are projections of the already recorded
  `SheafOfModules.sheafRingCoefficientOrdinaryAdjunction`, not new exactness claims.
  `derivedRestriction f` is its `Functor.mapDerivedCategory`, with the existing
  `mapDerivedCategoryFactors` comparison to termwise restriction on complexes.
  In particular `derivedRestriction (q n)` is S_n and `derivedRestriction (π n)` is Q_n.
- `existsUnique_ordinaryComparison` states the identity-on-sections normalization.
  The scalar action on its source is through `f ≫ g`; `hfg` identifies it with the
  action on its target. Its docstring gives the sectionwise action calculation.
  `ordinaryComparison` retains that unique normalization. `comparison` composes
  the canonical derived-functor compositor with the localized ordinary isomorphism;
  `comparison (π (n+1)) (q n) (π n) (hπ n)` is γ_n.
- `comparison_localized` states the normalization of γ after cochain localization,
  including the factorization isomorphisms on both sides. It applies to every complex,
  in every degree and on every section via the ordinary comparison's normalization.
- `chainMap B q n k` is the coefficient composite B_(n+k) → B_n, recursively the
  identity for k=0 and q_(n+k) followed by the shorter composite for k+1.
  `projection_chain` includes `hπ` explicitly and states compatibility with π_n.
  `iteratedRestriction` and `iteratedComparison` are actual recursive constructions,
  with identity functor and unitor for length zero. `chainComparison` compares the
  iterated S_i with direct scalar restriction. `finite_comparison` says that direct
  γ equals the iterated adjacent γ_i, including length zero. `comparison_assoc`
  states the compositor equality for any three composable coefficient maps and all
  specified composites, so every intermediate cut is covered. Its proof docstring
  explains the localization uniqueness argument. `derivedIdentity` is the canonical
  identification of restriction along an identity with the identity derived functor.
- `Sequence D S` has exactly the objects M_n and arrows d_n in the node.
  `Sequence.Hom` has exactly a_n and
  `M.transition n ≫ (S n).map (app n) = app (n+1) ≫ N.transition n`, which is the
  displayed semilinear equation written in Lean's left-to-right composition order.
  `sequenceCategory` gives the componentwise identities and composition, with the
  componentwise category laws. Its generic category parameters are specialized to
  the individual derived categories by the main construction.
- `step Q γ M n` is `Q_(n+1)(d_n) ≫ γ_n(M_n)`.
  `tower Q γ M` is Mathlib `Functor.ofOpSequence` with levels `Q_n(M_n)` and these
  steps. Its longer maps are precisely finite composites and its length-zero maps
  identities, by the existing sequence constructor's category laws.
- `step_naturality` is exactly `t_n^M ≫ Q_n(a_n) = Q_(n+1)(a_(n+1)) ≫ t_n^N`.
  `towerMap` uses `NatTrans.ofOpSequence`, with components `Q_n(a_n)` and this
  consecutive equation. Naturality for longer transitions follows from that constructor.
  `realization` packages these object and arrow operations as a functor and supplies
  componentwise identity and composition laws. `derivedCoefficientSequenceRealization`
  is its actual specialization to the node's coefficient maps and canonical γ_n.
- Under `[∀ n, IsIso (a.app n)]`, `inverse_step` states exactly the node's inverse
  compatibility equation, in Lean composition order.
  `realization_isIso` asserts an inverse tower arrow with components
  `Q_n(inv(a_n))` and explicitly states both composite identities. Thus it also gives
  the asserted isomorphism, without strengthening the hypotheses to an assumed tower
  isomorphism or a simultaneous representative.
- Every sequence object and morphism lives directly in its individual derived category.
  No flatness, completeness, boundedness or representative-selection hypothesis occurs.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; Mathlib `GrothendieckTopology` is
  the associated topology used here (no coverage-specific calculation is needed).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation of the Mathlib module-sheaf category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` and its additive instance.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`.
- `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`:
  `SheafOfModules.sheafRingCoefficientOrdinaryAdjunction` supplies both exactness instances.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`.
- `Mathlib.CategoryTheory.Localization.Predicate`: `Localization.liftNatIso` and
  `Localization.natTrans_ext` underlie the comparison and its stated coherence proof.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryCompIso`, `Functor.mapDerivedCategoryNatIso`, and
  `Functor.mapDerivedCategoryIdIso` construct the canonical comparisons.

Edge cases checked against the types and definitions: the first positive level is
Lean index 0; zero-length coefficient chains have identity maps; iterated comparisons
use the unitor in that case and `finite_comparison` includes k=0. Identity coefficient
maps are allowed. Zero modules, zero ring sheaves and the empty site are not excluded.
Non-flat maps such as ℤ/4 → ℤ/2 satisfy every required condition. Objects need not be
bounded and arrows need not lift to any single common sequence of complexes. Universal
quantification in `comparison_assoc` permits every intermediate cut, including identity
maps and repeated levels. The inverse theorem only assumes individual level arrows
are invertible. Universe variables are all declared and `autoImplicit` is false.

Searches before writing:

- `msearch.py ... leanfinder`: “Restriction of scalars for compatible towers of ring
  sheaves induces coherent functors on unbounded derived categories and realizes varying
  coefficient derived sequences as inverse systems”. Eight hits included
  `Functor.instLinearDerivedCategoryMapDerivedCategory`, local cohomology diagrams and
  condensed-module declarations. None states this varying-ring realization.
- `msearch.py ... loogle`: `"restrictScalars", "comp"`. Twelve hits include
  `ModuleCat.restrictScalarsComp`, `ModuleCat.restrictScalarsComp'` and their sectionwise
  components. These concern ordinary modules over rings, not ring-sheaf derived sequences.
- `msearch.py ... grep`: `restrictScalarsComp|mapDerivedCategoryNatIso|ofOpSequence`
  in `Algebra/Category/ModuleCat/Sheaf`: two hits in PushforwardContinuous, both ordinary
  coefficient calculations. No exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for scalar compositors,
  `ofOpSequence`, derived coefficient sequences and the proposed main name. The relevant
  existing exact-functor comparison API is reused. Existing constant-coefficient tower
  strictification (`DerivedCategory/Complete/NormalizedTower`) chooses complex models
  for a different theorem and is not this varying-ring sheaf realization. No declaration
  matched `DerivedCoefficientSequence` or `derivedCoefficientSequenceRealization`.
- Search of `lean/WeilConjectures` for the item id returned no result.

Sources opened: the ancestor blueprint integral compact-support formula; Stacks
`categories.tex`, definition-system-over-poset (0030) and properties-left-localization
(04VG); `sites-modules.tex`, lemma-abelian (03DA); `derived.tex`,
lemma-right-derived-exact-functor (015F). The node explicitly labels the varying-category
construction as an agent-written extraction; the report does not attribute it to 0030.

Validation: server compilation through `scompile.py`, in module mode, passed in both
sandbox and library-name modes. The module has no overlong lines and no unbound implicit
parameters. Every postponed theorem belongs to this node's own clauses and has its source
and proof in its docstring. No statement correction, dependency repair or new node is needed.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
