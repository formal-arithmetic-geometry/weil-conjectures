## Worker report

The module `Sheaf.Paper.ExactPullbackTowerCounitComparison` states
`CategoryTheory.ExactPullbackTower.exists_unique_counit_comparison`, with `sorry` as its
only proof. It introduces no definitions and does not change the informal statement.

Hypotheses and their Lean rendering:

| Node hypothesis | Lean |
| --- | --- |
| Two small sites | `{C D : Type u} [SmallCategory C] [SmallCategory D]`, topologies `J`, `K` |
| Commutative ring sheaves R, S | `R : Sheaf J CommRingCat.{u}`, `S : Sheaf K CommRingCat.{u}` |
| Arbitrary ringed-topos morphism, with left exact inverse image, adjunction and structural ring map | `f : RingedToposMorphism ... S ... R`; this existing structure includes `inverse`, `direct`, `adj`, `leftExact`, `ringMap`, its ring identities and the induced module direct image |
| Actual module pullback G | `G : Modules R ⥤ Modules S` and `adj : G ⊣ f.modules`, the same characterization as the recorded diagram K-flat and normalized-evaluation dependencies; the induced direct image is fixed by f, so this specifies inverse image followed by extension of scalars, up to its canonical adjunction isomorphism |
| Additive exact F and specified m | `[F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]`, `m : G ≅ F` |
| Module sheaves | Existing `DerivedTowerPullback.Modules R`, transparently `ringedSiteModules` and hence Mathlib `SheafOfModules` |
| Unbounded derived categories and localizations | `DerivedCategory`, `DerivedCategory.Q`, with four separately bound `HasDerivedCategory` universes `wA`, `wB`, `wTA`, `wTB` |
| Strict inverse sequences, levelwise G, F, m | `ℕᵒᵖ ⥤ Modules R`, `(Functor.whiskeringRight ℕᵒᵖ ...).obj G/F`, and its `mapIso m`; natural level n represents positive level n+1 |
| Specified universal left-derived pairs | `L`, `Lt`, `ε`, `τ` with the two `IsLeftDerivedFunctor` instances at the corresponding `HomologicalComplex.quasiIso` properties |
| Computation on objectwise K-flat flat-term representatives | The exact resolving class already used by `DerivedTowerPullback.IsGoodTower R`; the existing ringed-topos K-flat replacement and universal-pair theorem supplies computation for these arbitrary universal pairs, so no new resolution choice or stronger hypothesis is imposed |
| Exact descended F and tower F, with ξ and Ξ | Mathlib `F.mapDerivedCategory` and the tower functor's `mapDerivedCategory`, with their specified `mapDerivedCategoryFactors.hom` |

Every asserted clause is retained:

| Node clause | Lean |
| --- | --- |
| Existence of natural isomorphisms e and E | Outer existential over `e : L ≅ F.mapDerivedCategory` and the analogous `E` |
| Ordinary equation ξ e = Q(m) ε for every P | First conjunct: `e.hom.app (Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P = ε.app P ≫ Q.map ((NatIso.mapHomologicalComplex m ...).hom.app P)` |
| Uniqueness of e with this equation | Second conjunct, quantified over every `e'` with precisely the same equation |
| Tower equation Ξ E = Q(mTow) τ for every M | Third conjunct, using the whiskering functor's `mapIso m` followed by `NatIso.mapHomologicalComplex` |
| Uniqueness of E with this equation | Fourth conjunct, quantified over every `E'` satisfying that equation |
| Both counits invertible on every complex | Fifth and sixth conjuncts: `∀ P, IsIso (ε.app P)` and `∀ M, IsIso (τ.app M)`; neither quantifier is restricted to computing representatives |
| Natural isomorphism v at each positive level | `∃ v : ∀ n : ℕ, Comparison ... L Lt n` |
| Counit normalization on every objectwise K-flat flat-term tower complex | `∀ n, IsNormalizedOn G L Lt ε τ (IsGoodTower R) n (v n)`; this existing predicate inserts `L.map` of the source evaluation factor and the target evaluation factor and degreewise evaluation identity, in exactly the directions required to type the displayed formula |
| Characterization of each v by that normalization | Pointwise uniqueness over every `v' : Comparison ... n` satisfying the identical predicate |
| Evaluation of E equals e followed by v on all derived towers | The next conjunct states `evD.map (E.hom.app N) ≫ (towerDerivedEvaluationInterchange F (op n)).hom.app N = (v n).hom.app N ≫ e.hom.app (evD.obj N)`, including the exact-localization identification required in the node |
| Every b≥a transition commutes | Final conjunct quantifies `a b : ℕ`, `h : a ≤ b`, every derived tower N; it is `v_b ≫ L.map d = d' ≫ v_a` using the dependency's canonical `derivedTransition` |
| No boundedness assumptions | Every complex has degree type ℤ; all four derived categories are unbounded, with no truncation or boundedness binder |

Dependency declarations read and used:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its existing localization tensor.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`, `NatTrans.ofOpSequence`;
  towers themselves are their target functor categories.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategory`,
  `Functor.mapDerivedCategoryFactors`, with the exact-functor instances.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: the recorded acyclic-total-tensor
  K-flat predicate; the existing normalized-evaluation dependency uses its common-universe
  specialization `CochainComplex.IsAcyclicTensorKFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`;
  the existing normalized-evaluation predicate uses the recorded flat-term specialization.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`:
  `Functor.leftDerived_from_resolvingClass` (public statement-dependency import).
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  particularly its induced `modules` functor. Its owning already-landed node
  `def-weil-pbc-ringed-topos-morphism` is added to stmt_deps.
- `Sheaf.Paper.DerivedTowerEvaluationNormalization`: `DerivedTowerPullback.Modules`,
  `Comparison`, `IsNormalizedOn`, `IsGoodTower`, `evaluationComplexIso`, `derivedTransition`,
  whose definitions are now owned by the new existing-definition node
  `def-sf-derived-tower-evaluation-normalization`. The theorem
  `exists_unique_normalized_evaluation` is used only by the retained proof plan; its node
  `lem-cbc-derived-tower-evaluation-normalization` remains in proof_deps only.
- `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`:
  `towerDerivedEvaluationInterchange`, plus its pointwise finite-limit and finite-colimit
  instances for the tower extension of an exact functor. Its already-landed owning node
  `def-sbc-tower-derived-evaluation-interchange` is cited in stmt_deps, replacing
  `lem-weil-pbc-tower-derived-evaluation-normalization`. The right-derived main theorem
  is not used by this statement or proof.
- The sole direct proof import is `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor` /
  `Functor.exactFunctor_derivedFunctor`, retained as the stated proof dependency required
  by stages/2-statements.md §3.7. Four redundant proof imports were removed: KanExtension.Basic,
  Abelian.FunctorCategory, Localization.Predicate and DiagramKFlatReplacements. Their
  ingredients remain available through the public dependencies of the existing owning modules.

The item retains its original eight stmt_deps and its proof, proof_deps and statement
verbatim. Added notions are cited through definition owners, including the existing
ringed-topos morphism node. No dependency module or duplicate declaration is introduced.

Edge cases checked by reading the actual equations and their factor types: zero complexes
and the zero ring; `F = G` and `m = Iso.refl G`; arbitrary nonidentity automorphism m
(the right hand sides explicitly contain m, so no identity normalization is silently
assumed); level 1 (`n = 0`); identity transition `a = b` and arbitrary composite transitions;
strict towers rather than independently selected derived objects; unbounded complexes.
No nonempty site, nonzero coefficient ring, boundedness, flatness of every module, or
exactness of the underlying tensor pullback is assumed independently of its specified
isomorphism to exact F. The ringed-topos and module interfaces use one chosen universe
for small sites and their coefficients, exactly as their recorded signatures do; the four
localization morphism universes remain independent.

Searches:

- `msearch.py ... leanfinder "exact module pullback universal left derived functor strict towers counit comparison evaluation"`:
  eight hits, including `Functor.totalLeftDerivedCounit`, its universal instance,
  `Adjunction.derived_counit` and `derived'_counit`; none supplies this simultaneous exact
  comparison, both universal counits, normalized evaluation and transition statement.
- `msearch.py ... loogle "CategoryTheory.Functor.mapDerivedCategoryFactors, CategoryTheory.Functor.rightKanExtensionUnique"`:
  zero hits for that combined query.
- `msearch.py ... grep "mapDerivedCategoryFactors|rightKanExtensionUnique" CategoryTheory`:
  seven hits, generic Kan-extension definitions and preservation; these are ingredients,
  not an existing declaration of the node.
- `rg` over Mathlib's ExactFunctor, FunctorCategory, OfSequence, KanExtension and Localization
  sources: read exact descent, tower abelianness, strict sequence construction and Kan
  uniqueness signatures/docstrings. `rg` in project `WeilConjectures/` and `Sheaf/` for
  `exactEvaluationIso|exists_unique_counit_comparison|lem-sf-exact-pullback-tower-counit-comparison`
  found no declaration of this item. Searches for tower comparison/exact tower material
  found the already-landed `towerDerivedEvaluationInterchange`; reused that declaration
  instead of defining an additional canonical map.

Sources checked locally: the current blueprint localization-all-stages file, the item's
retained four-step proof, and `literature/stacks-project/derived.tex` at
`lemma-right-derived-exact-functor` (015F) and `lemma-find-existence-computes` (06XN).
The former says every unbounded complex computes the derived exact functor; the latter
supplies the resolving-class computation and its left-derived dual. No source discrepancy
or STATEMENT-DISPUTED fault was found.

Verification: the prescribed scompile.py compiled the theorem cleanly in both sandbox
and library module modes, with no warnings. The only postponed theorem is the item's
named declaration, whose docstring contains its complete four-step proof plan.


## Repair of the independent return

The immutable reviewed head was 06b022261c90. The saved packet was first dry-run against
current main: OK, commit 20fc2143636 (not pushed). Its only differences from the current
main item were lean and stmt_deps. The requested repairs are substantive record changes:

- H2/H3, exact evaluation interchange: replaced the added theorem dependency
  lem-weil-pbc-tower-derived-evaluation-normalization by the already-landed
  def-sbc-tower-derived-evaluation-interchange (Q38, 2026-10-21). This owns the exact
  interchange and the two pointwise finite-preservation instances actually used.
- H2/H3, counit-normalization definitions: replaced the added statement dependency
  lem-cbc-derived-tower-evaluation-normalization by the new existing-definition owner
  def-sf-derived-tower-evaluation-normalization. Its six declarations are unchanged
  in the published module. The theorem node remains only in the original proof_deps.
- H9 advisory: removed four redundant direct proof imports. Kept the actual exact-functor
  proof dependency as required by the stage-2 import rule. The theorem signature and its
  docstring are unchanged, as the independent mathematical review requested.

## New nodes

`def-sf-derived-tower-evaluation-normalization` attaches, with existing: true, the six
plain declarations in `Sheaf.Paper.DerivedTowerEvaluationNormalization`:
Modules, evaluationComplexIso, derivedTransition, Comparison, IsNormalizedOn, IsGoodTower
(in namespace CategoryTheory.DerivedTowerPullback). Its primary signature is verbatim
IsNormalizedOn. This is definition ownership, with no new module and no new theorem.
The statement describes each existing definition: Modules is the same ringedSiteModules
category after forgetting commutativity; evaluationComplexIso is the degreewise identity;
derivedTransition localizes the ordinary unique tower arrow for every a≤b; Comparison
is the type of natural isomorphisms with the stated source and target; IsNormalizedOn
is exactly its displayed equation with the two evaluation localization factors; and
IsGoodTower is exactly pointwise IsAcyclicTensorKFlat and flatness of every term.
The definitions do not select data from the normalized-evaluation existence theorem.
The blueprint localization Step 6 and Stacks 06XN (dual), 05RU are the source, with the
strict-tower specialization spelled out in the existing module.

Searches made during this repair: LeanSearch for the normalization predicate returned
eight generic counit/derived-functor hits, including totalLeftDerivedCounit, derivedε,
leftDerivedNatIso and mapDerivedCategorySingleFunctor; Loogle for
CategoryTheory.Functor.mapDerivedCategoryFactors returned twelve exact-localization
hits, including the factor used here; msearch grep for
IsNormalizedOn|IsGoodTower|evaluationComplexIso|derivedTransition returned zero Mathlib
hits. The raw search summaries are recorded in the new node. Project and DAG rg searches
found precisely these six existing helpers, their theorem record and consumers, with no
separate definition owner; no matching declaration was found in WeilConjectures.
blueprint_refs.py search 'tower evaluation' returned zero blueprint nodes, and ancestor
returned prop-sf-localization-all-stages. Thus the existing code is reused with a new
DAG owner, as the independent reviewer requested.

## Second reading by Q22

Repair self-check (no additional agent was started): reread the item node, its entire
Lean declaration and the six existing helper definitions. The hypothesis and clause
mapping in Worker report still applies verbatim: arbitrary ringed-topos pullback, exact
F and specified m; independent universal ordinary and tower pairs; unique e and E with
the two counit equations; both counits invertible on every complex; unique normalized
v at each positive level; evaluation equation with the canonical interchange; and every
transition, including a=b, all in unbounded derived categories. No signature change was
needed or made. Checked the new node against each of its six declaration bodies: only
definitional constructions are recorded, with no existence or uniqueness claim. In
particular good is arbitrary in IsNormalizedOn, while IsGoodTower is the precise
K-flat flat-term class used by the item. The zero/identity and first-positive-level
edge cases listed above remain present, and no extra universe equality was introduced.
No STATEMENT-DISPUTED issue or statement correction is needed. All other item fields
are unchanged relative to current main; the two theorem-only added stmt_deps were
replaced by definition owners. Final compilation and delivery dry run are recorded below.

Final self-check: the repaired file compiled cleanly via scompile.py in sandbox mode
(3.2 s) and library mode (3.5 s). Recorded signatures were checked verbatim through
the declaration delimiter, preserving named-argument `:=` occurrences inside the types.
