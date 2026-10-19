## Worker report

Item: `lem-coef-simplicial-boundary-collapse-test`, group N8, stage 2.

The module `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest` states
`CategoryTheory.simplicial_boundary_collapse_test`, with its sole proof `sorry`.
No definitions, new nodes, dependency modules, or statement changes are needed.
Only the target node's `lean` field is changed. No repair note exists for the item.

Source checked: Hovey, *Model Categories*,
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf,
Proposition 3.2.2 (printed p. 79), Proposition 3.6.8 and its full horn induction
(printed p. 99), Definition 1.3.1 and Lemma 1.3.4 (printed pp. 13–14).
The source confirms the boundary generation, collapse criterion, and equivalent
right-adjoint characterization used here. The module docstring carries all seven
steps of the node's proof, naming the matching proof dependencies.

Hypotheses and clauses, matched individually:

- The arbitrary category is `{M : Type v} [Category.{w} M]`; the simplicial-set
  universe `u` is independent of both `v` and `w`. There is no equality restriction.
- `[ModelCategory M]` gives precisely the three morphism classes, two-out-of-three,
  retract closure, lifting and factorizations. Mathlib's weak-factorization-system
  instances in `ModelCategory.Basic` identify each class with the appropriate
  lifting class. The two `HasFunctorialFactorization` binders explicitly require
  functoriality for `(cofibrations, trivialFibrations)` and
  `(trivialCofibrations, fibrations)`, as the node requires.
- Completeness and cocompleteness are explicit `HasLimitsOfSize` and
  `HasColimitsOfSize` at `max u w`, covering both the simplicial-set small universe
  and M's hom universe. This gives the node's complete/cocomplete model category
  in a common universe, without identifying object and morphism universes.
- `V : SSet.{u} ⥤ M` is the given functor, and
  `[PreservesColimitsOfSize.{u, u} V]` states preservation of all small colimits
  of simplicial sets in universe u. Using an explicit size avoids the default
  `PreservesColimits V`, which instead selects M's hom universe w.
- `hboundary : ∀ n : ℕ, Cofibration (V.map (SSet.boundary.{u} n).ι)` is exactly
  the image boundary cofibration hypothesis in every nonnegative dimension.
- The first conjunct quantifies over every `f : X ⟶ Y` and takes `Mono f` to
  `Cofibration (V.map f)`. Mono is degreewise injectivity for simplicial sets,
  exactly the dependency's cofibration class.
- The second conjunct is an implication whose premise is `∀ n : ℕ,
  WeakEquivalence (V.map (SSet.stdSimplex.{u}.map
  (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)))`. This is the canonical simplex collapse
  induced by the unique order map to [0], with no arbitrary map substituted.
- Under that additional premise, the first output takes `Mono f` and
  `SSet.Enhanced.IsWeakHomotopyEquivalence f` to the conjunction of
  `Cofibration (V.map f)` and `WeakEquivalence (V.map f)`: trivial cofibration
  means both properties, exactly as in the node.
- Its next output quantifies over every weak homotopy equivalence f, with no
  monomorphism condition, and concludes `WeakEquivalence (V.map f)`.
- Its horn output quantifies over `n : ℕ` and `i : Fin (n + 2)` and applies V
  to `(SSet.horn.{u} (n + 1) i).ι`, concluding both cofibration and weak
  equivalence. The successor dimension expresses exactly all n ≥ 1 horns.
- Its final output quantifies over every `U : M ⥤ SSet.{u}` and every
  adjunction `_adj : V ⊣ U`. It states preservation of fibrations by U and
  preservation of trivial fibrations, the latter as boundary lifting
  `SSet.modelCategoryQuillen.I.rlp (U.map p)` for `trivialFibrations M p`.
  Hovey Lemma 1.3.4 identifies this with being a Quillen adjunction. It stays
  inside the collapse implication, as required. Expanding this characterization
  uses existing notions throughout and requires no new Quillen-adjunction
  predicate or definition node. No arbitrary model structure on simplicial
  sets or stronger adjunction hypothesis is introduced.

Dependency declarations and imports:

- Read the full recorded theorem signature and proof docstring of
  `SSet.KanQuillen.right_proper_kan_quillen` in
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, which is imported publicly.
  It fixes the model structure's three classes, using Mathlib's simplices,
  boundaries, horns, mono cofibrations and Kan fibrations, and the realization
  weak equivalences. Its `I.rlp` characterization is used in the last clause.
- `SSet.Enhanced.IsWeakHomotopyEquivalence` from the publicly available
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` is the dependency's definition:
  bijections of realization path components and positive homotopy groups at
  all basepoints. Its full definition and docstring were inspected.
- Read `SSet.stdSimplex`, `SSet.boundary`, `SSet.horn`, their canonical `.ι`,
  `SSet.modelCategoryQuillen.I/J`, and the definitions and signatures of
  `ModelCategory`, `PreservesColimitsOfSize`, `Cofibration`, `Fibration`,
  `WeakEquivalence`, and `trivialFibrations` in the pinned Mathlib sources.
- The stated proof dependencies are imported without `public`:
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`
  (`SSet.relativeCellComplexOfMono`),
  `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`
  (`llp_isStableUnderRetracts`, `llp_isStableUnderCobaseChange`,
  `llp_isMultiplicative`),
  `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`
  (`isStableUnderTransfiniteCompositionOfShape_llp`), and
  `Mathlib.AlgebraicTopology.ModelCategory.BrownLemma`
  (`CofibrantBrownFactorization` and its cofibrant nonemptiness instance).
  Their signatures and accompanying docstrings were read. The other proof
  dependency is already the public statement dependency.

Edge cases checked before the final statement:

- n = 0 boundary is empty (`SSet.boundary_zero`), so its image hypothesis is
  required; it is not dropped. The initial map gives cofibrancy of V(Δ[0]).
- n = 0 collapse is the identity (`SimplexCategory.const_eq_id`).
- Both dimension-one horns are vertices and are included by n = 0 in the
  successor-indexed horn clause. There is no assertion about dimension-zero
  horns (their empty-to-point maps would not generally be weak equivalences).
- Empty simplicial sets and arbitrary weak equivalences, including maps with
  empty source/target, are not excluded. Mono quantifiers include identities.
- Empty coproducts and zero-length cellular constructions are included in the
  proof description; the final statement has no nonemptiness assumption.
- No cofibrancy of objects of M, fibrancy of simplicial sets, enrichment,
  properness, small generation of M, or right adjoint is assumed for the first
  three preservation conclusions.

Searches made (N8/item wrapper queries):

1. `leanfinder`: "A colimit preserving functor from simplicial sets to a model
   category preserves cofibrations when boundaries do and preserves weak
   equivalences when simplex collapses do" — 8 hits, consisting of
   `SSet.modelCategoryQuillen.I`, its cofibration/fibration instances and
   class-identification lemmas. None states the criterion for arbitrary V.
2. `loogle`: `"SSet", "PreservesColimits"` — one hit:
   `SSet.Subcomplex.instPreservesColimitsOfShapeToSSetFunctorOfIsFilteredOrEmpty`.
   This is not the target statement.
3. `grep`: `boundary.*cofibration|collapse.*[Ww]eak|[Qq]uillen[Aa]djunction`
   — zero hits.
4. Earlier `leanfinder` query "Quillen adjunction left adjoint preserves
   cofibrations and trivial cofibrations" — model-category constructors,
   cofibration classes and Brown factorizations only; no Quillen predicate.
5. `rg` over upstream `WeilConjectures`, project `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for
   `simplicial_boundary_collapse_test|lem-coef-simplicial-boundary-collapse-test|boundary.*collapse|collapse.*boundary`
   — only the proof reference in `CosimplicialFrameMapping.lean`; no duplicate
   declaration. Additional searches for Quillen/colimit-preservation interfaces
   confirmed that the existing derived-adjunction module also uses the
   expanded preservation conditions rather than a Quillen predicate.

Validation: `scompile.py N8 lem-coef-simplicial-boundary-collapse-test
<module path>` compiled both the sandbox file and named library module cleanly
on 2026-10-16 UTC. All universes and variables are explicitly bound, with
`autoImplicit false`. There are no warnings and the only postponed proof is
this item's named theorem. The node's `lean.statement` is the exact signature
from the module. No statement dispute or node fault was found.

## Second reading by N8

I independently reread the node statement, Hovey's source, the recorded dependency,
and the Lean declaration. The item-by-item correspondence is as follows.

- The category is `M : Type v` with `Category.{w} M` and `ModelCategory M`; the
  explicit `HasLimitsOfSize` and `HasColimitsOfSize` at `max u w` render the
  complete and cocomplete hypotheses without identifying `v`, `w`, or the
  simplicial universe `u`. The two `HasFunctorialFactorization` binders render the
  two functorial weak factorization systems.
- `V : SSet.{u} ⥤ M` and `[PreservesColimitsOfSize.{u, u} V]` render the arbitrary
  colimit-preserving functor at the source universe. `hboundary` renders the
  boundary-image cofibration hypothesis for every `n : ℕ`, including `n = 0`.
- The first conclusion quantifies over every simplicial map and renders
  `Mono f -> Cofibration (V.map f)`, exactly the boundary-cell conclusion.
- The collapse premise is the canonical map
  `SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)` for each `n`, with no
  replacement by an arbitrary map. Under it, the first conclusion renders the
  mono weak-homotopy-equivalence case as the conjunction of cofibration and weak
  equivalence (the definition of trivial cofibration), the second renders the
  arbitrary weak-homotopy-equivalence case, and the third renders every
  positive-dimensional horn (`horn (n + 1) i`, `i : Fin (n + 2)`) as both a
  cofibration and a weak equivalence. This indexing covers both 1-horns at
  `n = 0` and makes no dimension-zero horn assertion.
- The final conclusion quantifies every `U : M ⥤ SSet.{u}` together with an
  adjunction `V ⊣ U`. Its two clauses say that `U` preserves fibrations and sends
  every `M` trivial fibration to `SSet.modelCategoryQuillen.I.rlp`; the recorded
  Kan--Quillen dependency identifies `I.rlp` with simplicial trivial fibrations,
  so this is exactly Hovey's right-adjoint/Quillen-adjunction characterization.

No mismatch was found. In particular, no extra finiteness, properness,
cofibrancy, fibrancy, enrichment, or nonemptiness assumption appears, and the
empty simplicial set, empty coproducts, zero object maps, `n = 0`, and arbitrary
universes allowed by the node remain covered. The statement's quantifier order
and implication nesting agree with the node. No repair was necessary.

For an independent existing-definition check, I ran `msearch.py` LeanFinder for
"simplicial boundary collapse test functor cofibration", Loogle for
"simplicial boundary collapse test" (no matching declaration), and `rg` for
`simplicial_boundary_collapse_test`, `BoundaryCollapseTest`, and boundary/collapse
variants over Mathlib, `WeilConjectures`, and `lean/Sheaf`. The only hits were
individual Mathlib boundary/cofibration declarations and the existing downstream
proof reference; none states this criterion. I also opened the Hovey PDF at
Propositions 3.2.2, 3.6.8, Definition 1.3.1, and Lemma 1.3.4 and found the
source hypotheses and conclusions represented above.

The worker module compiled cleanly with the required `scompile.py` invocation;
its `lean.statement` remains verbatim equal to the theorem signature. There are
no new definitions, dependency repairs, statement changes, or remaining
mismatches.
