## Worker report

The module `lean/Sheaf/AlgebraicTopology/KanWhiteheadInverse.lean` states
`SSet.Enhanced.kan_whitehead_inverse`. It introduces small simplicial sets `A` and `B`
with `[KanComplex A]` and `[KanComplex B]`, a simplicial map `f : A ⟶ B`, and the
hypothesis `hf : IsWeakHomotopyEquivalence f`. The latter is the recorded declaration
`SSet.Enhanced.IsWeakHomotopyEquivalence` from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; by its definition it says that geometric
realization induces a bijection on components and bijections on every positive based
homotopy group at every source basepoint.

The conclusion is an existential triple `(g, H, J)`: `g : B ⟶ A`,
`H : A ⊗ Δ[1] ⟶ A`, and `J : B ⊗ Δ[1] ⟶ B`. Here `⊗` is the existing degreewise
simplicial product and `Δ[1]` is Mathlib's standard simplex. The four conjuncts render
the four endpoint clauses exactly: `SSet.ι₀ ≫ H = f ≫ g`,
`SSet.ι₁ ≫ H = 𝟙 A`, `SSet.ι₀ ≫ J = g ≫ f`, and
`SSet.ι₁ ≫ J = 𝟙 B`. Thus both homotopies run from the relevant composite to the
identity, as in the node statement. No connectedness or nonemptiness hypothesis is
introduced.

The statement dependency used is `def-cbc-enhanced-diagrams-cones`, through
`SSet.Enhanced.IsWeakHomotopyEquivalence` in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its definition uses Mathlib's
`SSet`, `KanComplex`, `Δ[1]`, geometric realization, and the component and homotopy-group
maps, so no private notion is introduced. The stated proof dependencies are imported:
`SSet.fibration_pullbackObjObjπ` (Mathlib, node
`lem-cbc-internal-hom-fibration-corner-map`),
`SSet.Enhanced.simplicial_homotopy_equivalence_weak`
(`Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`),
`CompactlyGenerated.Serre.topological_serre_model`
(`Sheaf.AlgebraicTopology.TopologicalSerreModel`),
`SSet.kan_realization_serre` (`Sheaf.AlgebraicTopology.KanRealizationSerre`),
`SSet.realization_finite_limits` (`Sheaf.AlgebraicTopology.RealizationFiniteLimits`),
and the Mathlib declarations recorded for the trivial Kan fibration and its lifting
property. The additional new prerequisite `lem-cbc-kan-relative-realization-lift`
is a proof dependency only and is not restated here.

I checked the edge cases named by the source and node: empty `A` or `B` (the component
bijection forces both empty, with unique maps), disconnected Kan complexes, dimension
zero (the boundary is empty and the vertex clause remains meaningful), and the absence
of any chosen basepoint. The standard interval has distinct endpoint maps in every
simplicial degree. The endpoint equations remain well-typed for identity and composite
maps, and the theorem does not assume either complex is inhabited.

Searches made before writing the declaration were:

- `msearch.py ... leanfinder "simplicial homotopy inverse for weak equivalence between Kan complexes"`:
  returned abstract model-category homotopy-class Whitehead declarations, with no exact
  explicit-cylinder statement.
- `msearch.py ... loogle "HomotopicalAlgebra.LeftHomotopyClass.whitehead"`:
  returned `HomotopicalAlgebra.LeftHomotopyClass.whitehead`, which requires a
  `ModelCategory`, cofibrant/fibrant structures, and abstract homotopy relations rather
  than the required realization hypothesis and explicit `SSet.ι₀`, `SSet.ι₁` maps.
- `msearch.py ... leansearch "Whitehead theorem weak equivalence Kan complexes simplicial homotopy inverse"`:
  returned the same abstract model-category results and no exact match.
- `msearch.py ... grep "whitehead|weakEquivalence.*Kan|Kan.*weakEquivalence" AlgebraicTopology`:
  found `Mathlib.AlgebraicTopology.ModelCategory.Homotopy` and its abstract
  `LeftHomotopyClass.whitehead`/`RightHomotopyClass.whitehead`; it found no exact
  realization-based statement.
- `rg` over `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json` for
  `kan_whitehead_inverse`, `Whitehead`, and `whitehead` found no declaration matching
  this node. The nearby `WhiteheadCWHomotopyInverse` theorem concerns topological
  CW spaces and is a different statement.

No `STATEMENT-DISPUTED` issue or node fault was found. The module compiled cleanly with
`scompile.py`; the only permitted postponed proof is the theorem's `sorry`.


Continuation check (NC stage-2 worker, 2026-10-17): I reopened the current DAG node,
its statement dependency record, the dependency source module, and the sandbox theorem.
No repair note is present for this item. The sandbox node differs from the current base
only in `lean`; the theorem signature matches that record verbatim. All universe and
term variables are explicit, and `autoImplicit` is disabled. No Lean change was needed.

I read `componentsMap`, `homotopyGroupMap`, and `IsWeakHomotopyEquivalence` in the
recorded `Sheaf.CategoryTheory.EnhancedDiagramsCones` source. The first is the map on
path-component quotients; the second postcomposes based cubical representatives; the
third requires a component bijection and, for every positive degree and every source
realization point, bijectivity on based classes. Postcomposition preserves the group
operation, so this is exactly the node's isomorphism condition. Mathlib's `KanComplex`
is fibrancy for horn lifting in positive dimensions, including both outer horns and
without a dimension-zero existence axiom. Mathlib's `SSet.ι₀` and `SSet.ι₁` are defined
by pairing the identity with the constant zero and one interval vertices, respectively.
Consequently the displayed restrictions have the required orientation, without assuming
a simplicial interval reversal. The arbitrary universe `u` covers small simplicial sets
in any size convention permitted by the dependency.

Source verification: [Kerodon 00UB](https://kerodon.net/tag/00UB), Proposition the project server,
states the converse for both Kan complexes; [Kerodon 03X7](https://kerodon.net/tag/03X7),
Corollary the project server, identifies its weak equivalences with realization weak equivalences.
The proposition was recovered through the web search result after the direct page fetch
timed out. Neither source imposes connectedness or nonemptiness.

I reran `rg` for `kan_whitehead_inverse|Whitehead|whitehead` in upstream
`WeilConjectures/`, side `lean/Sheaf/`, and `dag/lean_names_upstream.json`, and the
item-id search in upstream `WeilConjectures/`. There is no exact existing declaration.
The nearby topological CW Whitehead theorem has a different domain and conclusion.
The previous machine-search outputs remain in sandbox `searches.jsonl`; I also reran
LeanFinder on the realization-based inverse and Loogle on
`SSet.Homotopy, SSet.KanComplex`. The abstract model-category Whitehead interface
requires a model structure not provided by the current simplicial-set API and does not
supply the realization hypothesis or the explicit interval homotopies in one specialization.

The required `scompile.py NC lem-cbc-kan-whitehead-inverse` check passed again,
compiling the sandbox and library-path versions without errors or warnings.
The independent second reading remains for the dispatcher's next worker.

## Second reading by NC

I read the current node `lem-cbc-kan-whitehead-inverse`, its source place, the
dependency node `def-cbc-enhanced-diagrams-cones`, and
`Sheaf.AlgebraicTopology.KanWhiteheadInverse` independently. The source place is
Kerodon Proposition the project server (Tag 00UB), whose Kan-complex converse gives a
homotopy inverse for a weak homotopy equivalence; Corollary the project server (Tag 03X7)
identifies the simplicial weak-equivalence convention with weak equivalence of
geometric realizations. The source imposes no connectedness or nonemptiness.

The node's objects, hypotheses, and conclusion match the Lean as follows.

1. “Small simplicial sets” are `A B : SSet.{u}` in the theorem binder; the single
   explicit universe `u` is the fixed small-simplicial-set universe. Verdict: exact.
2. “Kan complexes” is rendered by `[KanComplex A] [KanComplex B]`. Mathlib's
   `KanComplex` requires all horns in positive dimensions, including outer horns,
   and does not require a dimension-zero inhabitant. Verdict: exact.
3. The simplicial map `f : A → B` is rendered by `(f : A ⟶ B)`, using the
   simplicial-set category. Verdict: exact.
4. The realization hypothesis (bijection on path components and isomorphisms on
   every positive based homotopy group at every source realization point) is
   rendered by `(hf : IsWeakHomotopyEquivalence f)`. The dependency declaration
   `SSet.Enhanced.IsWeakHomotopyEquivalence` is the conjunction of bijectivity of
   `componentsMap` and, for every `r : ℕ` with `1 ≤ r` and every
   `x : SSet.toTop.obj A`, bijectivity of `homotopyGroupMap`; these are exactly
   the node's component and positive based-group clauses. Verdict: exact.
5. The existential simplicial inverse `g : B → A` is rendered by
   `∃ (g : B ⟶ A)`. Verdict: exact.
6. The first cylinder homotopy `H : A × Δ¹ → A` is rendered by
   `H : A ⊗ Δ[1] ⟶ A`, where `⊗` is Mathlib's degreewise simplicial product.
   Its endpoint equations are rendered in order by
   `SSet.ι₀ ≫ H = f ≫ g` and `SSet.ι₁ ≫ H = 𝟙 A`; categorical composition
   makes these the restrictions `gf` and `id_A` at endpoints 0 and 1. Verdict:
   exact, including orientation.
7. The second cylinder homotopy `J : B × Δ¹ → B` is rendered by
   `J : B ⊗ Δ[1] ⟶ B`, with
   `SSet.ι₀ ≫ J = g ≫ f` and `SSet.ι₁ ≫ J = 𝟙 B`; these are precisely `fg` and
   `id_B` at endpoints 0 and 1. Verdict: exact, including orientation.
8. The final sentence “Neither connectedness nor nonemptiness is required” is
   respected: there is no such hypothesis or instance in the theorem. Verdict:
   exact.

The empty edge case is included because `KanComplex` has no dimension-zero
inhabitedness requirement; if one complex is empty, the component bijection forces
the other realization to be empty and the unique maps satisfy the displayed
equations. Disconnected complexes are allowed because the hypothesis is quantified
over every source basepoint. The `r = 0` homotopy-group case is excluded exactly by
`1 ≤ r`, while the component map handles degree zero. The arbitrary universe `u`
covers every allowed small-simplicial-set size, and no characteristic or ring
assumption occurs. The interval is the standard `Δ[1]`; the endpoint inclusions
`SSet.ι₀` and `SSet.ι₁` have the required source and target types.

I searched Mathlib and the project with LeanFinder, LeanSearch, Loogle, and `rg`
for realization-based Whitehead inverses, Kan weak equivalences, and
`kan_whitehead_inverse`. Mathlib only provides the abstract model-category
`LeftHomotopyClass.whitehead`/`RightHomotopyClass.whitehead`, which require a
model-category interface and do not state this realization hypothesis or explicit
`Δ[1]` endpoint equations. No matching declaration occurs in the upstream
`WeilConjectures`, the repository's `lean/Sheaf`, or
`dag/lean_names_upstream.json`; the nearby topological CW Whitehead result is a
different notion. The recorded dependency declaration was opened directly and is
used rather than copied.

No mismatch was found, so no Lean or node field was changed. The node has no
`statement_change` and no repair note. The module has one postponed theorem proof,
with the source and `(blueprint: lem-cbc-kan-whitehead-inverse)` in both module and
declaration docstrings, and no hollow definition. The required
`scompile.py NC lem-cbc-kan-whitehead-inverse` check compiled the sandbox and
library-path files successfully with no errors or warnings.
