## Worker report

The module `lean/Sheaf/CategoryTheory/FiniteColimitApproximation.lean` states
`SSet.Enhanced.finite_colimit_approximation`. Its sole theorem has proof `sorry`.
The natural-language statement, statement dependencies and proof plan are unchanged.
There are no new definition nodes or dependency repairs.

I checked the inherited sandbox module against the current node, dependency source,
Mathlib and the cited source. I added the newly available proof dependency import
`Sheaf.CategoryTheory.CoreKanFibration`, regenerated the node copy from the current
repository with only `lean` changed, and replaced the inherited report. The independent
second reading is left to the next worker.

Clause-by-clause match:

- The common sufficiently large universe is the explicit `universe u` and
  `(C D : SSet.{u})`. `[Quasicategory C]` and `[Quasicategory D]` are the stated
  quasicategories; `(F : C ⟶ D)` is the coherent functor, a simplicial map.
- Existence of all finite coherent colimits in C is `hC`: for every `K : SSet.{u}`
  and proof of `K.Finite`, every `H : K ⟶ C` has a vertex `c` of
  `coconeCategory H` satisfying `IsColimiting H c`. `hD` is the identical clause
  for D. Mathlib `SSet.Finite` means finitely many nondegenerate simplices,
  rather than a finite ordinary category or just finitely many vertices.
- Preservation of these colimits is `hF`. For each finite H and each colimiting
  cocone c, it requires a colimiting cocone d for `H ≫ F` with apex
  `d.1.1 = F.app _ c.1.1` and transformation
  `d.1.2 = ((ihom Δ[1]).map ((ihom K).map F)).app _ c.1.2`.
  These equalities fix precisely the image cocone, including its entire coherent
  cylinder; they impose no choice of a second comparison map.
- Conservativity is `hcon`: for each 1-simplex e of C, an equivalence witness for
  `F.app _ e` implies `IsEquivalenceEdge C e`. Preservation of equivalences is
  automatic for a simplicial map and is not an extra assumption.
- `happrox` quantifies over every vertex x of C, vertex y of D, and
  `ψ : SSet.Edge (F.app _ x) y`. Its witnesses are exactly x',
  `u : SSet.Edge x x'`, and `e : SSet.Edge y (F.app _ x')`.
  `IsEquivalenceEdge D e.edge` makes e an equivalence. The equation
  `homMk ψ.toTruncated ≫ homMk e.toTruncated = homMk (u.map F).toTruncated`
  says precisely `[e ψ] = [F(u)]` in hD. Lean composition is written in traversal
  order. It does not require a strict commuting triangle or a chosen 2-simplex.
- The conclusion `IsFunctorEquivalence F` supplies a coherent inverse simplicial
  map, with coherent natural equivalences of both composites with the identities.
  There is no fully faithful hypothesis.

The statement dependency `def-cbc-enhanced-diagrams-cones` is imported publicly
from `Sheaf.CategoryTheory.EnhancedDiagramsCones`. I read its definitions and
associated docstrings: `SSet.Enhanced.coconeCategory`, `IsColimiting`,
`IsInitial`, `IsContractible`, `mappingSpace`, `IsEquivalenceEdge`,
`AreNaturallyEquivalent` and `IsFunctorEquivalence`. Cocones are the specified
comma simplicial pullback, and colimiting means initial there. The universal
properties and coherent inverse are used directly, without duplicate definitions.
Mathlib's public imports are `Mathlib.AlgebraicTopology.SimplicialSet.Finite`
(`SSet.Finite`) and `Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat`
(`SSet.Truncated.HomotopyCategory.homMk`). I read the definition of the quotient
homotopy category, its triangle relation and `homMk_comp_homMk`: for a quasicategory
this is the edge presentation of the category with morphisms π₀ of mapping spaces.

The available proof dependencies are ordinary imports: `EnhancedFunctorConeCalculus`,
`KanFibrationFiberCriterion`, `RealizationCompactFiniteSupport`,
`HomotopyGroupsBasepointChange`, `CoreKanFibration`, `SliceArrowEquivalence`,
`JoinSliceRightFibration`, `JoinSliceDiagramIsomorphisms`,
`KanHomotopyPullbackInvariance`, `KanQuillenRightProper`, and `RealizationCylinder`
in their recorded Sheaf topic directories. The nine-step proof docstring follows
all nine steps of the node. The three proof nodes
`lem-cbc-left-fibration-equivalence-lift`, `lem-coef-infinity-full-essential-image`
and `lem-coef-join-slice-cocone-comparison` have no Lean record in the current DAG,
so there is no recorded module to import for them; their uses remain explicit in
the proof docstring. They are not prerequisites for typing this statement.

Edge cases checked: the empty finite simplicial set is included, so hC and hD
include initial objects and hF includes preservation of the empty colimit. Thus
neither empty quasicategory accidentally satisfies the finite-colimit assumptions.
The one-point quasicategory and finite shapes in every dimension are allowed;
identity and degenerate edges are admitted. Neither the diagram indexing shape
nor the approximation witnesses need to be nonempty beyond the stated conditions.
The single universe covers both quasicategories in any common enlargement and
introduces no independent smaller test universe. No characteristic or geometric
hypothesis is imposed.

Source reading: [Cisinski, Higher Categories and Homotopical Algebra]
(https://cisinski.app.uni-regensburg.de/CatLR.pdf), printed pp. 386–390,
Definition 7.6.1, Remark 7.6.2 and Theorem 7.6.10, read online on 2026-10-17.
The theorem assumes finite limits and their preservation and concludes equivalence
from right approximation. Taking opposites gives this node. With weak equivalences
the invertible edges, App 1 gives conservativity; App 2 gives the approximation
triangle. Inverting the dual equivalence puts e in the orientation in the node.
The homotopy-category equation expresses its commuting triangle. No additional
standing hypothesis is needed. No statement fault or dispute was found.

Searches rerun in this worker session (all recorded in `searches.jsonl`):

- `msearch.py ... leanfinder "A conservative functor between quasicategories
  preserving finite colimits with left approximation is an equivalence"`: eight
  hits, including `SSet.Truncated.HomotopyCategory.functorEquiv` and ordinary
  categorical/model localization results, none this criterion.
- `msearch.py ... loogle '"PreservesFiniteColimits", "IsEquivalence"'`: no hits.
- `msearch.py ... grep 'approximation|conservative' AlgebraicTopology/Quasicategory`:
  no hits.
- `msearch.py ... leansearch "A conservative functor preserving finite colimits
  satisfying the left approximation property is an equivalence of infinity
  categories"`: eight hits on ordinary exact functors and colimit preservation;
  no quasicategorical criterion.
- `rg` for `finite_colimit_approximation|FiniteColimitApproximation|finite.colimit.*
  approximation|approximation.*finite.colimit` in upstream `WeilConjectures/`,
  Mathlib, the shared `lean/Sheaf/`, and `dag/lean_names_upstream.json`: only the
  BrownLocalizationProducts proof comment refers to this item, no existing
  declaration. The upstream search for the exact DAG id also returned no hits.

Validation: the initial inherited module compiled cleanly through `scompile.py`.
The final module (including the added proof import) is checked again by the required
wrapper and delivery dry run. No global build or direct repository mutation is used.

## Second reading by Q63

I independently opened the current node copy at
`dag/nodes/sec-six-functors/lem-coef-finite-colimit-approximation.json`, its source place,
the dependency declaration in `Sheaf/CategoryTheory/EnhancedDiagramsCones.lean`, and the
module `lean/Sheaf/CategoryTheory/FiniteColimitApproximation.lean`. The item-by-item
matching is as follows.

- The objects are the common-universe simplicial sets `C D : SSet.{u}`, equipped with
  `[Quasicategory C]` and `[Quasicategory D]`, and the coherent functor `F : C ⟶ D`.
  These are exactly the node's quasicategories and functor; no extra category, ring,
  finiteness, characteristic, or universe-equality hypothesis is introduced.
- Finite coherent colimits in `C` and `D` are rendered by `hC` and `hD`: for every
  `K : SSet.{u}`, proof `_ : K.Finite`, and diagram `H : K ⟶ C` (respectively `D`),
  there is a cocone `c : (coconeCategory H) _⦋0⦌` with `IsColimiting H c`. The imported
  `SSet.Finite` is the node's finite-nondegenerate-simplex condition.
- Preservation is rendered by `hF`. Given the same finite `K`, `H`, and a colimiting
  cocone `c`, it supplies `d` over `H ≫ F`, with `d.1.1 = F.app _ c.1.1`, the exact
  transformed coherent edge `d.1.2 = ((ihom Δ[1]).map ((ihom K).map F)).app _ c.1.2`,
  and `IsColimiting (H ≫ F) d`. Thus it specifies the canonical image cocone and its
  universal property, exactly as the node's preservation clause.
- Conservativity is `hcon`: every edge `e : C _⦋1⦌` whose image
  `F.app _ e` is an `IsEquivalenceEdge D` is itself an `IsEquivalenceEdge C`. The
  converse required by Cisinski's App 1 is automatic for any simplicial map, so the
  Lean hypothesis is neither stronger nor weaker than the node's conservativity.
- Approximation is `happrox`: for every vertices `x`, `y` and edge
  `ψ : SSet.Edge (F.app _ x) y`, it gives `x'`, `u : SSet.Edge x x'`, and
  `e : SSet.Edge y (F.app _ x')`, with `IsEquivalenceEdge D e.edge` and
  `homMk ψ.toTruncated ≫ homMk e.toTruncated = homMk (u.map F).toTruncated`.
  Since composition is written in traversal order, this is exactly the node's equality
  that `F(u)` and `e ψ` represent the same morphism in `hD`; it imposes no strict
  triangle or chosen 2-simplex beyond the stated homotopy-category equality.
- The conclusion is `IsFunctorEquivalence F`, whose definition supplies a simplicial
  quasi-inverse and coherent natural equivalences in both composite directions. It is
  precisely the node's coherent functor equivalence and does not assume full faithfulness.

The source PDF was checked at Cisinski, *Higher Categories and Homotopical Algebra*,
Definition 7.6.1 (pp. 386--387) and Theorem 7.6.10 (pp. 389--390). The theorem assumes
finite limits and preservation, and right approximation with App 1; dualizing gives the
node's finite-colimit statement. The Lean `hcon` is sufficient for App 1 because functors
preserve the forward implication. The dependency's `coconeCategory`, `IsColimiting`,
`IsEquivalenceEdge`, `SSet.Truncated.HomotopyCategory.homMk`, and `IsFunctorEquivalence`
were read at their declarations; no private duplicate notion is used.

Edge cases were checked explicitly. `K = ∅` is admitted by `SSet.Finite`, so both
`hC` and `hD` include initial objects and `hF` includes preservation of the empty
colimit. One-point and higher-dimensional finite shapes are admitted. Zero and
degenerate edges are allowed, as are empty simplicial sets `C` or `D` subject to the
stated hypotheses. The single universe `u` is used consistently for all objects and
shapes, matching the node's common sufficiently large universe. No characteristic or
extra size restriction appears.

The existing-definition searches were reviewed in `searches.jsonl`: LeanFinder,
Loogle, LeanSearch, and Mathlib/project grep searches for the approximation criterion,
conservativity, and the exact declaration name found no existing declaration. The only
matching project reference is a proof comment in `BrownLocalizationProducts.lean`.
There were no mismatches, so no statement or dependency change was needed in this second
reading. The only inherited implementation adjustment is the already recorded import of
`Sheaf.CategoryTheory.CoreKanFibration`; it does not alter the theorem signature.
