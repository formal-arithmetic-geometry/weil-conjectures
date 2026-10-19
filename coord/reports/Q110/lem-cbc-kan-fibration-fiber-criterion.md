## Worker report

The module `Sheaf.AlgebraicTopology.KanFibrationFiberCriterion` states
`SSet.Enhanced.kan_fibration_fiber_criterion`, with one `sorry`. Four real helper
constructions in the same module supply the mapping-path object and its canonical
maps; no other DAG theorem is restated. The helpers belong to this item's explicitly
specified mapping-path construction. No statement correction, new node, dependency
repair, or disputed statement is needed.

Clause-by-clause correspondence:

- Simplicial sets are `SSet.{u}`, for an explicitly bound arbitrary universe `u`.
  All simplicial maps are natural transformations in that category.
- A Kan fibration `p : X ⟶ Y` is the hypothesis `Fibration p`, under Mathlib's
  `SSet.modelCategoryQuillen` scope. Its defining morphism property is `J.rlp`:
  `J` contains every horn in positive dimension, including both outer horns.
  There is no Kan hypothesis on `X` or `Y` in this part of the statement.
- Weak homotopy equivalence is precisely the dependency's
  `SSet.Enhanced.IsWeakHomotopyEquivalence p`: path components and all positive
  based homotopy groups of geometric realization.
- Trivial Kan fibration is `modelCategoryQuillen.I.rlp p`, where `I` is exactly
  the family of boundary inclusions in every dimension, starting at zero.
  `SSet.boundary` is the non-surjective-simplex subcomplex;
  `boundary_eq_iSup` identifies it with the union of faces, and
  `boundary_zero` identifies the zero-dimensional boundary with the empty object.
- The two equivalences in the first conjunct connect the three asserted
  properties. Every vertex fiber is
  `pullback (SSet.const (X := Δ[0]) y) p`, the strict simplicial pullback over
  the vertex `y`. The clause requires both `KanComplex` and `IsContractible`.
- For `f : A ⟶ B`, `[KanComplex A] [KanComplex B]` render exactly the stated
  map-of-Kan-complexes hypothesis, without a nonemptiness condition.
- `mappingPathSubcomplex f` consists degreewise of pairs `(a, path)` satisfying
  `evaluation ... 0 path = f a`. It is a subcomplex of
  `A ⊗ (ihom Δ[1]).obj B`. The operators restrict the product operators, so its
  `toSSet`, named `mappingPath f`, is the displayed degreewise pullback.
- `mappingPathProjection f` is inclusion into the product, projection to the
  internal hom, and the dependency's evaluation at vertex 1. Its `Fibration`
  clause is exactly the asserted mapping-path fibration.
- `mappingPathInclusion f` sends each simplex `a` to
  `(a, constantDiagrams Δ[1] B (f a))`. Its actual endpoint equation follows
  from currying and the unit isomorphism; no data or structural proof is `sorry`.
  `IsWeakHomotopyEquivalence (mappingPathInclusion f)` is the next clause.
- The final equivalence is `IsWeakHomotopyEquivalence f ↔ ∀ b, IsContractible
  (homotopyFiber f b)`, using the dependency's exact path-pullback model.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsWeakHomotopyEquivalence`,
  `IsContractible`, `evaluation`, `constantDiagrams`, and `homotopyFiber` in
  namespace `SSet.Enhanced`. Read their complete signatures and docstrings,
  and the comma-subcomplex definition underlying `homotopyFiber`.
- Mathlib `AlgebraicTopology.SimplicialSet.CategoryWithFibrations`: `I`, `J`,
  the scoped fibration structure, and `fibration_iff`.
- Mathlib `AlgebraicTopology.SimplicialSet.Boundary`: `boundary`,
  `boundary_eq_iSup`, and `boundary_zero`; Mathlib's existing `KanComplex`,
  simplicial internal hom, and categorical pullbacks supply the other notions.

Edge cases checked: the boundary condition includes `n = 0`, forcing surjectivity
on vertices. Horn conditions begin in dimension one and include both endpoints.
Empty Kan complexes are allowed. For an empty base, the universal fiber condition
is vacuous and the map has empty source, consistently giving a weak equivalence.
For a nonempty base an empty fiber is not contractible, because the dependency's
component bijection to the point fails. No basepoint is imposed when a source or
target is empty. The first clause works for non-Kan bases, as Kerodon 00ZP explicitly
states. All objects use the arbitrary common small simplicial-set universe, with
no universe ceiling or extra equality.

Searches for existing declarations:

- `msearch.py` LeanFinder: “A Kan fibration is a weak homotopy equivalence if and
  only if all its fibers are contractible; mapping path replacement of Kan
  complexes” returned eight generic model-category bifibrant/path-object and
  Whitehead results. None states this realization-based criterion and explicit
  simplicial mapping-path construction.
- `msearch.py` Loogle: `SSet.modelCategoryQuillen.fibration_iff,
  SSet.modelCategoryQuillen.I, SSet.KanComplex` returned zero hits.
- `msearch.py` grep of Mathlib/AlgebraicTopology:
  `contractib.*fib|fib.*contractib|mappingPath|WeakHomotopyEquivalence` returned
  zero hits. Direct reading verified the horn and boundary APIs above.
- `msearch.py` LeanSearch: “A Kan fibration is a weak homotopy equivalence exactly
  when its vertex fibers are contractible Kan complexes and exactly when it
  lifts simplex boundaries” returned the fibration structure and generic
  trivial-fibration lemmas, not the geometric statement.
- `rg` of upstream `WeilConjectures` and `lean/Sheaf` for
  `kan_fibration_fiber|mappingPath|contractib.*fib|fib.*contractib`, plus
  `grep -rn` for this node id in upstream, found no exact statement.
  `dag/lean_names_upstream.json` has no matching name. The side library contains
  `ContractibleHomotopyFiberEquivalence`, which states only the final clause;
  `KanQuillenRightProper` contains related model-structure assertions, while
  `RightFibrationContractibleFibers` proves a different lifting criterion and
  cites this item. All three files were read. None is an exact match, and none
  is imported to avoid a circular proof dependency.

Source checked: Kerodon Proposition the project server,
<https://kerodon.net/tag/00ZP>, explicitly permits arbitrary simplicial bases and
includes the three equivalent conditions used here. The mapping-path part is the
node's specified expansion, using the endpoint path-space fibration and interval
contraction, not an additional numbered quotation. The theorem docstring records
this proof plan in full. The node has no proof dependencies to import.

Validation: single-file compilation through the prescribed `scompile.py` wrapper;
required `deliver2.py --no-push` preflight and compile are run before handoff.

## Second reading by Q110

I read the current DAG node, its nine proof steps, source and dependency records,
the entire delivered module, and the complete relevant declarations in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`. I independently checked Kerodon
[00ZP](https://kerodon.net/tag/00ZP),
[0101](https://kerodon.net/tag/0101), and
[0328](https://kerodon.net/tag/0328), and Stacks `simplicial.tex`,
lines 5510–5749 (the trivial-Kan and Kan definitions and their surrounding
conventions), including Lemma 08NS at lines 5641–5664. Kerodon 00ZP assumes only
that the map is a Kan fibration; its source and target need not be Kan.
Kerodon 0101 assumes both source and target Kan, as does the second conjunct.
There is no repair note for this item. There is no stage-2 `statement_change`,
no new definition node, and no dependency-module delivery to audit.

Here is my independent list of the node's objects, hypotheses and conclusions,
with the corresponding Lean and verdict for each:

1. Arbitrary simplicial sets `X,Y`, and a simplicial map `p : X → Y`:
   `∀ (X Y : SSet.{u}) (p : X ⟶ Y)`; correct. The universe `u` is explicitly
   bound, and no nonemptiness, finiteness, connectivity or fibrancy assumption
   is imposed on these two objects.
2. The sole hypothesis on `p` is lifting all positive-dimensional horns,
   outer horns included: `Fibration p →`; correct. I opened Mathlib
   `CategoryWithFibrations.lean`: the scoped instance is `J.rlp`, and `J`
   ranges over `n+1` and every `i : Fin (n+2)`. `fibration_iff` gives this
   exact interface, rather than a model-category weak-equivalence hypothesis.
3. Weak homotopy equivalence of `p`: `IsWeakHomotopyEquivalence p`; correct.
   The dependency's definition is a bijection on realization path components
   and bijections on positive cubical homotopy groups at every source
   realization point, exactly the node's convention. It is not a simplicial
   equivalence of quasicategories or a map on just one chosen component.
4. Trivial Kan fibration of `p`, including dimension zero:
   `modelCategoryQuillen.I.rlp p`; correct. I read `I`, `boundary`,
   `boundary_eq_iSup`, and `boundary_zero`. `I` uses every `n : ℕ`, and
   the boundary is the union of proper faces, with empty boundary at zero.
   This is exactly the Mathlib interface recorded by the node
   `def-weil-pbc-trivial-kan-fibration`.
5. The strict fiber at every vertex `y` is `{y} ×_Y X`:
   `∀ y : Y _⦋0⦌, ... (pullback (SSet.const (X := Δ[0]) y) p)`; correct.
   This pulls back along the actual constant vertex map from the terminal
   standard zero-simplex, not a set-theoretic fiber of just `p.app 0`.
6. Each strict fiber is both Kan and weakly contractible:
   `KanComplex (...) ∧ IsContractible (...)`; correct. `KanComplex` is
   Mathlib's all-horn predicate; `IsContractible` in the dependency means
   realization weak equivalence to `Δ[0]`, including the component condition.
7. These three properties are equivalent:
   `(IsWeakHomotopyEquivalence p ↔ I.rlp p) ∧
   (I.rlp p ↔ ∀ y, KanComplex (...) ∧ IsContractible (...))`; correct.
   The two adjacent biconditionals give exactly the three-way equivalence,
   under the preceding hypothesis and with the same universally bound map.
8. Independently, let `f : A → B` be any map of Kan complexes:
   `∀ (A B : SSet.{u}) [KanComplex A] [KanComplex B] (f : A ⟶ B)`;
   correct. Neither Kan complex is assumed inhabited. These binders belong
   to the second conjunct and do not strengthen the first conjunct.
9. The specified mapping-path object is the pullback imposing evaluation at
   zero equal to `f`: `mappingPathSubcomplex f` consists of the pairs
   `(a,γ)` in `A ⊗ (ihom Δ[1]).obj B` with `ev₀ γ = f a`, in each degree;
   `mappingPath f` is its `toSSet`; correct. I checked its restriction
   equation against the naturality of `evaluation` and `f`. It is the
   node's degreewise pullback, with all higher simplices retained, and its
   real data do not depend on the theorem's `sorry`.
10. The final-endpoint map of this object is a Kan fibration:
    `Fibration (mappingPathProjection f)`; correct. The definition projects
    to the path coordinate and then uses `evaluation` at vertex `1`.
11. The constant-path inclusion `A → P(f)` is a weak equivalence:
    `IsWeakHomotopyEquivalence (mappingPathInclusion f)`; correct. The
    inclusion's actual degreewise formula is
    `a ↦ (a, constantDiagrams Δ[1] B (f a))`. Its endpoint equality is
    proved directly from the dependency's curry/evaluation definitions,
    and its naturality is the naturality of `f ≫ constantDiagrams ...`.
    There is no arbitrary map, chosen existence witness or hollow datum.
12. Finally, `f` is a weak equivalence iff every homotopy fiber is
    contractible:
    `IsWeakHomotopyEquivalence f ↔ ∀ b : B _⦋0⦌,
    IsContractible (homotopyFiber f b)`; correct. I opened the dependency's
    `homotopyFiber`, `comma`, and `commaSubcomplex`: these impose both
    `ev₀ γ = f a` and `ev₁ γ = constant b` on the entire simplex.
    Thus these are the specified homotopy fibers and the strict fibers of
    the mapping-path projection, not the strict fibers of `f` itself.

Edge cases: dimension zero is included in boundary lifting and forces
surjectivity on vertices; horn lifting begins at dimension one and imposes
no nonemptiness condition. The empty simplicial set is Kan and is permitted
as either Kan complex in the second conjunct. A map to an empty base forces
its source empty, and the vertex-fiber quantifiers are then correctly
vacuous. For an inhabited base, an empty fiber is not weakly contractible,
because its component map to the point is not surjective. Disconnected bases
and non-Kan bases are included in the first conjunct. Characteristic, schemes,
zero objects and index-set finiteness play no role here. The common arbitrary
universe `u` is the standard universe of this category of small simplicial
sets; no extra size equality or ceiling is introduced. No variable or
universe is left implicit.

Independent duplicate searches used different terms from the first worker:

- LeanFinder: `For a horn-lifting simplicial map, boundary lifting is
  equivalent to weak equivalence and contractible strict fibers` returned
  the horn lifting instance, `I`, `J`, `KanComplex`, the fibration structure,
  and truncated strict-Segal identities. I opened the exact horn/boundary
  declarations; none states the fiber criterion or the mapping-path result.
- Loogle: `"KanComplex", "pullback"` returned zero hits.
- `msearch.py` grep: `pathObject|PathObject|fiber.*[Cc]ontract|[Cc]ontract.*fiber`
  returned generic model-category path objects and unrelated chain-complex
  path objects. I opened `ModelCategory/PathObject.lean`: `PrepathObject` and
  `PathObject` package unspecified objects and projection maps with a
  supplied weak equivalence; they do not construct this simplicial
  mapping-path pullback or state this realization fiber criterion.
- LeanSearch: `For simplicial sets, characterize boundary lifting by weak
  equivalence and contractible fibers of a Kan fibration` returned generic
  `ModelCategory.cm4a/cm4b`, the horn fibration APIs and `KanComplex`.
  No exact statement was returned. Generic model-category lifting axioms
  do not identify the realization-based weak equivalences with boundary
  lifting in this category.
- Direct `rg` of upstream `WeilConjectures`, project `lean/Sheaf`, and the
  DAG for `mappingPath`, `pathFibration`, `fibrationReplacement`,
  `homotopyFiber`, and fiber/contractibility variants found no existing
  declaration of the whole item or existing named mapping-path construction.
  I read `ContractibleHomotopyFiberEquivalence.lean` and
  `KanPullbackPathComparison.lean`; the first contains only the last clause,
  and the second concerns a two-legged path pullback comparison.
  `KanQuillenRightProper.lean` states related model-structure properties.
  The DAG nodes `lem-coef-space-kan-fibration-fiber-criterion` and
  `lem-coef-space-path-fibration-replacement` are special cases/clauses of
  this item, not an existing declaration of the item. This distinction is
  also explicitly recorded in the item's maintainer stage-1 review.
  No module is dropped and no second definition is introduced.

Repairs made:

- H8: the first theorem docstring summarized nine DAG steps in three short
  paragraphs. I replaced only that proof-plan text with the nine current
  node proof steps, including their dependency ids, low-degree component
  argument, the three path lifts in step 4, and the mapping-path contraction.
  I also added the module's main-definition/main-statement index.
- Missing proof imports: the worker report's sentence saying that the node
  has no proof dependencies is incorrect. It has ten. I added non-public
  imports of the five available proof modules: Mathlib's internal-hom
  corner-map theorem, `KanMappingHomotopyInvariance`,
  `RealizationFiniteLimits`, `TopologicalSerreModel`, and
  `TrivialKanHomotopyEquivalence`. I opened their declarations and checked
  their interfaces. A source import-graph traversal found no path back to
  this item from any of the five, so none creates an import cycle.
  The enhanced-diagrams dependency is already publicly imported;
  trivial-Kan fibrations are the existing Mathlib interface already loaded.
  The remaining three proof nodes (`lem-cbc-simplicial-homotopy-equivalence-weak`,
  `lem-coef-kan-realization-serre`, and `lem-coef-serre-homotopy-exact-sequence`)
  have neither a recorded Lean declaration nor a Mathlib match on the current
  base, so there is no corresponding proof module yet to import.

The mathematical definitions and theorem signature are unchanged. The node's
`lean.statement` was checked byte-for-byte against the signature in the module.
The sole postponed theorem remains `SSet.Enhanced.kan_fibration_fiber_criterion`
with proof `sorry`; no theorem was proved. All four helper definitions retain
real data and source/blueprint docstrings. The repaired module compiles cleanly
through `scompile.py`, both in sandbox and library position, under the prescribed
60-second limit. The wrapper also compiled its needed side overlay. No errors
or warnings were emitted. Delivery preflight is recorded below after running.

Final preflight: `deliver2.py Q110 lem-cbc-kan-fibration-fiber-criterion --no-push`
printed `OK (dry run): commit 7132be4cbe passes the preflight and compiles;
nothing pushed`. No mathematical or signature changes were needed after that
check. The actual delivery is made with the prescribed `deliver2.py` wrapper.
