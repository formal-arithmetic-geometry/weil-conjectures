## Worker report

### Worker result

Q50 stage 2 repaired the returned delivery by adding the missing Lean statement module and binding it in the node copy. The module is `lean/Sheaf/AlgebraicTopology/CartesianMappingSimplexMixedEquivalence.lean`, with declaration `SSet.Pinched.cartesian_mapping_simplex_mixed_mapping_equivalence`. The declaration has one postponed proof (`sorry`), as required for stage 2; it introduces no definition and no hollow data. The module and node use the canonical project constructions `SSet.Pinched.rigidification`, `SSet.Pinched.vertex`, `SSet.Pinched.edgeVertex`, and `SSet.Pinched.enrichedPostcomposition`.

The source is Lurie, *Higher Topos Theory*, Proposition 3.2.2.10, the bottom horizontal arrow of the mixed mapping square (printed p. 184), with Proposition 2.4.4.3 for the Cartesian mapping criterion and Proposition 2.2.4.1/Theorem 2.2.5.1 for transfer to raw coherent realization. The blueprint source is the item `lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence`. The module and theorem docstrings state this source and carry the four-step proof plan from the split.

### Statement, hypothesis by hypothesis

- `{Y : SSet.{u}} [Quasicategory Y]` is the small simplicial-set total space and its quasicategory structure. The latter is required by the recorded `SSet.Enhanced.cartesianFibration` notion, whose base and total are quasicategories.
- `(n : ℕ) (hn : 1 ≤ n)` renders the positive standard simplex dimension from the node. `hn` is retained in the signature even though the postponed proof does not use it yet.
- `(p : Y ⟶ Δ[n])` is the map to the standard simplex. The Cartesian-fibration hypothesis is rendered as
  `@Enhanced.cartesianFibration Y (Δ[n] : SSet.{u}) p inferInstance (@quasicategory_of_innerFibration _ _ (stdSimplex.isoNerve n).hom ⟨innerFibrations.of_isIso _⟩ inferInstance)`.
  The explicit base witness is the standard-simplex/nerve isomorphism and Mathlib's inner-fibration characterization; it supplies the canonical quasicategory fact without adding a mathematical assumption.
- `(a b z : Y _⦋0⦌)` binds the source vertex `z` and the endpoints `a,b` of the Cartesian edge.
- `(e : Δ[1] ⟶ Y)` is the edge. `hea : Y.δ 1 (SSet.yonedaEquiv e) = a` and `heb : Y.δ 0 (SSet.yonedaEquiv e) = b` render its source and target endpoint equations (the `δ 1` source and `δ 0` target convention used by the project).
- `hz : stdSimplex.obj₀Equiv (p.app (op ⦋0⦌) z) ≤ stdSimplex.obj₀Equiv (p.app (op ⦋0⦌) a)` is exactly `p(z) ≤ p(a)` after transporting degree-zero standard-simplex vertices to `Fin (n+1)`, where the order is the standard ordinal order.
- `he : Enhanced.IsCartesianEdge p e` renders that `e` is p-cartesian using the recorded final-horn lifting definition.

The conclusion is `Enhanced.IsWeakHomotopyEquivalence` of the concrete map

`enrichedPostcomposition (rigidification.obj Y) (vertex Y z) (vertex Y a) (vertex Y b) ((eqToHom (congrArg₂ (fun x y ↦ hom (rigidification.obj Y) (vertex Y x) (vertex Y y)) hea heb)).app _ (edgeVertex Y (SSet.yonedaEquiv e)))`.

Here `edgeVertex` is the canonical coherent-realization vertex `[e]`; the `eqToHom` transports its endpoint-indexed hom from the Yoneda edge endpoints to the named `a,b`; and `enrichedPostcomposition` is precisely `[e] ∘ - : 𝔠[Y](z,a) → 𝔠[Y](z,b)`. `Enhanced.IsWeakHomotopyEquivalence` is the recorded realization-based weak equivalence predicate, so the conclusion is the exact weak-equivalence clause of the node.

### Dependency declarations used

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations `SSet.Enhanced.IsWeakHomotopyEquivalence` and `SSet.Enhanced.mappingSpace` (the weak-equivalence and right-pinched mapping conventions).
- `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus`, declaration `SSet.Marked.Over.relative_marked_anodyne_calculus` (the recorded Cartesian-fibration framework and quasicategorical total-space consequence used by the source proof plan).
- `Sheaf.CategoryTheory.RigidificationPostcompositionComparison`, declarations `SSet.Pinched.rigidification`, `SSet.Pinched.vertex`, `SSet.Pinched.edgeVertex`, and `SSet.Pinched.enrichedPostcomposition` (the canonical coherent realization and specified enriched composition map).
- Mathlib `quasicategory_of_innerFibration`, `stdSimplex.isoNerve`, and `innerFibrations.of_isIso` (the explicit standard-simplex quasicategory witness in the Cartesian-fibration binder).

The stage-1 proof dependencies `lem-coef-infinity-cartesian-mapping-criterion` and `lem-coef-rigidification-postcomposition-comparison` are reflected in the module's source/docstring proof plan; the latter's module supplies the canonical coherent-realization interfaces used in the signature. No private copies or arbitrary maps were introduced.

### Edge cases checked

I checked `n = 1` and the positive-dimension boundary `n ≥ 1`; equal base vertices (`p(z)=p(a)`), a vertical Cartesian edge, and a degenerate identity edge; empty source or target mapping simplicial sets; and repeated vertices in the standard simplex. The `stdSimplex.obj₀Equiv` transport leaves all these cases in the same ordinal universe. The earlier-vertex inequality is essential: for `p = 𝟙 (Δ[1])`, the edge `0 → 1`, and `z = 1`, the source mapping space is empty while the target has the edge, so dropping `p(z) ≤ p(a)` would be false. No nonemptiness or Kan hypothesis on the raw coherent mapping sets was added.

### Searches

- `msearch.py ... leanfinder "Cartesian edge over a standard simplex induces weak equivalence on coherent realization mapping spaces"`: 8 hits, all unrelated product-simplex, singular-set, or model-category declarations; no exact statement.
- `msearch.py ... loogle "SSet.Enhanced.IsWeakHomotopyEquivalence, SSet.Pinched.enrichedPostcomposition"`: zero hits (Loogle reported unknown identifier for the project predicate).
- `msearch.py ... grep "rigidification.*postcomposition|cartesian.*mapping.*simplex" AlgebraicTopology`: zero hits.
- `rg` over `WeilConjectures/` and the project's `lean/Sheaf/`: no existing declaration with the item theorem name or a statement of the mixed Cartesian coherent-mapping equivalence. The only relevant project declarations are the canonical `edgeVertex` and `enrichedPostcomposition` interfaces in `Sheaf.CategoryTheory.RigidificationPostcompositionComparison.lean`.
- DAG search found no duplicate item declaration. The recorded dependency nodes and their full declarations were read before writing.

### Compilation evidence

Required per-file compilation was run with:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q50 lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence /home/ubuntu/weil-newtargets-stage2-sandbox/Q50/lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence/lean/Sheaf/AlgebraicTopology/CartesianMappingSimplexMixedEquivalence.lean`

The wrapper compiled the sandbox file and the library overlay successfully (exit 0, no errors and no warnings; the postponed proof warning is suppressed by the module's stage-2 option). Earlier drafts exposed the missing standard-simplex quasicategory witness, the degree-zero ordinal coercion, and the coherent Hom namespace; these were repaired and the final command is clean.

## Second reading (Q50)

I reread the final module against the node and source after the clean compile. The endpoint orientation is correct: `δ 1` is the source and `δ 0` the target, matching `IsCartesianEdge` and `edgeVertex`; `hea` and `heb` are used only for the canonical endpoint transport. The lower-base order is expressed in `Fin (n+1)` via `stdSimplex.obj₀Equiv`, so it does not compare opaque degree-zero terms or impose an extra universe equality. The Cartesian-fibration binder supplies exactly the base quasicategory witness needed by the recorded definition, while `[Quasicategory Y]` supplies the total-space instance. The conclusion is the specified enriched postcomposition map, not an arbitrary weak equivalence between the two mapping sets.

The theorem docstring identifies the HTT source, blueprint id, all four proof clauses, empty/degenerate cases, and the absence of a raw-Kan hypothesis. The node copy changes only its `lean` record; no statement, dependency, proof, source, or status field was changed. There are no new nodes, no dependency modules, no statement correction, and no `STATEMENT-DISPUTED` flag.

## New nodes

None.

## Dependency modules

None. All recorded interfaces needed for the statement are usable; the canonical realization and composition declarations come from the recorded proof-dependency module.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (NT-cc reviewer, 2026-10-17)

- H3: the delivered signature assumed `[Quasicategory Y]` and used `SSet.Enhanced.cartesianFibration` (the quasicategory-only notion of def-coef-infinity-fibrations, with an explicit `Δ[n]` quasicategory witness). The node takes cartesian fibrations "as in [lem-coef-relative-marked-anodyne-calculus]", which defines them for arbitrary small simplicial sets without assuming the total space a quasicategory, and whose recorded Lean uses `SSet.Marked.Over.relativeFibration false`. That the total space is a quasicategory is proof step 1, not a hypothesis. The binder is now `(hp : Marked.Over.relativeFibration false p)` and `[Quasicategory Y]` is dropped; the hypothesis-list entries above for `[Quasicategory Y]` and the `@Enhanced.cartesianFibration ...` binder, and the Mathlib witness declarations, are superseded. The now unused `Mathlib.AlgebraicTopology.Quasicategory.Nerve` import is removed.
- H9 / stage-2 rule 7: the stated proof dependency lem-coef-infinity-cartesian-mapping-criterion (module `Sheaf.CategoryTheory.InfinityCartesianMappingCriterion`) is now imported (non-public).
- The garbled HTT numbers in the worker result are restored (3.2.2.10, 2.4.4.3, 2.2.4.1, 2.2.5.1).
- Conclusion, endpoint transport, order hypothesis and all other binders are unchanged. `nt_compile.py` is clean for the fixed module (no error, no warning); `#print axioms`: propext, sorryAx, Classical.choice, Quot.sound.
