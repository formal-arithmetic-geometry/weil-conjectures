## Worker report

The module `Sheaf.CategoryTheory.CocartesianFullRestriction` states
`SSet.Enhanced.cocartesian_full_restriction` and defines the canonical auxiliary
constructions used by the statement:

- `relativeFunctorFiber p a` is the degreewise pullback fiber of
  `(ihom K).map p` over `diagramVertex a`.
- `relativeFunctorInclusion R p a` is the canonical pullback map induced by
  `R.ι` and identity on the base point.
- `relativeDiagramInFull R p a n z` says that the underlying coherent diagram
  of `z` factors through `(ihom K).obj (R : SSet)`; because `hfull` identifies
  `R` with the full subcomplex on its vertices, this renders “all object values
  belong to R”.

The theorem renders each hypothesis as follows. `p : E ⟶ B` binds the map,
`[Quasicategory E] [Quasicategory B]` say that its endpoints are quasicategories,
and `(hp : cocartesianFibrationOver p)` says that the map is a cocartesian
fibration. By the recorded definition, `hp` includes `InnerFibration p` and
cocartesian lifts of every base edge from every prescribed source. These are
separate from the transport hypothesis, which only concerns sources in `R`.
`hfull` states exactly that `R` is the full subcomplex on the
predicate `x ∈ R.obj (op ⦋0⦌)`. `hreplete` says that an equivalence edge in `E`
whose source is in `R` has target in `R`. `htransport` binds an object `x` in
`R`, a base vertex `b`, and a base edge `α` with source `p(x)` and target `b`,
and supplies an edge `e` with source `x`, target in `R`, image `α`, and
`IsCocartesianEdge p`.

The conclusion is the conjunction of these clauses:

1. `Quasicategory (R : SSet)` and `cocartesianFibrationOver (R.ι ≫ p)` render
   the restricted cocartesian fibration.
2. For every edge `e : Δ[1] ⟶ (R : SSet)`, the equivalence
   `IsCocartesianEdge (R.ι ≫ p) e ↔ IsCocartesianEdge p (e ≫ R.ι)` renders both
   preservation and reflection.
3. For every `K : SSet.{u}` and `a : K ⟶ B`, both strict relative fibers are
   quasicategories. The existential range of `relativeFunctorInclusion` is
   equivalent degreewise to `relativeDiagramInFull`, rendering the full
   subcategory on diagrams valued in `R`.
4. For every pair of `R`-valued fiber vertices and every simplex degree, the
   induced `mappingSpaceMap` is bijective degreewise. This is the asserted
   equality of right-pinched mapping simplicial sets.
5. For every precomposition `t : L ⟶ K` and every `R`-valued coherent diagram,
   the displayed existential gives its canonical precomposition in the `R`
   internal hom and identifies its image with precomposition in `E`; this is
   naturality under precomposition, including `K = ∅` (where the pullback fiber
   is the point fiber and all degreewise maps are identities).

Dependencies used: `SSet.Enhanced.fullSubcomplex`,
`SSet.Enhanced.IsEquivalenceEdge`, `SSet.Enhanced.mappingSpaceMap`,
`SSet.Enhanced.mappingSpace`, and `SSet.Enhanced.diagramVertex` from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; `SSet.Enhanced.fiber` from
`Sheaf.CategoryTheory.InfinityFibrations` (reexported by the next interface);
`SSet.Enhanced.cocartesianFibrationOver` and
`SSet.Enhanced.IsCocartesianEdge` from
`Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`; the recorded
composition/initiality declaration
`SSet.Enhanced.cocartesian_composition_initiality` from
`Sheaf.CategoryTheory.InfinityCocartesianCompositionInitiality`; and the
recorded outer-horn declaration
`SSet.Enhanced.inner_fibration_equivalence_outer_horn_lift` from
`Sheaf.CategoryTheory.InnerFibrationEquivalenceOuterHornLift`. The pushout
product dependency is the Mathlib declaration
`SSet.innerAnodyneExtensions_pushoutObjObjι'` in
`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct.lean`.

Edge cases checked before writing: `R = ⊥` and `R = ⊤`, identity base edges,
the one-point base, empty `K`, one-point `K`, degenerate cocartesian edges,
and nerves of ordinary categories. The empty-index case is represented by the
strict fiber over `K = ⊥`, whose only simplex is the pullback point.

Searches made: `msearch.py Q148 lem-coef-cocartesian-full-restriction leanfinder`
for transport-stable full subcategories (ordinary `IsCocartesian` matches only);
`msearch.py ... loogle "Cocartesian", "Full"` (no match); `msearch.py ... grep
"cocartesian|cocartesianFibration" CategoryTheory` (ordinary Mathlib
cocartesian declarations only); `rg` over `WeilConjectures/` and project
`lean/Sheaf` for cocartesian restriction, full subcategory, and relative
functor-fiber names (no exact declaration). The search outputs and timestamps
are retained in `searches.jsonl`.

## Repair of returned H3

The returned immutable head `ee192e83dc3e` omitted the hypothesis that `p` is
a cocartesian fibration. The saved packet still had that omission; its initial
dry run passed mechanically at `cda7992806`, which did not resolve H3. Added
`(hp : cocartesianFibrationOver p)` to the theorem, documented its inner-horn
and edge-lift contents, and regenerated the node's verbatim Lean signature.
The original report incorrectly attributed the fibration condition to the two
quasicategory instances; that explanation is corrected above. No mathematical
node statement or dependency changed: its first hypothesis already requires
that `p` be a cocartesian fibration. The saved node agrees with the current
shared node in every field outside `lean`.

Self-check with the node and module open: `hp` renders the previously missing
map condition; the endpoint instances, full-subcomplex equality, repleteness,
and transport hypotheses remain explicit. The five conclusion clauses and
three canonical helper definitions are retained. In the edge case `R = ⊥`,
`htransport` alone is vacuous and cannot supply `InnerFibration p`; `hp` still
requires it, as needed for the ambient relative fibers. For `R = ⊤`, the new
hypothesis is precisely the original ambient cocartesian-fibration assumption.
Empty `K`, identity base edges, and the point base are still included. All
universes and variables are bound explicitly with `autoImplicit false`.

## Second reading by Q148

Independent maintainer reading of immutable delivery
`ee275fa6178f985f60d69618b6dfb6f8a83f5f5a`, performed with the node,
module, both statement-dependency nodes and their actual declarations open.
This section replaces the delivered placeholder; it does not claim that another
worker performed a reading before delivery.

Hypothesis and conclusion audit:

- `E B : SSet.{u}`, the two `Quasicategory` instances, and `p : E ⟶ B`
  give the stipulated endpoints and map. `hp : cocartesianFibrationOver p`
  includes BOTH inner lifting and lifts of every base edge. The previous
  missing-hypothesis defect is repaired in the immutable delivery.
- `R : E.Subcomplex` and `hfull` give the full subcategory on exactly its
  degree-zero objects. `hreplete` uses the dependency's actual two-inverse-triangle
  equivalence predicate; `δ 1` is source and `δ 0` is target. This is repleteness,
  including the reverse direction by taking inverse equivalence edges.
- `htransport` retains each source in `R`, every base edge, its exact image,
  and a cocartesian lift with target in `R`. Its explicit target `b` adds no
  restriction, since it is quantified over and fixed to `δ 0 α`.
- The first two conjuncts give the restricted quasicategory and cocartesian
  fibration. The edge iff has the correct restriction and ambient edge maps.
- `relativeFunctorFiber` is the ACTUAL strict pullback over the constant base
  vertex `diagramVertex a`, using `fiber` from `InfinityFibrations` (reexported
  by `InfinityFibrationsOverSimplicialBases`). It is not the comma homotopy fiber.
  Both strict fibers are asserted quasicategories for arbitrary small `K`.
- The inclusion is the specified `pullback.map`, not an arbitrary map. Its
  internal-hom factor is induced by `R.ι`; that map is degreewise injective,
  and its pullback retains injectivity. The image iff uses factorization of
  the entire coherent simplex through `R`. Under `hfull` this is exactly the
  condition on all vertices `(k,i)` of `K × Δ[n]`, equivalently that all diagram
  vertices have object values in `R`. Thus this encodes the full subcategory.
- The mapping clause is bijectivity of the CANONICAL `mappingSpaceMap` in
  every degree, not just a weak equivalence. The dependency defines this map
  by applying the inclusion to the underlying pinched simplex. Together with
  its simplicial naturality, this is the required degreewise identification.
- The final clause gives precomposition on the underlying coherent simplices.
  Its witness is uniquely determined by the injective inclusion, and is
  precomposition in `R`. Naturality of `MonoidalClosed.pre` also gives the
  exact base `t ≫ a`; the pullback universal property induces restriction on
  strict fibers. These maps commute with simplicial operators and with
  `mappingSpaceMap`. Thus the underlying-simplex formulation retains the
  asserted naturality; no unrelated existence choice is being substituted.

Dependencies and source:

Read `EnhancedDiagramsCones.lean` and `InfinityFibrationsOverSimplicialBases.lean`,
including the latter's reexport `InfinityFibrations.lean`. Checked `fullSubcomplex`,
`IsEquivalenceEdge`, `diagramVertex`, `fiber`, `mappingSpace`, `mappingSpaceMap`,
`IsCocartesianEdge`, and `cocartesianFibrationOver` against both dependency nodes.
Also read the exact composition/initiality and relative outer-horn declarations
and the recorded Mathlib pushout-product declaration. They supply the interfaces
used by the node's six proof steps; no helper prerequisite is missing.

The IAS URL did not fetch, so read the same HTT PDF at
[the author's Harvard mirror](https://people.math.harvard.edu/~lurie/papers/HTT.pdf).
Checked printed pp. 116–119 (equivalences, cancellation, horn criterion,
initiality dual), p. 131 (2.4.4.3), pp. 100–101 (2.3.2.4–5), and pp. 151–152
(3.1.2.1). The mapping-space and exponentiation citations support the agent's
lemma; it is not presented as a verbatim published theorem.
WANTED: an archived HTT copy in literature/. The online reading is not an archive.

Edge cases and size:

Checked `R = ⊥` (transport vacuous, while `hp` still supplies ambient inner
lifting), `R = ⊤`, empty total/base where a map exists, point base, identity and
degenerate edges, degree zero and the first outer-horn dimension two, empty and
point `K`, and nerves of ordinary categories. Empty `K` yields terminal internal
homs and point strict fibers, even when `R` is empty. No nonemptiness or
Kan-base assumption occurs. All variables and universes are bound with
`autoImplicit false`. The arbitrary common simplicial-set universe agrees with
the recorded interfaces and fixed-universe convention; there is no site-universe
identification or pro-etale replacement.

Independent duplicate searches used `rg` for strict relative fiber/inclusion
names, transport-stable restrictions, full subcategories, and cocartesian
terminology in project `lean/Sheaf`, upstream `WeilConjectures`, and pinned
Mathlib. Opened the ordinary Mathlib `IsCocartesian`/`IsStronglyCocartesian`
signatures: they concern ordinary categories and do not replace this statement.
The existing generic relative restriction helper changes the indexing domain;
it is not this postcomposition inclusion. The worker's recorded LeanFinder,
LeanSearch, Loogle and grep searches were also read. No duplicate was found.

Findings and repairs:

- H1/H11: replaced the placeholder second-reading section with this actual
  clause-by-clause independent reading. Corrected the report's location for `fiber`
  and added source/archive and compiler evidence.
- H5/H6: moved the two inline `by simp` compatibility proofs out of the
  definition into the named, documented `relativeFunctorInclusion_squares`,
  with a `sorry` proof. This helper belongs to the canonical inclusion in the
  same node (proof step 5) and is listed in `lean.declarations`. The definition
  still constructs the specified pullback map; only proof obligations are postponed.
- H8: expanded the theorem proof docstring to all six node steps, including
  exact-base strict fibers, reflection through initial lifts, and empty `K`.
- H9: changed the two proof-only project imports from public to ordinary imports.

No mathematical statement, hypothesis, conclusion, universe, DAG edge, or source
record was changed. The item `lean.statement` remains verbatim equal to the
main theorem signature. There is no statement_change and no citer audit is required.
No new definition node or dependency module is introduced.

Compiler evidence:

Ran only the prescribed single-file wrapper against the immutable module and
then against the complete replacement module:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q148 \
  lem-coef-cocartesian-full-restriction \
  snapshot/lean/Sheaf/CategoryTheory/CocartesianFullRestriction.lean
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q148 \
  lem-coef-cocartesian-full-restriction \
  fixes/lean/Sheaf/CategoryTheory/CocartesianFullRestriction.lean
```

Both returned exit code 0 without diagnostics. Immutable: sandbox 1.6 s,
library 1.7 s, overlay `nt-local-compile-_n6wmj3l`. Replacement: sandbox 1.5 s,
library 1.5 s, overlay `nt-local-compile-owntqpwb`. The installed wrapper reports
server execution and uses the private overlay; this differs from its historical
local-only description, so the actual wrapper result is recorded here.
No direct SSH, global build, delivery, merge, or project-clone write was performed.
