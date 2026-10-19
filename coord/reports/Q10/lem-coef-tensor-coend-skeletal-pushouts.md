## Worker report

The module `Sheaf.CategoryTheory.TensorCoendSkeletalPushouts` states
`CategoryTheory.TensorCoendSkeletal.tensor_coend_skeletal_pushouts`, with real
coequalizer and colimit constructions for its objects. Every theorem proof is
`sorry`. All declarations belong to this node, including the elementary tensor
interchange, descent uniqueness, and stage-map coherence needed to type the
specified constructions. Each theorem has the corresponding proof steps in its
docstring. No statement correction, dependency repair, or new independent notion
was necessary. The node changes only in `lean` and the addition of two already
landed definition nodes to `stmt_deps`.

The indexing convention avoids negative natural numbers: `stage T X k` retains
degrees strictly below `k`, so it is the paper's `R_(k-1)`. In particular,
`stage T X 0` is the empty coequalizer (the initial object), and
`stage T X (n + 1)` is precisely `R_n(X)`. This changes only the representation of
the index, and keeps the n = 0 square.

Clause-by-clause correspondence:

- A category enriched over small simplicial sets is `{C : Type u}` with
  `[Category.{v} C] [SimplicialCategory C]`. Both universes are explicit and
  independent; the tensor parameter is `SSet.{v}`, exactly as in the recorded
  tensor dependency. All small colimits are `[HasColimits.{v} C]`. The indexing
  categories used here are small, and no object/hom universe equality is imposed.
- Chosen tensors and cotensors are `(T : SimplicialTensorCotensor C)`. Its fields
  `tensor`, `cotensor`, `tensorUnit`, `cotensorCounit`, `tensor_isIso` and
  `cotensor_isIso` are the recorded enriched representing data. The object
  `T.tensor K A` denotes the node's `A tensor K`.
- An arbitrary simplicial object is `(X : SimplicialObject C)`; a simplicial
  morphism is `(f : X ⟶ Y)`. There is no model-category or cofibrancy binder.
- The diagonal summands and standard simplices use the already recorded
  `SimplicialModelRealization.summand T X a` and `SSet.stdSimplex.obj a`.
  `Degree k` bounds the degree by `< k`; `Operator k` retains ALL simplex
  operators with both endpoint degrees `< k`, including identities and
  nonidentity endomorphisms. `relationLeft` applies `T.tensorMap` to
  `X.map alpha.op`; `relationRight` applies the representing-isomorphism
  transpose of `SSet.stdSimplex.map alpha`. `stage` is their actual coequalizer,
  and `stageι` its actual coproduct-summand projection.
- The initial `R_-1` is the first conjunct
  `∀ X, Nonempty (IsInitial (stage T X 0))`. It is constructed by the empty
  coequalizer, not chosen from an unspecified existence claim.
- The unbounded coequalizer `|X|` is the existing
  `SimplicialModelRealization.realization T X`, imported through the two added
  landed dependencies. It is not redefined.
- `LatchingIndex n` is the opposite full subcategory of `Under [n]` consisting
  of epimorphic legs with target degree `< n`. In the simplex category,
  epimorphisms are precisely the order-preserving surjections. A triangle from
  theta' to theta in `Under [n]`, reversed in this index, is exactly a map
  rho with theta = theta' followed by rho. Its intervening rho is automatically
  surjective, because theta is surjective. Thus the full-subcategory encoding
  has exactly the objects and morphisms in the node, without adding any
  nonsurjective rho. `latchingDiagram X n` applies `X` to this reversed
  codomain projection, so its arrow is exactly `X(rho): X_a → X_a'`.
  `latching` is its colimit; `latchingCocone` has legs `X(theta)`;
  `latchingTo` is its induced lambda_n.
- The boundary is Mathlib's `SSet.boundary n`, defined simplexwise by failure
  of surjectivity. `boundary_eq_iSup` identifies it with the union of proper
  codimension-one faces, and `boundary_zero` identifies degree zero with the
  empty subcomplex. `boundaryLeft` is tensoring its inclusion with L_n;
  `boundaryRight` tensors lambda_n with the boundary. `attaching` is exactly
  their pushout B_n. `attachingTo` is `pushout.desc` of lambda_n tensor 1 and
  the boundary inclusion. Its named `tensor_interchange` equality is precisely
  the commutation needed for this actual descent, not a data axiom.
- `IsUpperMap`'s first conjunct gives the stated theta component of the top
  edge after every latching coprojection. Its second conjunct gives the stated
  delta component after every proper injective face, using the unique
  factorization `j` of that face through the boundary. It quantifies over every
  such factorization, not just elementary cofaces. `upperMap_exists` asserts
  existence and uniqueness with BOTH component descriptions, so it asserts
  agreement on all face intersections and mixed overlaps. `upperMap` uses
  `Classical.choose` only from this uniquely determining statement.
- The square is `IsPushout (upperMap T X n) (attachingTo T X n)
  (stageMap T (𝟙 X) (Nat.le_succ n))
  (stageι T X (n + 1) [n] (Nat.lt_succ_self n))` for EVERY natural `n`.
  Its four arrows have exactly the orientation in the node. `stageMap_exists`
  uniquely characterizes every truncation map by its diagonal summands, so
  the right edge is the required inclusion-induced map.
- `sequence T X` is the actual `ℕ`-indexed functor of stages `R_n`; its map
  on n ≤ m is the uniquely determined inclusion map. `stageMap_laws`
  supplies its identity and composition proofs, postponing only named
  propositions. The comparison conjunct asserts an isomorphism
  `colimit (sequence T X) ≅ realization T X` whose hom restricts, for EVERY
  n, to the uniquely determined full-coend comparison `toRealization`.
  Thus it specifies the canonical comparison rather than an arbitrary iso.
- Square naturality is the last conjunct. `IsAttachingMap` uniquely
  characterizes the induced map on B_n by both pushout summands, using the
  canonical `latchingMap f n` and `T.tensorMap boundary (f_n)`. The two
  following equations give naturality of the upper and left edges. The
  bottom and right edges are natural by the diagonal component equation in
  `stageMap_exists` and the general composition law `stageMap_laws`.
- Isomorphism naturality is included in the comparison conjunct: for every
  f and every target comparison with the same specified legs, there is a
  unique map c of sequential colimits with the prescribed stage restrictions,
  and `c ≫ eY.hom = e.hom ≫ SimplicialModelRealization.map T f`. Existence
  of c is asserted, so the naturality condition is not vacuous. The existing
  realization map is coequalizer descent of the recorded summand maps.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SimplicialTensorCotensor`:
  `CategoryTheory.SimplicialTensorCotensor`, including its entire structure
  signature, and `CategoryTheory.SimplicialTensorCotensor.tensorMap`.
- `Mathlib.AlgebraicTopology.SimplicialSet.Basic` and the recorded
  `Degenerate`, `Subcomplex`, `Finite` modules: `SSet`, `SSet.degenerate`,
  `SSet.nonDegenerate`, `SSet.Subcomplex`, `SSet.Finite`. Their full signatures
  and documentation were read. Only `SSet` and the subcomplex interface occur
  in this statement. Standard simplices and their boundary use Mathlib's
  `SSet.stdSimplex`, `SSet.boundary`, and subcomplex inclusion.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `Cones`, `IsLimit`, and
  `Mathlib.CategoryTheory.Filtered.Basic`: `colimit`, `Cocone`, `IsColimit`,
  `colimit.desc`, `IsFiltered`. Full signatures/docstrings were read;
  filteredness is not an additional hypothesis here. Coequalizers, coproducts,
  pushouts, `IsInitial`, `colimMap`, and `IsPushout` use Mathlib directly.
- Proof dependency `def-weil-pbc-simplicial-object` is the Mathlib-status node
  matching `CategoryTheory.SimplicialObject` in
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`, read in full at its
  defining signature. This is imported publicly because it also occurs in
  the signature, and is not separately redefined.
- Added landed node `def-coef-simplicial-model-realization` uses module
  `Sheaf.CategoryTheory.SimplicialModelRealization`: `summand`, `Operator`,
  `relationSummand`, `relationLeft`, `relationRight`, `realization`. Its node
  statement and recorded declarations, docstrings and complete signatures
  were read. It also gives the exact parameter-map convention used here.
- Added landed node `def-coef-simplicial-realization-map` uses module
  `Sheaf.CategoryTheory.SimplicialModelRealizationMap`:
  `CategoryTheory.SimplicialModelRealization.map`. Its node and whole module
  were read, including the coequalizer-descent compatibility theorem.
- The parameter transpose is the existing
  `CategoryTheory.SimplicialUndercategory.tensorTranspose` from
  `Sheaf.CategoryTheory.SimplicialUndercategoryModel`, imported by the full
  realization dependency. Its signature, docstring and actual inverse
  representing-isomorphism construction were read; it requires no model
  structure. The new `parameterMap` only specializes this transpose to a
  parameter morphism followed by `T.tensorUnit`.

Source check: opened Dugger's actual online PDF, printed pp. 9–10 and 90.
Formula (3.2) gives both coend arrows. Theorem 3.5's proof gives the truncated
coequalizer, sequential-colimit identification and displayed latching-boundary
pushout. Section 19.1 gives the enriched tensor/cotensor adjunctions. The node's
categorical formulation isolates the colimit calculation from that theorem's
model/cofibrancy hypotheses, exactly as its fourteen-step proof explains.
The Lean theorem's docstring retains all fourteen steps and their order.

Edge cases checked before writing and checked again against the compiled file:

- n = 0: `LatchingIndex 0` and `Degree 0` are empty; the boundary is empty.
  Tensor adjunctions preserve these initial objects. Thus B_0 and R_-1 are
  initial and the same statement gives R_0 ≅ X_0 tensor Delta^0.
- Constant simplicial objects: for n ≥ 1 all degree-n simplices are supplied
  by degeneracies; the formula recovers a constant skeletal filtration up to
  its canonical isomorphisms. No latching mono or cofibrancy is assumed.
- An initial simplicial object gives initial tensor cells and coends; the
  empty latching and boundary cases remain included.
- Nonidentity endomorphisms and operators that are neither injective nor
  surjective are retained in `Operator k`. Epi-mono image factorization in
  proof step 10 treats them, rather than silently using the fat realization.
- The simplex boundary lifts used in `IsUpperMap` exist for every proper
  injective face: its image is a proper subset, so every composite simplex
  is nonsurjective. The mono boundary inclusion makes each lift unique.
- Object and morphism universes remain independent; no extra smallness,
  model structure, nonemptiness of latching categories, or cofibrancy occurs.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "tensor coend skeletal filtration latching pushout"`:
  eight hits, including `CategoryTheory.SmallObject.attachCellsιFunctorObj`,
  `SSet.Subcomplex.MulticoequalizerDiagram`, and `Arrow.cechConerve_obj`.
  None gives the general tensor-coend skeletal square and natural comparison.
- `msearch.py ... loogle "SimplicialObject, coend"`: zero hits, unknown
  unqualified identifier `SimplicialObject`. The qualified source searches
  below independently check the actual simplex/coend APIs. A follow-up Loogle
  query `"CategoryTheory.SimplicialObject", "CategoryTheory.Limits.IsPushout"`
  completed successfully with zero hits.
- `msearch.py ... grep "latching|coend|skeletal" CategoryTheory`: 25 hits,
  chiefly categorical skeletalization and ends/coends in Type. None matches.
- `rg` for `latching|coend|realization|skeletal` in the upstream
  `WeilConjectures` tree: only unrelated derived/adically completed
  realization material and a Grothendieck-abelian realization comment;
  no tensor-coend skeletal statement. Exact item-id search found no hit.
- `rg` in `lean/Sheaf` for latching, tensor coend and realization found and
  led to reuse of the full coend and its map listed above. Reedy model
  structure modules have general restricted latching constructions;
  simplex-set/topological realization modules are special cases, and the
  chain-bar coend is chain-specific. None is this statement. The local
  latching index here is the explicit proper-surjection diagram of this
  node, expressed with Mathlib's `Under`, full subcategory, opposite and
  functor composition, not a replacement of a dependency's notion.
- `tools/blueprint_refs.py search "skeletal coend"`: zero blueprint nodes.
  DAG `rg` for truncated coends and latching-surjection wording located this
  item, the existing full-coend/extra-degeneracy material, and specialized
  simplicial-space/bar statements; no separate definition node is needed
  for the truncated diagram explicitly introduced in this item's statement.
- Grep of Mathlib's latching interfaces found no simplicial tensor-coend
  skeletal theorem. The concrete boundary and existing `SimplicialObject`
  definitions are used directly. Exact proposed-name searches in the upstream
  name index, Mathlib, upstream sources and side-project sources found no
  collision (`TensorCoendSkeletal`, `tensor_coend_skeletal_pushouts`,
  `tensor_coend`, `skeletal_pushout`).

Validation: the module compiled through the prescribed `scompile.py` wrapper
with exit status 0 and no warnings (both sandbox and library-path probes).
The final delivery dry run is recorded below after it completes. No delivery
was pushed; an independent second reader is still required.

Delivery dry run: `deliver2.py Q10 lem-coef-tensor-coend-skeletal-pushouts
--no-push` completed with exit status 0 and printed
`OK (dry run): commit 4aeb1db006 compiles and passes the preflight except for
the second reading, which the second reader writes; nothing pushed.`
The staged packet consisted only of this report, the item's node JSON, and
`lean/Sheaf/CategoryTheory/TensorCoendSkeletalPushouts.lean`. The expected
independent second-reading section is deliberately left for the next worker.

## Second reading by Q10

I independently read the item JSON, the entire delivered module, all five
statement-dependency records and their defining declarations, the simplicial-object
proof dependency, and the tensor transpose used by the realization dependency.
There is no repair note for this item. The node has no `statement_change` and
there are no new nodes or dependency modules in this packet.

Source: I opened [Dugger's actual PDF](https://pages.uoregon.edu/ddugger/hocolim.pdf),
formula (3.2) on printed p.9, the proof of Theorem 3.5 on printed p.10,
and Section 19.1 on printed p.90. This item has no Stacks source. Formula (3.2)
uses all simplex operators; the proof gives exactly the bounded coequalizer,
sequential colimit and displayed square. The source's Reedy-cofibrancy hypotheses
are used for its subsequent cofibration/weak-equivalence conclusions. The present
node explicitly isolates the categorical colimit assertion and supplies its own
fourteen-step universal-property proof. I checked that calculation: both tensor
adjunctions give the needed colimit preservation; the image factorization of an
arbitrary simplex operator gives all relations, including endomorphisms. No model
hypothesis is needed for this assertion. The categorical latching colimit is the
stated generalization of the source's union of degeneracy images.

My checklist of the node, with its Lean counterpart and verdict:

1. A category C enriched over small simplicial sets: `{C : Type u}`,
   `[Category.{v} C] [SimplicialCategory C]`. I opened Mathlib's
   `SimplicialCategory`, which is `EnrichedOrdinaryCategory SSet.{v} C`,
   including the identification of underlying arrows with zero-simplices.
   Verdict: exactly the required ordinary/enriched structure.
2. Chosen tensors and cotensors, all small colimits: `T : SimplicialTensorCotensor C`
   and `[HasColimits.{v} C]`. I read the dependency's entire structure: tensor
   and cotensor objects, universal elements and invertibility of the canonical
   enriched representing maps. Mathlib's `HasColimits` means diagrams with
   object/hom size v. Thus it is cocompleteness in the same small universe as
   the enrichment. Verdict: no extra instance or model hypothesis.
3. An arbitrary simplicial object X: `SimplicialObject C` is exactly
   `SimplexCategoryᵒᵖ ⥤ C`; maps `f` are natural transformations.
   Verdict: no restriction on X or its latching arrows.
4. The coequalizer R_n and its two maps: `stage T X (n + 1)`, with
   `Degree (n + 1)` and `Operator (n + 1)`. The operator subtype bounds BOTH
   endpoint lengths, retains every arrow, and uses the dependency's
   `relationSummand = T.tensor Delta^a X_b`. `relationLeft` applies
   `T.tensorMap Delta^a (X.map alpha.op)` into the a summand;
   `relationRight` transposes `Delta^alpha` followed by the universal tensor
   element into the b summand. Verdict: precisely the two displayed arrows,
   with a harmless shift from degree bound n to count n+1.
5. R_-1 initial and the full coequalizer |X|: the first conjunct asserts
   `Nonempty (IsInitial (stage T X 0))`. This stage is the actual empty
   coequalizer. The full object is the recorded
   `SimplicialModelRealization.realization T X`; I read its actual all-operator
   coequalizer and both arrows. Verdict: initial empty stage and exactly the
   full coend, without an unspecified replacement object.
6. L_nX, its index and lambda_n: `LatchingIndex n` is the opposite of the full
   subcategory of `Under [n]` with `a.right.len < n` and `Epi a.hom`.
   An arrow in the opposite direction is a triangle with
   theta = theta' followed by rho. Since theta is surjective, rho is
   automatically surjective. `latchingDiagram` reverses the codomain
   projection and applies X, hence its map is exactly `X(rho)` in the
   specified direction. `latching` is this colimit; `latchingCocone` has
   legs `X(theta)`; `latchingTo` is `colimit.desc`. Verdict: all objects,
   morphisms, diagram arrows and the canonical map agree.
7. Boundary and B_n: Mathlib's `SSet.boundary n` is the subcomplex of
   nonsurjective simplices. I opened its definition, `boundary_eq_iSup`
   (the union of codimension-one faces), and the degree-zero interface.
   `boundaryLeft` tensors its inclusion; `boundaryRight` tensors lambda_n;
   `attaching` is the actual pushout of this span. Verdict: the required
   boundary and pushout, including the empty boundary.
8. The canonical left edge B_n to X_n tensor Delta^n: `attachingTo` is
   `pushout.desc` of the tensor of lambda_n and the boundary inclusion.
   The named `tensor_interchange` provides their agreement, postponing
   only its proof. Verdict: the canonical map, not an arbitrary arrow.
9. The specified upper edge and overlaps: `IsUpperMap` specifies every
   latching-colimit leg by the transpose of Delta^theta, and every proper
   injective face by `T.tensorMap Delta^a (X.map delta.op)` followed by
   `stageι`. The face clause quantifies over every lift through the boundary
   with its factorization equality. Every proper injection has such a lift,
   uniquely since boundary inclusion is mono; thus this clause is not vacuous.
   The predicates describe the maps after the two pushout legs, so their
   common-domain agreement is retained. `upperMap_exists` asserts unique
   existence, and `upperMap` chooses precisely this uniquely determined map.
   Verdict: both formulas and all overlaps are present.
10. The square for every n: the second conjunct is
    `IsPushout (upperMap ...) (attachingTo ...) (stageMap T (id X) ...)
    (stageι ...)`. In Mathlib's square convention these are the upper, left,
    right and bottom edges respectively. `stageMap_exists` fixes the right
    edge on every diagonal summand; `stageι` is the degree-n projection.
    Verdict: correct orientations and canonical maps for every natural n.
11. The sequential-colimit isomorphism: `sequence T X` has objects
    `stage T X (n+1)` and inclusion-induced maps. Its functor laws use the
    named `stageMap_laws`. The third conjunct gives an actual isomorphism
    from its colimit to the recorded realization and fixes its hom on EVERY
    stage as `toRealization`, itself uniquely specified on every summand.
    Verdict: the canonical comparison is invertible, not merely some iso.
12. Naturality of the square: the last conjunct gives a unique map of B_n's,
    `IsAttachingMap` fixes its restrictions on BOTH pushout legs, and the two
    following equations commute with the upper and left edges. The bottom
    edge's naturality is precisely `stageMap_exists` on the n summand, and
    the right edge's is the composition law in `stageMap_laws`.
    Verdict: all four edges are natural; identity and composition follow
    from the uniqueness characterizations.
13. Naturality of the isomorphism: for every f and every target comparison
    with its canonical legs, the third conjunct asserts a unique colimit
    map c with all prescribed stage legs and
    `c ≫ eY.hom = e.hom ≫ SimplicialModelRealization.map T f`.
    Each Y has such an eY by the same theorem, so this is not conditional
    on an unavailable choice. I opened the dependency's `mapLeg`,
    `map_condition`, and `map`: the right-hand map is exactly coequalizer
    descent of the component tensor maps. Verdict: the stated naturality,
    with the correct order of quantifiers.

Edge cases: at n=0 both `Degree 0` and `LatchingIndex 0` are empty, and the
boundary is empty. The same square includes R_-1 and attaches the degree-zero
tensor. In degree one a constant object has identity latching map, so the
square introduces no new object up to its canonical isomorphism. An initial
simplicial object remains initial after the tensors and colimits used here.
If C has a zero object, there is no nonzero or nontriviality restriction.
No scheme or coefficient ring occurs, so empty schemes and characteristic
impose no extra cases. Universes u and v are independently bound, all diagrams
used are small, and no equality u=v or nonempty latching-index hypothesis
occurs. Nonidentity endomorphisms and mixed operators are retained.

Independent searches, using words beyond the worker's query:

- LeanFinder: `simplicial object realization skeletal filtration boundary
  latching pushout` returned `SSet.skeleton_succ`, `SSet.skeleton`,
  `SSet.skeletonOfMono`, and related simplicial-set skeleton results. I opened
  `Skeleton.lean`: these identify subcomplexes of a simplicial set, not the
  arbitrary enriched tensor-coend square.
- Loogle: `"SimplicialObject", "IsPushout"` returned zero hits.
- LeanSearch: `The realization of a simplicial object is the sequential
  colimit of its skeleta, each obtained by a latching boundary pushout.`
  returned `SSet.toTop`, `SSet.iSup_skeleton`, `SimplicialObject`, and
  coskeletal/pointwise-colimit results, none with this statement.
- Wrapper grep: `geometricRealization|latchingObject|skeleton_succ` in
  AlgebraicTopology returned the two `skeleton_succ` occurrences above.
  Direct rg in Mathlib and upstream WeilConjectures found no general
  latching/tensor-coend theorem. Project rg found the landed realization
  and its map (reused), general Reedy and direct-category latching APIs,
  and specialized pinched-cube and simplicial-space constructions. I opened
  the general Reedy latching signatures: they use a positive wide
  subcategory and additional limit-size interfaces, rather than giving
  this item's explicit proper-surjection diagram or skeletal theorem.
- A separate project search for `tensorparam|tensorparameter|parameterMap`
  found an actual H4 issue: `HomotopicalAlgebra.barTensorParameterMap` in
  `Sheaf.CategoryTheory.SimplicialBarProjectiveResolution` has exactly the
  same signature and body as this delivery's `parameterMap`. I opened it
  and its node record. It is an unrestricted tensor-parameter arrow,
  despite its bar-specific name.

Repair: removed the duplicate `parameterMap` declaration and its entry in
`lean.declarations`. At each former use I wrote the application of the
already recorded `SimplicialUndercategory.tensorTranspose` directly, exactly
as the full-realization dependency does. This avoids importing the downstream
bar-resolution theorem and its proof dependencies. All tensor-parameter maps
still have precisely the same underlying term. The worker report's discussion
of a new `parameterMap` is superseded by this repair. No mathematical
statement, hypothesis, stage object, canonical arrow or conclusion changed.
No other mismatch was found.

All six postponed theorems remain named, have source/blueprint docstrings and
proof explanations corresponding to this node's steps; their proofs are all
`sorry`. All definitions have real data. Unique-choice definitions have full
uniqueness characterizations. Structure-law proofs use existing equalities;
there is no anonymous sorry in data. All declarations are recorded, no private
notation or instance is introduced, and all lines meet the 100-column rule.
The main `lean.statement` is verbatim equal to the file signature. The only
node-field changes remain `lean` and addition of the two landed definition
nodes to `stmt_deps`.

Validation after repair: prescribed `scompile.py` compiled the delivered module
in both sandbox and library-path probes with exit status 0 and no warnings.
The wrapper also compiled its three side-only prerequisite overlays cleanly.
The main signature equality and line-width checks passed again.

Second-reader delivery dry run: `deliver2.py Q10
lem-coef-tensor-coend-skeletal-pushouts --no-push` exited 0 and printed
`OK (dry run): commit 23672928f7 passes the preflight and compiles; nothing pushed`.
It staged exactly the report, the item node and the single delivered module.
