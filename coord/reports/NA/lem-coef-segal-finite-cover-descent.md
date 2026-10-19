## Worker report

The item is stated in `Sheaf.AlgebraicTopology.SegalFiniteCoverDescent` as
`SSet.SegalSpace.finite_cover_descent`, with proof `sorry`. It uses the recorded
Kan--Quillen right proper module and the recorded Reedy-cartesian simplicial-space
module. The missing interval-cover notion is supplied by the new definition node
`def-coef-segal-interval-cover`, in `Sheaf.AlgebraicTopology.SegalFiniteIntervalCover`.

For the item statement, the Lean correspondence is as follows.

- The outer simplex dimension is `n : ℕ`; a subset of `{0,…,n}` is the finite set
  `S : Finset (Fin (n + 1))`. The family is
  `𝔽 : Finset (Finset (Fin (n + 1)))`. Its two hypotheses are rendered by
  `∀ S ∈ 𝔽, S.Nonempty` and by closure under nonempty intersections
  `∀ S T, S ∈ 𝔽 → T ∈ 𝔽 → (S ∩ T).Nonempty → S ∩ T ∈ 𝔽`.
- `F(n)` is the existing `SSet.SegalSpace.discreteRepresentable n` construction
  (the discrete-inner extension of `SSet.stdSimplex.obj ⦋n⦌`), and the face
  `F(S)` is Mathlib's `SSet.stdSimplex.face S`. The family union is the new
  `SSet.SegalSpace.faceUnion 𝔽`, the lattice supremum of those full faces.
- `V : SimplicialSpace.{u}` is Reedy fibrant through `IsReedyFibrant V`. Its Segal
  hypothesis is exactly
  `∀ m : ℕ, 2 ≤ m → Enhanced.IsWeakHomotopyEquivalence (segalMap V m)`;
  `segalMap` is the existing map to the iterated consecutive-edge pullback
  `pathSpace V m`.
- The simplicial subobject `A ⊆ X`, discrete in the inner direction, is represented
  by a subcomplex `A` of `SSet.stdSimplex.obj ⦋n⦌` and the inclusion hypothesis
  `hA : A ≤ faceUnion 𝔽`. Both `A.toSSet` and `(faceUnion 𝔽).toSSet` are postcomposed with
  `Functor.const SimplexCategoryᵒᵖ`, giving discrete simplicial sets in each
  outer degree. The canonical inclusion is
  `Functor.whiskerRight (SSet.Subcomplex.homOfLE hA)
  (Functor.const SimplexCategoryᵒᵖ)`. This agrees with the existing
  `discreteRepresentable` construction on the whole simplex.
- For every `S ∈ 𝔽`, `A ∩ F(S)` is rendered by the lattice meet
  `A ⊓ SSet.stdSimplex.face S`, and the interval-cover clause is
  `IsIntervalCover S (...)`.
- The conclusion is the restriction map in the existing mapping-space calculus,
  `mappingSpacePre (Functor.whiskerRight (SSet.Subcomplex.homOfLE hA)
  (Functor.const SimplexCategoryᵒᵖ)) V`; membership in
  `SSet.modelCategoryQuillen.I.rlp` is precisely the trivial Kan-fibration
  boundary-lifting property, including the zero-simplex boundary.
- If `𝔽` is empty, `faceUnion 𝔽 = ⊥`; `hA` forces `A = ⊥`, so both discrete-inner
  simplicial spaces are empty as required. No nonemptiness hypothesis on the family
  was added.

The new definition module gives the missing combinatorics. Its filename is `SegalFiniteIntervalCover.lean` because the shared library now contains a distinct landed module `SegalIntervalCover.lean` owned by `lem-coef-segal-interval-cover`; that declaration was inspected and does not state this Finset-family predicate. `IsConsecutiveInterval`
is defined by endpoints `a ≤ b` and the filtered set
`S.filter (fun x ↦ a ≤ x ∧ x ≤ b)`. `faceUnion 𝒥` is the supremum of the canonical
Mathlib full faces `SSet.stdSimplex.face I`. `IsIntervalCover S A` requires
`A ≤ face S`, a finite family of such consecutive intervals whose face union is `A`,
all vertices of `S`, and every edge whose endpoints are consecutive in the induced
order on `S`. All definition data is real; there is no `sorry` in this module.

Dependency declarations read and reused:

- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` and the imported
  `SSet.modelCategoryQuillen.I.rlp` boundary characterization.
- `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`:
  `SSet.SegalSpace.SimplicialSpace`, `IsReedyFibrant`, `segalMap` (through its public
  Segal-space import), `mappingSpace`, and `mappingSpacePre`.
- `Sheaf.CategoryTheory.ReedyModelStructure` (proof-only import):
  `HomotopicalAlgebra.Reedy.model_structure`, supplying the model axioms used
  in the finite gluing proof.
- `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex`:
  `SSet.stdSimplex.face`, `face_inter_face`, `mem_face_iff`, `obj₀Equiv`, and `edge`.

Edge cases checked: `n = 0`; singleton `S`, where the only interval cover containing
its vertex is the full singleton face; empty `𝔽`; empty and zero-dimensional
subcomplexes; repeated or overlapping family members; and a family containing two
sets whose intersection is empty (the closure condition correctly imposes no member
for that intersection). The `Finset` encoding covers every subset of the finite ordinal
and adds no universe or cardinality restriction.

Searches for an existing interval-cover declaration were made with `msearch.py`:
LeanFinder found only `SSet.stdSimplex.face` and `SSet.stdSimplex.edge`; Loogle found
no interval-cover declaration; grep found no `interval.*cover` or
`IntervalCover|ConsecutiveInterval|faceUnion` in Mathlib/AlgebraicTopology,
the source `WeilConjectures/`, or `lean/Sheaf/`. The item's recorded searches were
also checked: the strict Segal hits concern strict simplicial sets and do not state
Reedy-fibrant mapping-space descent.

## New nodes

`def-coef-segal-interval-cover` is the missing independent notion used by the item.
Its source is Rezk, Lemmas 10.1 and 11.11. Mathlib supplies the canonical face and
edge subcomplexes but no predicate for finite consecutive interval covers; the four
search records in its node document this. The item cites this node in `stmt_deps`.

## Restoration self-check

I reread the item JSON, the new definition node, both dependency node records, and
both modules. The family quantifiers, nonempty-intersection closure, Reedy-fibrancy
and Segal weak-equivalence hypotheses, subcomplex inclusion, per-face interval-cover
condition, and trivial-Kan restriction conclusion all appear in the theorem in the
same order. The empty-family case is forced to `A = X = ⊥`; no extra hypothesis is
present. During restoration, the saved packet was found to extend the subcomplexes
constantly in the outer direction, which did not render the discrete-inner clause.
This was repaired to degreewise postcomposition using `Functor.whiskerRight`,
matching `discreteRepresentable` and the published `outerHornInclusion` convention.
The natural-language DAG statement is unchanged. The proof docstring now carries
all six proof steps, and the proof-only Reedy-model dependency is explicitly imported.
The interval-cover module uses Mathlib's `stdSimplex.face` and `edge`, with
actual supremum data and no hollow definition. The corrected modules are compiled cleanly with `scompile.py` in dependency order (2026-10-17 UTC).
This restoration self-check is supplied for the separate second reader; it does
not replace that independent reading.

## Second reading by NA

I independently reread the item node, its source place, the two dependency records, the new definition node, and both Lean modules. Rezk Lemma 10.1 (printed p. 23) defines a cover of `F(n)` as a union of consecutive interval faces with the same 0-space as `F(n)`; Lemma 11.11 (printed p. 27) uses the analogous cover condition in the finite face decomposition. The item generalizes this to a finite intersection-closed family of vertex faces, with explicit spine containment. The paper's printed all-vertices condition alone is insufficient: the union of edges [0,1] and [2,3] misses the middle edge. The existing DAG already states the corrected spine-containing version, and the Lean follows that version; no new statement correction is made here.

The node's objects, hypotheses, and conclusion match the Lean as follows:

- Small simplicial sets and the Kan structure: `SSet.{u}` and the imported
  `SSet.modelCategoryQuillen` structure. Verdict: exact, with arbitrary `u`.
- Ambient dimension and its finite vertex set: `n : ℕ` and `Fin (n + 1)`.
  Verdict: includes every `n ≥ 0`.
- A vertex subset and its full face: `S : Finset (Fin (n + 1))` and
  `SSet.stdSimplex.face S`. Mathlib defines this by image containment.
  Verdict: exactly the node's `F(S)` with its induced order.
- The finite face family: `𝔽 : Finset (Finset (Fin (n + 1)))`.
  Verdict: exactly a finite family of subsets; repetitions do not affect unions.
- Nonempty family members: `∀ S ∈ 𝔽, S.Nonempty`. Verdict: exact; this does
  not assert that `𝔽` itself is nonempty.
- Intersection closure: `∀ S T, S ∈ 𝔽 → T ∈ 𝔽 → (S ∩ T).Nonempty → S ∩ T ∈ 𝔽`.
  Verdict: exactly closure under nonempty intersections.
- The simplicial space: `V : SimplicialSpace.{u}`. Its conjunction states
  `IsReedyFibrant V` and weak equivalence of `segalMap V m` for every `m ≥ 2`.
  I read `pathSpace` and `segalMap`: their target is the strict consecutive-edge
  pullback, not a strict-Segal condition on a single simplicial set. Verdict: exact.
- The union `X`: `faceUnion 𝔽`, extended discretely in the inner direction.
  The existing `discreteRepresentable n` uses exactly this postcomposition with
  `Functor.const SimplexCategoryᵒᵖ` on the whole standard simplex. Verdict: exact.
- The discrete-inner subobject `A ⊆ X`: a standard-simplex subcomplex `A` and
  `hA : A ≤ faceUnion 𝔽`, with the same postcomposition. Verdict: exact; every
  such subobject is represented, without a fibrancy hypothesis on `A` or `X`.
- The local cover hypotheses: `∀ S ∈ 𝔽, IsIntervalCover S
  (A ⊓ SSet.stdSimplex.face S)`. Verdict: exactly `A ∩ F(S)` is an interval cover;
  its vertices, intervals, and consecutive edges are checked below.
- The conclusion: `SSet.modelCategoryQuillen.I.rlp (mappingSpacePre ... V)`.
  Its map is restriction along `Functor.whiskerRight
  (SSet.Subcomplex.homOfLE hA) (Functor.const SimplexCategoryᵒᵖ)`.
  I read `mappingSpacePre` and the boundary/trivial-fibration clause of
  `right_proper_kan_quillen`. Verdict: precisely the canonical restriction
  `Map(X,V) → Map(A,V)` is a trivial Kan fibration, including degree-zero lifting.

All quantifiers range over the node's objects; moving the independent `V` binder
past the face-family data has no mathematical effect. No hypothesis or conclusion
clause is added, omitted, strengthened, or weakened.

The new definition module renders the interval-cover notion with `IsConsecutiveInterval`, `faceUnion`, and `IsIntervalCover`. Consecutive intervals are filtered subsets between endpoints in the induced order on `S`; this forces nonempty intervals and keeps them inside `S`. `IsIntervalCover` requires containment in the full face, a finite union of such interval faces, every vertex of `S`, and every edge joining consecutive elements of `S`. For a singleton `S`, the vertex clause forces the full singleton face, agreeing with the node. For empty `S`, the empty face and empty union are permitted. The existing `SegalIntervalCover` structure was checked separately: it packages a positive-length interval presentation of a representable `F(m)` and is not a predicate for arbitrary vertex subsets and ambient subcomplexes, so it does not state this node's notion and is not duplicated by `IsIntervalCover`.

I checked the edge cases `n = 0`, singleton faces, empty `𝔽`, empty and zero-dimensional subcomplexes, repeated or overlapping family members, and disjoint family members. An empty family gives `faceUnion 𝔽 = ⊥`; `hA` then forces `A = ⊥`, and the displayed restriction is the identity on the terminal mapping space. The Finset encoding introduces no extra cardinality, characteristic, or universe restriction. Degenerate edges in the Lean edge quantifier are already forced by the subcomplex and vertex clauses; the nondegenerate consecutive-edge content is exactly the source condition.

I searched Mathlib, the source checkout, and `lean/Sheaf` with LeanSearch, LeanFinder, Loogle, and `rg`/grep for finite interval covers, consecutive intervals, face unions, and finite-cover Segal mapping descent. The only relevant hits were `SSet.stdSimplex.face`, `SSet.stdSimplex.edge`, and strict-Segal spine APIs; none states this Reedy-fibrant simplicial-space theorem or this arbitrary-subset interval-cover predicate. I also checked the recorded declarations of `lem-coef-kan-quillen-right-proper` and `lem-coef-simplicial-space-reedy-cartesian`; the imported names and universes match their node records. No mismatch was found, so no source or Lean statement was changed in this second reading.

Independent search details (second reader): LeanFinder query `Bisimplicial homotopy Segal objects mapping restriction from intersection-closed finite face unions` returned only strict-Segal/path APIs; Loogle query `"spine", "fibration"` returned zero hits; LeanSearch query `A finite union of simplex faces containing each induced spine gives a trivial restriction fibration into a homotopy Segal object` returned faces, strict spines, and horn lifting, with no exact theorem. The launcher grep query `IntervalCover|ConsecutiveInterval|faceUnion|finite_cover_descent` returned zero upstream hits. Direct `rg` over Mathlib/AlgebraicTopology, upstream WeilConjectures, and shared lean/Sheaf found the already discussed positive-dimensional `SegalIntervalCover` module and its callers, and no generalized predicate or finite-family descent theorem. I read Mathlib StdSimplex.lean:243–305: `face` is exactly image containment, `edge` has the stated endpoints, and `face_empty = ⊥`. The report's earlier broad zero-hit claim predates the landed `SegalIntervalCover`; this second reading records that relevant hit explicitly.
