## Worker report

The module `lean/Sheaf/AlgebraicTopology/SegalIntervalCover.lean` states the
Rezk Lemma 10.1 interval-cover equivalence.  It imports the dependency module
`Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian` and uses its declarations
`SSet.SegalSpace.SimplicialSpace`, `discreteRepresentable`, `mappingSpacePre`,
`IsReedyFibrant`, `segalMap`, and `Enhanced.IsWeakHomotopyEquivalence`.

The helper declarations in the same module make every object in the informal
statement explicit.  `intervalFace m a b hab hbm` is the map induced by
`SimplexCategory.subinterval a (b-a)`, so it is the image of the injection
`j ↦ a+j` from `F(b-a)` to `F(m)`.  `spineEdge m a` is the special case
`F(1) → F(m)` for `a : Fin m`.  `SegalIntervalCover` introduces `m` and the
hypothesis `1 ≤ m`, a finite `Finset (ℕ × ℕ)` of valid intervals `[a,b]`,
subobjects `G,H : Subobject F(m)`, and the inclusion factorization
`G_to_H ≫ H.arrow = G.arrow`.  Its `spine_image` field says pointwise in both
simplicial directions that the image of `G` is exactly the union of all
consecutive edge images.  Its `interval_image` field says pointwise that the
image of `H` is exactly the finite union of the listed interval images.  Thus
these fields render the clauses `G(m)`, `F([a,b])`, `H`, and `G(m) ⊆ H` without
an arbitrary map or a choice of representative.

The theorem declaration is:

`theorem segal_interval_cover (C : SegalIntervalCover.{u}) (V : SimplicialSpace.{u}) (hV : IsReedyFibrant V ∧ ∀ r : ℕ, 2 ≤ r → Enhanced.IsWeakHomotopyEquivalence (segalMap V r)) : Enhanced.IsWeakHomotopyEquivalence (mappingSpacePre (Subobject.arrow C.H) V)`

The binders render the node as follows.  `C.m` and `C.hm` are the integer
`m ≥ 1`; `C.intervals` and `C.interval_valid` are the finite collection of
pairs `0 ≤ a < b ≤ m`; `C.G`, `C.H`, and `C.G_to_H_fac` render the two
subspaces and `G ⊆ H`; `spine_image` and `interval_image` render their stated
unions.  `V` is a small simplicial space.  The two conjuncts of `hV` render
Reedy fibrancy and, for every `r ≥ 2`, the weak-homotopy-equivalence
consecutive-edge comparison `segalMap V r`.  The conclusion is weak homotopy
equivalence of `mappingSpacePre C.H.arrow V`, which is exactly restriction
`Map(F(m),V) → Map(H,V)` from the dependency's mapping-space construction.
The proof is `sorry` as required; its docstring records the finite interval
induction and the Segal comparison argument.

Edge cases checked: `m = 1` has one edge and `spineEdge` is the identity
interval; `m = 0` is excluded by `hm`; every listed interval has positive
length; an empty interval list cannot satisfy `spine_image` for `m ≥ 1`; and
empty simplicial-set levels are handled by the pointwise `Set.range` clauses.
The definitions use the full universe `u` of the representable and mapping
simplicial sets.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "finite union of consecutive interval faces containing the spine of a representable simplicial space restriction mapping space weak homotopy equivalence"`: hits were `SSet.spine_map_subinterval`, strict-Segal interval lemmas, and horn/spine facts; none states the mapping-space restriction theorem or finite interval-cover notion.
* `msearch.py ... loogle "Subobject, Set.range, SimplexCategory.subinterval, Enhanced.IsWeakHomotopyEquivalence"`: zero hits (the query parser did not recognize `Subobject`).
* `msearch.py ... grep "intervalFace|SegalIntervalCover|segal_interval_cover" AlgebraicTopology`: zero hits.
* `rg -n "interval-cover|interval cover|consecutive interval|segal_interval|Segal.*interval" lean/Sheaf /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no matching declaration.

Mathlib's `SimplexCategory.subinterval` is used for the canonical face maps;
its existing `SSet.spine_map_subinterval` result concerns a single simplicial
set and does not duplicate this theorem.  No node correction, statement fault,
`STATEMENT-DISPUTED`, dependency-module repair, or new definition node is
needed.  The helper declarations are recorded in the item's `lean.declarations`
list as permitted owning-module helpers.

## Second reading by NB

I independently opened the item and all six of its proof steps, the statement
dependency node and its recorded module, the two other proof-dependency nodes
and their signatures, and the delivered Lean file. There is no repair note for
this item. Its only changed node field is `lean`; there is no statement correction,
new definition node, or dependency-module repair to audit.

Source read: [Rezk's paper](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf),
Sections 2.2--2.5 (printed pp. 5--7), Definition 4.1 (p. 11), and Lemma 10.1,
its preceding cover definition and proof (p. 23). This is a simplicial-space
result, with no Stacks source. The source's standing convention is simplicial
sets as spaces, with the Reedy model structure unless another is specified.
Definition 4.1 requires Reedy fibrancy and the consecutive-edge weak equivalences;
it requires neither completeness nor connectedness.

The list of objects, hypotheses and conclusions, matched in order:

1. Small simplicial spaces, `F(m)` and simplicial mapping spaces: PASS.
   `SimplicialSpace.{u}` is `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. I opened
   `SegalCartesianExponent.lean`: `discreteRepresentable m` applies the constant
   simplicial-set functor to the standard outer representable. This is discrete
   in the inner direction, rather than constant in the outer direction.
   In `SimplicialSpaceReedyCartesian.lean`, `mappingSpace` is outer-degree-zero
   evaluation of the existing cartesian internal hom. Since `F(0)` is terminal,
   its inner q-simplices are precisely maps `A × cΔ[q] → V`.
2. An integer `m ≥ 1`: PASS, `C.m : ℕ` and `C.hm : 1 ≤ C.m`.
   Natural-number endpoints encode exactly the integers in the stated range.
3. The spine `G(m)` as the union of all consecutive edges: PASS, `C.G` is a
   subobject of `discreteRepresentable C.m`, and `C.spine_image` identifies its
   image in every bidegree with the union indexed by `a : Fin C.m`.
   `spineEdge m a` is the whiskered standard-simplex map on the consecutive
   interval of length one starting at `a.val`.
4. The canonical interval face `F([a,b])`: PASS, `intervalFace m a b hab hbm`
   uses `SimplexCategory.subinterval a (b-a)`. I read its definition in
   Mathlib `SimplexCategory/Basic.lean:172`: it sends `j` to `j+a`, the stated
   injection `a+j`. Whiskering with the constant inner functor gives exactly
   `F(b-a) → F(m)`. Both endpoint proofs are bound and their arithmetic use is
   discharged by `omega`; no map or object is chosen using an unproved theorem.
5. A finite collection of valid intervals: PASS, `C.intervals` is a
   `Finset (ℕ × ℕ)`, and `C.interval_valid` says `a < b ∧ b ≤ m` for every
   member. Nonnegativity is supplied by `ℕ`. Removing duplicate intervals
   changes no union and imposes no mathematical restriction.
6. The subobject `H` equal to their union: PASS, `C.H` is a subobject of the
   same representable, and `C.interval_image` identifies its image with exactly
   those interval-face images, at every outer and inner simplex. Subobject
   arrows are monomorphisms; the pointwise clauses determine the required
   subobjects, allowing any isomorphic representative of their domains.
7. Spine containment `G(m) ⊆ H`: PASS, `C.G_to_H` is a map of their underlying
   subobjects and `C.G_to_H_fac` factors the spine arrow through `H.arrow`.
   A factorization of subobject arrows is precisely containment; its data are
   unique by monicity and are not an arbitrary restriction map hypothesis.
8. A small Reedy fibrant `V`: PASS, the theorem binds
   `V : SimplicialSpace.{u}`, with `hV.1 : IsReedyFibrant V`. I read the
   definition: the terminal map is in the relative-matching right class for
   opposites of injective simplex maps, using the existing Kan fibrations.
   No extra model-category instance is a theorem hypothesis.
9. All Segal comparisons in degrees `r ≥ 2`: PASS, `hV.2` quantifies over all
   natural `r` with `2 ≤ r`. I opened `pathSpace`, `segalMap` and Mathlib's
   `SSet.Path`/`spine`: the target is the strict string of edges with matching
   source and target vertices, and the map restricts to those consecutive
   edges. For positive length the vertices are determined by the edges, so
   retaining them adds no condition. This is the displayed iterated fibre
   product, not strict Segal bijectivity or a substituted homotopy pullback.
10. Restriction `Map(F(m),V) → Map(H,V)` is a weak homotopy equivalence: PASS.
    `mappingSpacePre (Subobject.arrow C.H) V` has precisely that variance and
    is defined by `MonoidalClosed.pre`, hence by precomposition. I opened
    `Enhanced.IsWeakHomotopyEquivalence`: it requires bijectivity on realization
    components and every positive based homotopy group, exactly the convention
    of the Kan dependency. There is no extra trivial-fibration conclusion.
    The bundled cover precedes `V`, and its fields depend only on the cover;
    this is equivalent to the node's order of universal quantification.

The source discrepancy is already recorded in the inherited node and in
`coord/reports/Q31/lem-coef-segal-interval-cover.md`, which I read. Merely having
all vertices would allow `[0,1] ∪ [2,3]` in `F(3)`. Into the discrete nerve of
the one-object category with automorphism group `C₂`, restriction is the map
from eight triples of arrows to four pairs forgetting the middle arrow, hence
not a weak equivalence. Such discrete nerves are Reedy fibrant Segal spaces.
The node and Lean both require the whole spine and exclude this example.
No new statement change is called for.

Edge cases: `m=0` is excluded in both versions; for `m=1` the unique consecutive
edge is the whole representable and containment forces `H=F(1)`. For `m=2` a
proper cover is the spine, giving the assumed degree-two comparison. Overlapping
intervals `[0,2]` and `[1,3]` intersect in `[1,2]`; touching intervals have a
singleton intersection, whose vertex lies in the local spine. Repeated or
contained intervals give no new piece. The empty interval collection forces
the image of `H` empty by `interval_image`, contradicting spine containment and
the nonempty spine when `m≥1`. More precisely, the worker report's reference
to `spine_image` alone is insufficient: all three fields are used here.
The empty simplicial space `V` is allowed: maps from both nonempty domains
give empty mapping simplicial sets, and restriction is an equivalence.
For terminal `V` both mapping spaces are terminal. Empty bidegrees are treated
without choosing points. Universe `u` is arbitrary and common to the small
spaces; the indexing simplex category and finite interval endpoints are small
in every such universe. There are no schemes, coefficient rings, characteristics,
or additional universe equalities in this statement.

Independent searches, actually run through the prescribed wrapper:

- LeanFinder, `simplicial space finite interval subcomplex spine containment
  restriction mapping spaces Segal equivalence`: eight hits, including
  `SSet.StrictSegal.spineToSimplex_interval`, `SSet.spine_map_subinterval`, and
  strict-Segal spine equivalences. I opened Mathlib `StrictSegal.lean:265--325`
  and `Path.lean:282--299`: these concern individual simplices and bijective
  strict-Segal comparisons of one simplicial set, and do not state this result.
- Loogle, `SSet.spine`: twelve hits, including `SSet.spine`, its vertex and
  arrow formulas, `spine_map_subinterval`, and strict-Segal inverse formulas.
  None asserts this mapping-space restriction equivalence.
- Grep, `SegalIntervalCover|segal_interval_cover|intervalFace|spineEdge`, scoped
  to `AlgebraicTopology`: zero hits. Direct `rg` searches of Mathlib's
  simplicial-set subcomplex files, all upstream `WeilConjectures/`, the shared
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no duplicate owning
  declaration. The broader upstream `Rezk|Segal|bisimplicial|spine` search also
  returned no result. I checked the DAG sibling
  `lem-coef-segal-finite-cover-descent`: it has no Lean record and is a more
  general intersection-closed face-family statement, not an existing declaration
  of this item's theorem. Existing simplex maps and subobjects are reused.

Repairs: the old theorem docstring compressed the induction into a finite-cover
sentence and did not explain why the intersections are eligible. I replaced it
with all six DAG proof steps: mapping fibrations; boundary-lifting closure and
union gluing; the spine comparison; strong induction on ambient length with
singleton intersections removed; attachment pullbacks at strictly smaller
length; and two-out-of-three. It names each proof dependency where used.
I added explicit non-public imports of `KanQuillenRightProper` and
`ReedyModelStructure` for those recorded proof dependencies, and corrected the
cover docstring's duplicated `G_to_H` to `Subobject.arrow H`. The theorem's
signature and all mathematical definitions were already correct and are retained.
All definitions have real data, and the only postponed theorem is the item's
named theorem with `by sorry`; no theorem was proved and no hollow definition
was introduced. Every top-level declaration has its source/blueprint docstring.

Validation: the required `scompile.py NB lem-coef-segal-interval-cover` invocation
compiled the delivered file through both wrapper checks, with exit zero and no
warnings or errors (reported 1.4 s and 1.9 s). An exact comparison after the
signature reader's whitespace normalization confirms `lean.statement` matches
the file. All lines are at most 100 characters; `autoImplicit false`, explicit
`universe u`, and the closed signatures leave no unbound variable or universe.
