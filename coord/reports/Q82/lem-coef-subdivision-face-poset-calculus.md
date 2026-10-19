## Worker report

The module `Sheaf.AlgebraicTopology.SubdivisionFacePosetCalculus` states
`SSet.SubdivisionFacePoset.subdivision_face_poset_calculus`, with its only theorem
proof `sorry`. The seven helpers give concrete data for notions introduced in this
node: actual vertex support, downward closure of face collections, the resulting
subcomplex, canonical simplex coprojections and their cocone, image-of-faces maps,
and the induced map of subcomplexes. No new independent notion, dependency module,
other DAG statement, or statement correction is introduced.

Clause-by-clause correspondence:

1. A small simplicial set is `X : SSet.{u}`, exactly the recorded Mathlib
   definition. Simplicial maps are natural transformations. All degrees, including
   zero, use `SimplexCategory.mk n` (`⦋n⦌`) and its opposite.
2. The simplex category is `CostructuredArrow stdSimplex X`. An object is a
   standard simplex together with its map to X; a morphism is a simplex-category
   morphism with precisely the commuting triangle in the node. The diagram is
   `CostructuredArrow.proj stdSimplex X ⋙ SimplexCategory.sd`.
3. `SimplexCategory.sd` is Mathlib's nerve of `NonemptyFiniteChains` of the
   ulifted finite ordinal. In a linear order every subset is a chain, so this is
   exactly the nonempty-subset poset in the statement. Its maps use the existing
   `NonemptyFiniteChains.orderHomMap`, whose data are direct images of finsets.
4. `SSet.sd` is the existing left Kan extension of that diagram along standard
   simplices. `simplexInclusion σ` is `stdSimplex.sdIso.inv.app n ≫ sd.map σ`.
   `subdivisionCocone X` has exactly those coprojections. The first conjunct says
   this is a colimit, using `Nonempty (IsColimit ...)`. Presheaf colimits are
   computed degreewise, so this is the specified degreewise colimit construction;
   this uses the recorded colimit universal property, not a new Sd model.
5. `SSet.ex` is the existing restricted ULift Yoneda functor: its n-simplices
   are `ULift (SimplexCategory.sd.obj ⦋n⦌ ⟶ Y)`, and its operators are
   precomposition by direct image. ULift only packages the same hom-set.
6. The actual natural Hom bijection is the existing
   `sdExAdjunction.homEquiv X Y`. The second conjunct gives its exact evaluation:
   its value on `yonedaEquiv σ`, with ULift removed by `.down`, is
   `simplexInclusion σ ≫ f`. Its two naturalities belong to the existing
   adjunction; the theorem supplies the representative-level formula needed here.
7. `lastVertex : sd ⟶ 𝟭 SSet` and `j : 𝟭 SSet ⟶ ex` are natural
   transformations. Their components are transpose under that same Hom bijection.
   For every standard-simplex flag, `IsGreatest` says that its output vertex
   belongs to the nonempty subset and bounds every vertex in it. This uniquely
   specifies the maximum, without imposing a linear order on an arbitrary P.
   Naturality then makes every general component the map induced by simplexwise
   maxima. The next conjunct says exactly that `j` on σ is σ after that
   normalized standard-simplex last-vertex map.
8. The finite-poset hypotheses are `(P : Type u) [PartialOrder P] [Finite P]`.
   Faces are the existing `PartialOrder.NonemptyFiniteChains P`; a collection is
   `F : Set (NonemptyFiniteChains P)`. `IsFaceCollection F` is exactly closure
   under nonempty subsets (the order on chains is inclusion). There is no
   nonemptiness hypothesis on P or F and no chosen total order on P.
9. `support x` is `Finset.univ.image x.obj` with its actual nonempty chain data.
   `complex F hF` has membership `support x ∈ F`; thus it is exactly A in the
   node. Its operators are the restricted nerve operators, and the construction
   checks that restriction supports are subsets of the original support.
10. `e P F hF` is an isomorphism from `sd.obj (complex F hF).toSSet` to
    `nerve {c : NonemptyFiniteChains P // c ∈ F}`. The subtype inherits
    the inclusion partial order, as required for the face poset. The theorem
    chooses the entire family together, and characterizes each comparison on
    every representative `simplexInclusion σ` and every vertex of every flag:
    the resulting face finset is the image of the corresponding subset under
    the vertices of σ. Hence these are canonical comparisons, not arbitrary
    isomorphisms or arbitrarily chosen data definitions.
11. For each weakly increasing flag in the face nerve, the following
    `IsGreatest` conjunct evaluates `e.inv ≫ lastVertex.app A`, followed by
    inclusion in `nerve P`. Its i-th output is the maximum of the i-th face,
    exactly the node's `(max F₀, ..., max Fᵣ)` formula. Repeated faces are allowed.
12. For another finite poset Q, collection G and closure hG, the binder
    `(u : P →o Q) (hu : ∀ c ∈ F, c.map u ∈ G)` is exactly the monotonicity
    and admissible-face hypothesis. `complexMap hF hG u hu` is entrywise u;
    `facesMap u hu` is its genuine direct-image monotone map on face subtypes.
    The displayed naturality square identifies the subdivision map with the
    nerve of this image map, including u that collapses vertices.
13. Inclusions are covered by the same square with identity vertex map and
    F contained in G; inclusions into a larger vertex poset use its order
    embedding as u. No separate arbitrary inclusion map is assumed.
14. The final `eN` family explicitly states `Sd N(P) ≅ N(Ch(P))`, using the
    existing `NonemptyFiniteChains P`. Its representative formula fixes the
    canonical image-of-faces comparison, not merely its isomorphism class.
    This is the all-faces specialization of the preceding construction.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set`: `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`, `SSet.Subcomplex` and
  `.toSSet`/`.ι` in `...Subcomplex`. The node is a Mathlib leaf; its other
  clauses `degenerate`, `nonDegenerate`, and `Finite` were read in their
  recorded source modules. They are not needed for this statement's formulas.
- `def-cbc-enhanced-diagrams-cones`: imported its recorded module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. That source explicitly reuses
  Mathlib's `nerve` and `stdSimplex`; the full signatures/docstrings of those
  were read in `Mathlib.AlgebraicTopology.SimplicialSet.Nerve` and `.StdSimplex`.
  Thus ordinary nerve and standard simplex are those exact primitives, not
  replacements for the enhanced-category definitions.
- `def-weil-pbc-category-colimit`: `Cocone`/`IsColimit` and the chosen-colimit
  API from `Mathlib.CategoryTheory.Limits.HasLimits` and `.IsLimit`.
  `subdivisionCocone` uses the actual cocone; its universal property is stated
  directly. `SSet.sd`/`.ex`/`.sdExAdjunction`/`stdSimplex.sdIso` were read in
  `Mathlib.AlgebraicTopology.SimplicialSet.Subdivision`.

Source check: read online Kerodon [00Y8](https://kerodon.net/tag/00Y8),
[00Y9](https://kerodon.net/tag/00Y9), [00YL](https://kerodon.net/tag/00YL),
[00YM](https://kerodon.net/tag/00YM), [00YN](https://kerodon.net/tag/00YN), and
[00YU](https://kerodon.net/tag/00YU). The 00YJ request timed out; the node's
complete explicit ordered-complex proof and the successfully opened sources
suffice for the specialization. The theorem docstring preserves all fourteen
proof steps of the node. No source-based change to the node was necessary.

Edge cases checked: empty P, empty F on a nonempty P, singleton faces, dimension
zero, repeated entries and repeated faces, non-injective vertex maps, identity
maps and subcomplex inclusions, the full face collection, and arbitrary universe
u. With F empty, the subcomplex has no simplices, and the face subtype is empty;
no maximum of an empty face is ever invoked. For a non-injective u the image
finset removes repetitions, exactly as required. No finiteness requirement is
imposed on X or Y. IsGreatest is applied only to the node's nonempty faces.

Searches made before finalizing:

- `msearch.py ... grep "Subdivision|face poset|nonemptyFiniteChains"
  AlgebraicTopology`: seven hits, including the subdivision file and its
  nonempty-chain import. Read that entire file: its TODO explicitly leaves
  the general face comparison unimplemented.
- `msearch.py ... leanfinder "simplicial set subdivision Ex Sd face poset"`:
  eight hits about standard-simplex faces, horns and boundary; no full statement.
- `msearch.py ... loogle "SSet.sd, SSet.ex, SSet.sdExAdjunction"`: one hit,
  the existing adjunction. This is reused directly, and supplies only that part
  of the node.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for
  `subdivision|face.?poset|sdExAdjunction|lastVertex`, and the item id: no exact
  full statement. The downstream `ExInfinityFiniteProducts` module constructs
  `SSet.sdLastVertex` and `SSet.exLastVertexUnit`. Those definitions were read;
  this delivery does not copy them, define new versions of them, or import the
  downstream theorem. Its quantified natural transformations are instead fixed
  uniquely by their representative formulas, so downstream consumers can
  identify the already constructed transformations by those formulas.
- Exact full-name search for `SSet.SubdivisionFacePoset` and
  `subdivision_face_poset_calculus` in Mathlib/project/upstream names found no
  declaration collision. The only `support` hits use other namespaces/notions.

Validation: `scompile.py` compiles the finished module cleanly in both sandbox
and library-module modes. All universes and variables are bound explicitly;
there is no file-local notation/instance, no data containing sorry, and exactly
one postponed theorem matching this DAG node. Dry-run result is recorded after
running `deliver2.py --no-push`. The second reader, not this worker, supplies
its independent reading and pushes.


## Second reading by Q82

I independently read the sandbox node and the complete Lean module, the three
statement-dependency records and the declarations used from them. I checked the
online source before deciding whether any Lean repair was needed. The source is
Kerodon, not Stacks: [00YL](https://kerodon.net/tag/00YL),
[00Y9](https://kerodon.net/tag/00Y9), [00YM](https://kerodon.net/tag/00YM),
[00YN](https://kerodon.net/tag/00YN), and [00YU](https://kerodon.net/tag/00YU).
The direct 00YJ page timed out again, but its complete Example the project server is
available and was read in [the full subsection 00Y5](https://kerodon.net/tag/00Y5),
lines 71–72 of the web rendering. Thus the first worker's source-reading gap is
closed. I also read 00Y8 and 00YT for the subdivision existence and maximum
naturality. The braced hypothesis of 00YL is appropriate: the complexes here
are downward-closed ordered complexes in a poset nerve. It is not being
asserted that subdivision of an arbitrary simplicial set is a poset nerve.
The general simplicial sets occur only in the colimit/adjunction/last-vertex
clauses, which do not require that hypothesis.

My independent object/hypothesis/conclusion checklist follows. Each verdict is
that the Lean has the same mathematical content as the node.

1. **Small simplicial sets and simplices.** `X Y : SSet.{u}` are arbitrary
   small simplicial sets, and `σ : Δ[n] ⟶ X` is a simplex. I read the recorded
   Mathlib leaf `SSet := SimplicialObject (Type u)` in Basic.lean and the
   definition `stdSimplex := uliftYoneda` and `stdSimplex.objEquiv` in
   StdSimplex.lean. Operators are contravariant simplex maps, with no Kan,
   braced, finite or nonempty assumption on X or Y. Verdict: exact.
2. **The category of simplices and its diagram.** `subdivisionCocone X` is
   indexed by `CostructuredArrow stdSimplex X`. I read the actual
   `CostructuredArrow` definition and its `left`, `hom`, `Hom.left` and
   commuting-triangle convention. This has precisely objects `Δ[n] ⟶ X`
   and arrows α with `stdSimplex.map α ≫ τ = σ`. The diagram
   `CostructuredArrow.proj stdSimplex X ⋙ SimplexCategory.sd` uses those
   same arrows. Verdict: exact, including arrow direction.
3. **The nonempty-subset poset and subset images.** I read
   `SimplexCategory.sd := toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙
   PartOrd.nerveFunctor`, and `NonemptyFiniteChains`, its inclusion order,
   `map`, and `orderHomMap` in Order/NonemptyFiniteChains.lean. On the
   finite linear ordinal, every nonempty subset is a chain. The ULift of
   the ordinal changes its encoding only; maps really take finset images.
   Nerve simplices are weak flags, not strict flags. Verdict: exact.
4. **Degreewise colimit construction.** Mathlib's `sd` is the left Kan
   extension along the same standard-simplex functor. `simplexInclusion σ`
   is `stdSimplex.sdIso.inv.app n ≫ sd.map σ`; `subdivisionCocone X`
   packages precisely these maps. The first theorem conjunct is
   `∀ X, Nonempty (IsColimit (subdivisionCocone X))`. I read `IsColimit`
   (desc, factorization, uniqueness) in Limits/IsLimit.lean and the recorded
   colimit interface. This is the required colimit in simplicial sets;
   presheaf colimits compute it degreewise. `Nonempty` asserts its universal
   property without making a data definition out of a postponed theorem.
   Verdict: exact.
5. **Ex and the natural Hom bijection.** `ex` is the existing
   `Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd`; I read that
   definition and `restrictedULiftYonedaHomEquiv'` in Limits/Presheaf.lean.
   Its n-simplices are the specified Hom set, encoded by ULift, and its
   operators are precomposition. `sdExAdjunction.homEquiv X Y` is the actual
   bijection, already carrying both naturalities as an adjunction. The
   second conjunct identifies its exact value on `yonedaEquiv σ` after
   removing ULift with `.down`. Verdict: exact; no naturality is assumed
   separately or replaced by a mere unrelated bijection.
6. **Natural last-vertex maps.** The existential `lastVertex : sd ⟶ 𝟭 SSet`
   chooses a natural transformation. For every standard simplex, every
   degree r, flag t and vertex i, its normalized value is `IsGreatest`
   of the nonempty subset `(t.obj i).finset`, with ULift removed on vertices.
   This says both membership and greatestness, hence exactly maximum.
   Naturality with every `σ : Δ[n] ⟶ X` gives the node's induced map on
   arbitrary X. Verdict: exact, no maximum on an arbitrary whole poset.
7. **Transpose and the transition formula.** `j : 𝟭 SSet ⟶ ex` is natural;
   the next conjunct says it is the transpose of `lastVertex.app X` under
   that very `sdExAdjunction.homEquiv`. Its displayed value on σ is
   `simplexInclusion (𝟙 Δ[n]) ≫ lastVertex.app Δ[n] ≫ σ`. The initial
   inclusion is exactly the standard-simplex identification needed because
   the domain is `SimplexCategory.sd.obj ⦋n⦌`. Verdict: the node's
   `σ λ_{Δⁿ}`, with the same normalization and order of composition.
8. **Finite poset, faces and downward closure.** The binders are
   `(P : Type u) [PartialOrder P] [Finite P]`, followed by
   `F : Set (PartialOrder.NonemptyFiniteChains P)` and
   `hF : IsFaceCollection F`. The latter is closure under `b ≤ a`, where
   that order is nonempty-subset inclusion. There is no total-order,
   inhabitedness, decidable-equality or chosen-enumeration hypothesis.
   Verdict: exactly the node's finite poset and face collection.
9. **The actual ordered subcomplex A.** `support x` has finset
   `Finset.univ.image x.obj`, with nonemptiness and comparability proved
   from the nerve simplex data. `complex F hF` is the genuine subcomplex
   with membership `support x ∈ F`; its restriction proof uses the actual
   image of the simplex operator. I read Mathlib's `Subcomplex`, `toSSet`
   and `ι` in the recorded Subcomplex.lean. Verdict: exactly A, with its
   restricted operators, not an arbitrary simplicial set or private nerve.
10. **Canonical face-poset comparison.** The family `e P F hF` consists of
    isomorphisms `sd.obj (complex F hF).toSSet ≅ nerve {c // c ∈ F}`.
    The subtype inherits inclusion order. The first clause after e fixes
    its hom on every representative `simplexInclusion σ`: each face's
    finset is the image of the corresponding `(t.obj i).finset` under the
    actual vertices of `σ ≫ (complex F hF).ι`. These equations determine
    the canonical comparison, not only its isomorphism class. Verdict:
    exact; the simultaneous family has the node's natural compatibility.
11. **Maximum formula on flags of faces.** The next clause applies e.inv,
    then `lastVertex.app A`, then A's actual inclusion in `nerve P`.
    `IsGreatest (↑(t.obj i).val.finset : Set P)` gives precisely the i-th
    coordinate `max Fᵢ`. Every degree and every i is quantified. The
    finsets are nonempty chains, so this requires neither a linear order
    on P nor a maximum of an empty set. Verdict: exact.
12. **Image-of-faces functoriality.** The additional finite poset Q, G and
    hG use the same notions. `(u : P →o Q)` supplies just monotonicity;
    `hu : ∀ c ∈ F, c.map u ∈ G` is precisely admissibility of every face.
    `complexMap hF hG u hu` applies u entrywise and checks its image
    support; `facesMap u hu` applies the genuine direct-image chain map
    on the face subtypes. The equation
    `sd.map (complexMap ...) ≫ (e Q G hG).hom =
    (e P F hF).hom ≫ nerveMap (facesMap ...).monotone.functor`
    is the required square. Verdict: exact, also when u identifies vertices.
13. **Inclusions and empty complexes.** Subcomplex inclusions are instances
    of that same square with the identity vertex map and F ⊆ G; inclusion
    of vertex posets is included by the corresponding order embedding.
    There is no nonempty assumption anywhere on P or F. Verdict: these
    clauses really follow with the node's canonical inclusion maps.
14. **The full-nerve specialization.** `eN` has precisely the type
    `∀ P [PartialOrder P] [Finite P], sd.obj (nerve P) ≅
    nerve (PartialOrder.NonemptyFiniteChains P)`. Its representative formula
    imposes the same direct-image normalization as e. Taking F to be all
    chains gives the node's full-nerve statement; no extraneous property
    or arbitrary alternative comparison is asserted. Verdict: exact.

Edge-case review: P empty and F empty give empty types of simplices and empty
face nerves in every degree. F may also be empty on an inhabited P. A singleton
face and n = 0 use Fin 1 and have the expected unique maximum. Repeated vertices
of σ and repeated faces of t are allowed: nerve flags are weakly increasing,
and finset image removes repetitions. A constant monotone u is allowed whenever
hu holds. Identities and inclusions use the same formulas. The full face
collection gives N(P). Universe u is arbitrary; all objects compared in a map
are in the fixed common universe, with the standard simplex lifted to it. There
are no coefficients, schemes, zero-object assumptions or characteristic cases
in this node. No edge case from the node is excluded.

Independent H4 searches (in addition to opening the actual definitions above):

- `msearch.py Q82 ... leanfinder "subdivision face poset calculus"` returned
  eight standard-simplex face/horn and simplex-description hits; none states
  the general comparison.
- `msearch.py Q82 ... grep "facePoset|barycentric|nondegenerate.*subdivision"
  AlgebraicTopology` returned zero hits.
- `msearch.py Q82 ... loogle "SSet.stdSimplex.sdIso"` returned the standard
  simplex comparison and its left-Kan-extension instance only. I read the
  entire Subdivision.lean; its TODO explicitly leaves the general
  nerve-of-nondegenerate-faces comparison open.
- `msearch.py Q82 ... leansearch "Subdivision of a poset nerve is canonically
  the nerve of nonempty chain supports"` returned generic nerves, arbitrary
  `NonemptyChain`, and descriptions of nondegenerate nerve simplices.
  `NonemptyChain` is an arbitrary possibly infinite chain and is not the
  finite-face notion used here. None gives this theorem or the helpers.
- I separately ran rg over Mathlib's simplicial-set directory, the complete
  upstream `WeilConjectures` tree, project `lean/Sheaf`, and the recorded
  upstream names, using `barycentric`, `subdivision`, `face.?poset`,
  `lastVertex`, `IsFaceCollection`, `simplexInclusion`, `support`, and
  `Finset.univ.image`. There is no full-statement match or name collision.
  I opened the project's `ExInfinityFiniteProducts.lean`: its concrete
  standard-simplex `sdLastVertex` and `exLastVertexUnit` use the same maximum
  convention. This delivery introduces no duplicate definitions of them:
  its existential transformations are fixed by the evaluation formulas.
  The seven helpers encode objects and maps introduced in this node and
  have no existing same-notion declaration in the searched sources.

No new node, dependency module, statement correction, or repair note for this
item is present, so H12/H13 and the correction-specific citer audit do not
arise. The three dependencies have usable interfaces; no replacement was
needed. I checked the seven helper definitions' real data and their internal
structure-law proofs: no sorry or choice from a postponed existence theorem
occurs in any of them. The only postponed theorem is the named item theorem,
with all fourteen proof steps in its docstring. Source places and the exact
blueprint id appear in every declaration docstring and the module header.
There is no private declaration, file-local notation or local instance; every
variable and universe is explicitly bound, and all Lean lines are at most
100 characters. The node's lean.statement was checked verbatim against the
file's theorem signature.

Mismatches found: none in the Lean statement or the dependency interfaces.
Changes made: this independent second-reading report only; the correct Lean
module and its node record are unchanged. The source check above closes the
worker report's 00YJ retrieval gap.

Validation: independently ran the prescribed `scompile.py Q82
lem-coef-subdivision-face-poset-calculus
lean/Sheaf/AlgebraicTopology/SubdivisionFacePosetCalculus.lean`. Both sandbox
and library-module compilation completed cleanly (1.5 s and 1.6 s), with no
errors or warnings. Delivery dry run and final push follow this reading.
