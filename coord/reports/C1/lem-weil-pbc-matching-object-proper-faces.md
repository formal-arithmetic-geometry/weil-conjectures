## Worker report

The module `Sheaf.CategoryTheory.ProperFaceMatchingObject` states the three clauses of
`lem-weil-pbc-matching-object-proper-faces`, in degree one and in every degree `n + 2`.
Both theorem proofs are `sorry`; the four definitions are fully specified, with no `sorry`.
The index category and diagram are objects explicitly introduced in the item's own statement,
so their constructions belong to this node, just as the dependency's boundary diagram does.
There are no new nodes, dependency replacements, or changes to the informal statement.

Source checked: https://stacks.math.columbia.edu/tag/0186, statement and full proof. The local
literature file is unavailable on this machine. The source uses all maps; restricting to
injective maps preserves its missing-vertex and double-missing-vertex factorization argument.

Hypotheses and objects:

- The category is `C : Type u` with `[Category.{v} C]`; both universes are explicit and independent.
- Finite limits are the existing `[HasFiniteLimits C]`.
- The simplicial object is the existing `K : SimplicialObject C`; its operators are `K.map ε.op`.
- Degree `n ≥ 1` is covered exhaustively by `matching_object_proper_faces_one` and
  `matching_object_proper_faces_succ_succ`, whose degree is `n + 2` for any `n : ℕ`.
- `properFaceProperty n` requires `a.left.len < n` and injectivity of `a.hom.toOrderHom`
  for `a : Over ⦋n⦌`. Thus the source length `k` is nonnegative automatically, and precisely
  `0 ≤ k < n`. `ProperFaceCategory` is the full subcategory selected by this property.
  Its arrows are order-preserving maps with `ε ≫ δ = δ'`, exactly the stipulated triangles;
  no extra injectivity hypothesis on arrows is imposed.
- `properFaceDiagram K n` is the opposite of the inclusion followed by `Over.forget`,
  composed with `K`. It sends a face to `K.obj (op a.obj.left)` and an arrow to `K.map ε.op`.
- `properFace n i` is `Over.mk (SimplexCategory.δ i)`, with its properness and injectivity
  supplied by existing Mathlib results. It is precisely the increasing injection omitting `i`.
- The objects called `M_n`, `pr_i`, and `μ_n` are bound as a boundary cone `c`, its projections,
  and a morphism `μ` with the face-component equations. `hc : IsLimit c` states the assumed
  meaning of matching object; `hμ` states the assumed meaning of its matching morphism.
  These specify the objects already introduced by “let M_n ... and μ_n be ...” in the node,
  and do not impose further conditions on `K` or on the ambient category. The dependency
  supplies such a cone and map. Quantifying over every such choice avoids a private definition.

Clauses:

1. A compatible family with vertex `W` is a natural transformation
   `(Functor.const _).obj W ⟶ properFaceDiagram K degree`. Its naturality equation is exactly
   `x_δ ≫ K.map ε.op = x_(δ∘ε)` in Lean's composition order. `E W` is an equivalence to
   face tuples; the first equation says it is exactly restriction to `properFace ... i`.
   In degree one the target is an arbitrary pair. For degree `n + 2` it is the subtype
   whose pair equations are `x i ≫ d_(j-1) = x j ≫ d_i`, using precisely the dependency's
   `matchingBoundaryShape` and `matchingBoundaryIndex`. The next equation states naturality
   under every `f : W' ⟶ W`, component by component; this is equality of tuples by extensionality.
2. `π` is a natural transformation with vertex exactly `c.pt`, so `Cone.mk c.pt π` is the
   proper-face cone on the same matching object. `Nonempty (IsLimit ...)` says it is limiting.
   For every proper face `a`, index `i`, and factor `ε` satisfying
   `ε ≫ SimplexCategory.δ i = a.obj.hom`, its component equals
   `pr_i ≫ K.map ε.op`. The quantifier ranges over every factorization, so each gives the
   same `π.app (op a)`, which is precisely independence of factorization. Every proper
   face has such a factorization by the node's first proof step. This does not require a
   choice-dependent definition or an additional existence assertion in the conclusion.
3. For every proper face `a`, `μ ≫ π.app (op a) = K.map a.obj.hom.op` states the component
   identity. The following universal implication says every `μ'` with these same components
   equals `μ`. Together these are exactly the specified existence and uniqueness.

Dependency declarations read and used:

- `def-galois-finite-limits-colimits`: Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits,
  `CategoryTheory.Limits.HasFiniteLimits` (full class/docstring read). No finite-colimit
  hypothesis is imposed because the item only asks for finite limits.
- `def-weil-pbc-simplicial-object`: Mathlib.AlgebraicTopology.SimplicialObject.Basic,
  `CategoryTheory.SimplicialObject`, `.δ`, and the existing functor map; their signatures
  and docstrings were read. Degeneracy maps are part of `K` but need no additional binder.
- `lem-weil-pbc-simplicial-matching-object`: Sheaf.CategoryTheory.SimplicialMatchingObject,
  `matchingBoundaryShape`, `matchingBoundaryIndex`, `matching_object_one`, and
  `matching_object_succ_succ`; the full module was read. The first two define the diagram
  used by the latter theorem and this module. The latter two supply the choices represented
  by `c`, `hc`, `μ`, and `hμ`; the theorem works for any such choices.

Edge cases: degree one has two vertices and no compatibility condition, exactly as stated
by the matching-object dependency and the item's proof. Degree two uses pairs of three
faces and maps to degree zero. The source category contains no empty ordinal and excludes
both the identity face and degeneracies as objects. General arrows need not be separately
restricted: their composites into injective faces force injectivity. Arbitrary `W`, empty
or zero objects when the category has them, and all object/hom universes are retained.
No disputed statement or correction was needed; the degree-one convention is explicit
in the dependency and the item's proof.

Searches for an existing declaration:

- `msearch.py leanfinder`: “matching object simplicial object limit over all proper injective
  faces”: eight hits, including `cechNerveTerminalFrom`, splitting indices, and standard
  simplices; none states this theorem or defines this proper-face diagram.
- `msearch.py loogle`: “SimplicialObject, Cone”: no hits, unknown identifier `SimplicialObject`.
- `msearch.py grep`: “matching.?object|properFace”, in AlgebraicTopology: no hits.
- `msearch.py leansearch`: “simplicial matching object limit over injective proper faces”:
  service unavailable (Internal Server Error), recorded as unavailable.
- `rg` in WeilConjectures and lean/Sheaf, both by this node id and by `properFace` /
  `matching_object_proper`, and subsequent exact declaration-name searches also including
  Mathlib: no matches. `dag/lean_names_upstream.json` contains no record for this node id.
  The existing general full-subcategory, over-category, simplex, and natural-transformation
  machinery is reused, rather than reconstructed.

Validation: the complete module compiled on the server via the prescribed `scompile.py`
under the default timeout, with exit code zero and no warnings. The delivery dry run is
run after writing this report. The independent second reading remains for the next worker.

## Second reading by C1

Independent reading of the sandbox node and the entire module, alongside all three
statement dependencies and their declarations. Verdict: the two theorem signatures
jointly render the node exactly; no mathematical or Lean repair is needed. Only this
second-reading report was added. The worker report remains intact.

Source: the local Stacks checkout is absent, so I read the actual `simplicial.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/simplicial.tex,
`lemma-formula-limit`, its complete proof and the preceding discussion, and checked
https://stacks.math.columbia.edu/tag/0186. The source uses a truncated simplicial object
and all maps into the next ordinal; the node explicitly requests the injective restriction
for a full simplicial object. Its factorization proof applies to this restriction: every
proper injection misses a vertex, and factors through its omission; if two vertices are
missing, the factors through their simultaneous omission remain injective. The preceding
text adds no ring, scheme, characteristic, or smallness hypothesis. The degree-one case
is the discrete pair, as explicitly specified by the dependency and step 2 of this node.

Object/hypothesis/conclusion checklist (node first, then Lean rendering and verdict):

1. Ambient category with finite limits: `{C : Type u} [Category.{v} C]
   [HasFiniteLimits C]` in both theorems. Exact. Read the Mathlib finite-limits class,
   including its extension from finite small categories to other index universes; finite
   colimits are not assumed.
2. Simplicial object, degree terms, operators and faces: `(K : SimplicialObject C)`,
   `K _⦋m⦌`, `K.map ε.op` and `K.δ i`. Exact. Read Mathlib's `SimplicialObject` and
   face declaration: it is precisely `SimplexCategoryᵒᵖ ⥤ C`, and faces map the ordinal
   injection omitting the specified index.
3. Degree `n ≥ 1`: the theorem `_one` covers 1; `_succ_succ` takes arbitrary `(n : ℕ)`
   and covers `n + 2`. Exact, exhaustive, without an upper bound.
4. Proper-face objects `δ : [k] → [n]`, `0 ≤ k < n`, injective and increasing:
   `properFaceProperty` is `a.left.len < n ∧ Function.Injective a.hom.toOrderHom` on
   `Over ⦋n⦌`. Exact. Ordinal length is a natural number, so the lower bound is automatic.
5. Commuting-triangle morphisms: `ProperFaceCategory` is the property's full subcategory
   of `Over ⦋n⦌`. Exact. Read `FullSubcategory.category`, its inclusion and `Over.Hom`,
   `Over.Hom.left`, `Over.w`: the equation is `ε ≫ δ = δ'`, in the specified direction.
   No arrow restriction is added; its injectivity follows from that of its composite.
6. Diagram `P_n(K)`: `properFaceDiagram` is the opposite of inclusion followed by
   `Over.forget`, then composed with `K`. Exact on both objects and arrows; taking the
   opposite gives `K(ε) : K_k → K_k'` in the required direction.
7. Codimension-one faces: `properFace m i` is `Over.mk (SimplexCategory.δ i)` with
   the strict-length and injectivity evidence. Exact, using the existing mono instance
   and `mono_iff_injective`; neither an unknown object nor a new notion of face.
8. Matching object, projections and map: `c : Fan ...` in degree one, respectively
   `c : Cone (matchingBoundaryIndex K n).multicospan`; `hc : IsLimit c`, vertex `c.pt`,
   `c.proj i` or `c.π.app (WalkingMulticospan.left i)`, and `μ` with `hμ` fixing its
   face components. Exact descriptions of the objects introduced by the node's “let”.
   These are not extra conditions on `K`: the dependency's `matching_object_one` and
   `matching_object_succ_succ` supply them. I read that complete module and the dependency
   node: its `matchingBoundaryShape` has precisely pairs `i < j`, and its `fst` is
   `K.δ (j.pred ...)`, its `snd` is `K.δ (i.castLT ...)`, hence exactly `d_(j-1)` and `d_i`.
9. Clause (1), compatible families: natural transformations from the constant functor
   at `W` to `properFaceDiagram` express every component and precisely the triangle
   compatibility. Exact; naturality has no additional mathematical constraints.
10. Clause (1), bijective restriction to tuples: `∃ E : ∀ W, ... ≃ ...`, with the
    equation identifying each output with `x.app (op (properFace ... i))`. Exact.
    Degree one has arbitrary pairs; higher degrees use the dependency's subtype of
    all pair equations. The following equality under every `f : W' ⟶ W` expresses
    naturality componentwise and therefore for the whole tuple. Quantifiers agree.
11. Clause (2), all factorizations give the same component: the single transformation
    `π` has, for every `a`, `i`, and `ε` with `ε ≫ δ i = a.obj.hom`, the component
    `c.proj i ≫ K.map ε.op` (or the boundary projection version). Exact. Equality to
    this same component proves independence of every factorization. There always is
    a factorization, by step 1; its absence is not being assumed as a hypothesis.
12. Clause (2), limit cone on the same object: `Nonempty (IsLimit (Cone.mk c.pt π))`.
    Exact, with vertex literally the original matching object's vertex.
13. Clause (3), matching-map components and uniqueness: `∀ a, μ ≫ π.app (op a) =
    K.map a.obj.hom.op`, followed by `∀ μ', (∀ a, ...) → μ' = μ`. Exact. The prescribed
    map is already introduced and supplied by the dependency; its component equations
    and uniqueness are both asserted, not just existence of an unrelated map.

Edge cases: degree 1 has exactly two vertex faces and only identity arrows; it imposes
no nonexistent face equations into degree -1. Degree 2 (higher theorem at parameter 0)
has three edges, three vertices and all three pair equations. Degree 0 is excluded by
the node itself, not by the formalization. `ProperFaceCategory 0` is nevertheless the
empty category, since no length is less than 0. Empty ordinals are not in the source's
simplex category; identity and degeneracy maps are correctly excluded as proper-face
objects. Zero objects or empty schemes, if present in `C`, and arbitrary vertices `W`
remain allowed. Object and hom universes `u`, `v` are independent and explicit; this
fixed finite index imposes no limit-index universe restriction. Characteristic is
irrelevant and none is assumed.

Independent searches used different terms from the worker:

- LeanFinder: “simplicial boundary matching limit diagram of non-surjective injections”.
  Eight hits, including `SSet.boundary`, `boundary_eq_iSup`, splitting indices and horn
  multicoequalizers. These concern simplicial sets or other diagrams, not the requested
  arbitrary-category proper-face matching limit.
- Loogle: `SimplexCategory.δ`. Twelve hits, including its signature, mono instance,
  `eq_δ_of_mono` and face/degeneracy identities. These supply existing ordinal notions,
  not the statement or its proper-face category.
- LeanSearch: “compatible face families simplicial matching object boundary limit”.
  Unavailable (Internal Server Error); no positive or negative verdict inferred.
- `msearch.py grep`: `matching.?object|proper.?face|face.*limit`. Five unrelated hits.
  Direct `rg` over Mathlib's simplicial-object and simplex-category sources, the full
  `WeilConjectures` source, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  with matching-object, proper-face, coskeleton and non-surjectivity terms found no
  duplicate of this definition or statement. I also opened the nearby project module
  `CoskeletonMatchingTuples`: it concerns all truncated simplex maps and a right Kan
  extension, not injective proper faces or this boundary-cone identification.

No new definition nodes or dependency replacement modules are present or required:
the four small constructions specify the index objects and diagram explicitly introduced
by this very node and reuse Mathlib's existing over/full-subcategory/functor machinery.
No statement correction is present or needed, so no correction-citer audit applies.
Every declaration has its source and blueprint docstring; both theorem docstrings carry
the node's factorization, compatibility, inverse/naturality, limit and uniqueness proof
steps. The definitions contain no `sorry`; the only theorem proofs remain `sorry`, as
stage 2 requires. Imports all supply notions used here. There is no file-local notation,
private copy, unbound variable, or extra instance; all lines meet the 100-character limit.
The node's `lean.statement` was compared directly with the main theorem's signature and
is verbatim identical. The prescribed `scompile.py` compiled the entire delivery cleanly
(exit 0, 1.2 seconds), without errors or warnings. Dry run and push follow this reading.
