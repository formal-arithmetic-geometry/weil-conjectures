## Worker report

Module `Sheaf.Paper.SiteHypercoverFiniteExtension` states
`CategoryTheory.FormalSplitAttachment.exists_split_truncated_extension`.
All helper declarations are in `lean.declarations`; they unpack the explicit
conditions already introduced in this node, rather than introduce an independent
mathematical notion. There is one postponed theorem, with the node's full
construction and composition argument in its docstring. All definitions have
actual data and contain no postponed proofs.

Hypotheses, in the order of the node:

- An arbitrary category D: `{D : Type u} [Category.{v} D]` in the surrounding
  variable declaration; u, v, w are explicitly declared universes. Finite limits:
  `[HasFiniteLimits D]`. The index universe w is independent of both categorical
  universes, so families indexed by any set are allowed.
- n≥0: `{n : ℕ}` in the surrounding declaration. No positivity assumption.
- The n-truncated object K: `SimplicialObject.Truncated (FormalCoproduct.{w} D) n`.
  `term K q` is precisely its degree-q formal family, with indices `(term K q).I`.
- All old indices finite: `hfinite : ∀ q : Fin (n + 1), Finite (term K q).I`.
- The nondegenerate subset N_q is defined intrinsically by `IsNondegenerate`:
  the negation of membership in any image of an epimorphism from a strictly
  lower degree. `Epi` in SimplexCategory is precisely surjectivity.
- The split bijection: the first conjunct of `hsplit : IsSplit K` says
  `Function.Bijective (labelIndex K q)`. `Labels K q.val` consists of triples
  (r, surjection [q]→[r], nondegenerate index of K_r). It allows every retained r;
  an epimorphism automatically forces r≤q, so this is exactly the node's range.
- Component isomorphisms: the second conjunct of `IsSplit` is
  `IsIso ((operator K a.2.1.val).φ a.2.2.val)` for every normalized label.
- M is the boundary limit: `c : BoundaryCone K M`, `hc : IsMatching K c`.
  `BoundaryCone.projection` runs over all [q]→[n+1], q≤n, and its naturality
  expresses compatibility of the lower projections. `IsMatching` is the
  unique-lifting universal property, tested on every formal family T. This is an
  equivalent presentation of exactly the finite boundary diagram in the node:
  every such ordinal map omits a value and factors through its codimension-one
  face; choices of missing value are identified by the pairwise face-overlap
  equations. Conversely those overlap equations are instances of naturality.
  Thus no coskeleton existence assumption or chosen arbitrary boundary is added.
  In n=0 it is exactly the two projections of a binary product, with no overlaps.
- The arbitrary finite new family and its boundary map:
  `(V : FormalCoproduct.{w} D) [Finite V.I] (v : V ⟶ M)`.

Conclusion, clause by clause:

- `L : SimplicialObject.Truncated ... (n + 1)` is an actual functor retaining all
  operators (including nonidentity endomorphisms), not just a collection of faces.
- `e : (SimplicialObject.Truncated.trunc ...).obj L = K` gives literal agreement
  with K in all old degrees and on all old operators, not only an isomorphism.
- `t : attachedFamily K V = term L ...` gives the displayed new-degree family
  literally: indices `V.I ⊕ Labels K (n + 1)` and object V_j or U_{r,i} as
  appropriate. It is equality of formal families, not just of their cardinalities.
- `IsSplit L` gives the same explicit split condition on the extension.
- The next conjunct `∀ q : Fin (n + 2), Finite (term L q).I` is finiteness in
  every degree of L.
- The next equivalence says an index x in degree n+1 is nondegenerate iff it is
  the image of `Sum.inl j` for some j in V.I, using the transport `eqToHom t`.
  Since t is equality of families, this identifies precisely the J summand.
- The universal boundary morphism is b. Its projection equality for every α
  says `b ≫ c.projection q α` is exactly the L-operator followed by the old-degree
  equality transport `(eqToHom e).app ...`. In particular the codimension-one
  projections are the face maps, so b is exactly L's boundary map.
- `newInclusion K V ≫ eqToHom t ≫ b = v` is its restriction to V.
- The final conjunct says, for every old label a=(r,σ,i) and every face δ_i,
  `oldInclusion ... ≫ eqToHom t ≫ operator L δ_i ≫ (eqToHom e).app ...`
  equals the singleton inclusion of U_{r,i} followed by `operator K (δ_i ≫ σ)`.
  Composition in SimplexCategory uses diagrammatic order, so `δ_i ≫ σ`
  is precisely σ∘δ_i from the node. Equality is in FormalCoproduct D, hence
  includes both the index function and the component morphism.

Dependency declarations used:

- `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits`:
  `CategoryTheory.Limits.HasFiniteLimits` (full signature and docstring read).
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject.Truncated`, `Truncated.trunc`, and
  `SimplexCategory.Truncated.Hom.tr` (recorded simplicial-coskeleton match).
- `Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic`:
  `CategoryTheory.Limits.FormalCoproduct`, `.Hom.f`, `.Hom.φ`, `.incl`,
  `.Hom.fromIncl`, and the recorded category instance (full signatures and
  documentation read). The same dependency nodes are also the only proof
  dependencies, so no further proof-only import is needed.

Edge cases checked:

- n=0: no lower degeneracies in K_0; normalized old labels in new degree are
  just K_0, and attachedFamily is V ⨿ K_0. The boundary is K_0×K_0.
- n=1: the old labels are one copy of N_0 and two copies of N_1, giving
  V ⨿ N_0 ⨿ N_1 ⨿ N_1. They are not incorrectly counted as three objects.
- Empty V, empty old families, empty component objects and empty new index sets
  use the same subtype/sigma/sum definitions, with no nonemptiness assumptions.
- Every retained degree is indexed by Fin(n+1) or Fin(n+2), including the top
  and degree zero. No universe equality or lower universe of test objects is
  imposed. The universal property quantifies over the same formal-family category.

Searches performed:

- msearch leanfinder: “Extend a split truncated simplicial object by adjoining
  nondegenerate simplices with prescribed boundary”: 8 hits, including truncation,
  sk, Truncated.trunc, and cosk; no prescribed-boundary split attachment theorem.
- msearch loogle: `CategoryTheory.SimplicialObject.Splitting`: 12 hits for full
  simplicial-object Splitting, its cofan, and transport. The full-object
  Splitting requires degrees above n and cannot encode this truncated hypothesis.
- msearch grep `split.*trunc|trunc.*split` in AlgebraicTopology: 0 hits.
- msearch leansearch: “Extending split truncated simplicial objects by adding
  prescribed nondegenerate simplices”: service unavailable, Internal Server Error.
- rg in Mathlib's SimplicialObject/Split.lean found the full-object `Splitting`
  structure; its source was inspected. No truncated interface was found.
- rg in the upstream WeilConjectures tree and project lean/Sheaf for
  FormalCoproduct, Truncated, hypercover, this node id, and the proposed names:
  existing étale hypercover structures concern schemes rather than an arbitrary
  category D and do not state the attachment theorem. No duplicate declaration.
- rg in dag/nodes for split truncations/nondegenerate indices/boundary diagrams:
  the existing étale finite-split-hypercover and full simplicial matching nodes
  do not introduce this arbitrary-category truncated attachment. They were
  inspected; the owning-node helpers unpack this node's own explicit conditions.

Source inspected locally: hypercovering.tex, lemma-split (0DAU) and
lemma-hypercovering-object (0DAV), including construction of the extension.
No statement correction or disputed statement is needed.

Validation: scompile.py reports a clean server compilation, nice 19, two threads,
60-second per-file limit; no local compiler was run. The delivery remains for an
independent second reader.


## Second reading by NS

Independent second reading against the repository node, the sandbox node and module,
Stacks hypercovering.tex `lemma-split` (0DAU) and the entire construction in
`lemma-hypercovering-object` (0DAV). I also read the three dependency nodes and their
recorded Mathlib declarations, rather than relying on the first reader's report.
The categorical attachment is the portion of 0DAV after passing to the slice with
finite limits and before the covering assertions. No site topology, basis membership,
or covering hypothesis belongs to this extracted categorical statement.

Object/hypothesis/conclusion inventory and verdicts:

1. Category D with finite limits: `{D : Type u} [Category.{v} D]` and
   `[HasFiniteLimits D]`. Exactly the node's arbitrary category and hypothesis.
   Mathlib `HasFiniteLimits` quantifies over finite categories; its size-transfer
   instance covers finite indexing categories in other universes. PASS.
2. Nonnegative n: the surrounding `{n : ℕ}`. Includes zero. PASS.
3. K, an n-truncated simplicial formal family: `K : SimplicialObject.Truncated
   (FormalCoproduct.{w} D) n`. Mathlib `Truncated` is the functor category on the
   opposite of the full simplex subcategory of lengths at most n. `term K q`
   gives K_q, and its `.I` and `.obj` give I_q and U_q,i. `operator` applies K
   to the opposite of the same ordinal map, with no missing operators. PASS.
4. Each I_q finite: `hfinite : ∀ q : Fin (n + 1), Finite (term K q).I`.
   No choice of enumeration or bound on cardinalities is required. PASS.
5. N_q is the complement of all lower surjective degeneracy images:
   `IsNondegenerate K q i` negates an existential over r<q, σ, and j with
   `(operator K σ).f j = i`. Mathlib `SimplexCategory.epi_iff_surjective`
   confirms that `Epi σ` means exactly surjectivity. PASS.
6. Explicit splitting: `Labels K q.val` is the sigma type of r, surjective σ,
   and i in N_r; `labelIndex` sends it to K(σ)(i). An epi implies r≤q, so
   ranging over all retained r adds no labels. The first conjunct of `IsSplit`
   is precisely bijectivity and the second is `IsIso` of every corresponding
   component `.φ`. This is 0DAU's split convention, not a chosen arbitrary
   decomposition. PASS.
7. Boundary limit M: `{M : FormalCoproduct.{w} D}`, `c : BoundaryCone K M`,
   `hc : IsMatching K c`. This presents the same limit as the node, with all
   lower-simplex projections instead of only the top faces and their overlaps.
   To check equivalence, restrict a BoundaryCone to the injections δ_a and to
   the injections omitting a<b; naturality gives exactly
   d_(b-1) p_a = d_a p_b. Conversely, for α:[q]→[n+1], choose a missing a,
   write α=δ_a β, and set p_α=p_a followed by K(β). If a second value b is
   missing, α factors through the injection omitting both; the displayed
   overlap equation makes the two definitions equal. Further precomposition
   preserves a missing value, giving all naturality equations. These operations
   are inverse on cones and preserve their mediating arrows. `IsMatching`
   tests the unique factorization on every object T of the same formal-family
   category. Thus it neither adds a coskeleton assumption nor changes M. PASS.
8. Arbitrary finite V and boundary map v: `V : FormalCoproduct.{w} D`,
   `[Finite V.I]`, `v : V ⟶ M`. Exactly the node's J and its specified arrow. PASS.
9. Existence of the extended simplicial object: the existential L is an actual
   `(n+1)`-truncated functor. The equality e with `Truncated.trunc ... .obj L`
   identifies its entire old functor with K, including all old maps. PASS.
10. Displayed top family: equality t identifies `term L` in degree n+1 with
    `attachedFamily K V`, whose indices are `V.I ⊕ Labels K (n+1)` and whose
    objects are V_j or U_r,i. This is the stated family, with no replacement
    of components by merely isomorphic or arbitrary objects. PASS.
11. Splitness and finiteness of L: `IsSplit L` and the following quantified
    `Finite` conjunct cover every retained degree. PASS.
12. New nondegenerate indices precisely J: the equivalence for every top index x
    says `IsNondegenerate ... x` iff x is `(eqToHom t).f (Sum.inl j)` for some j.
    Equality transport identifies J with its actual summand in L. PASS.
13. Boundary arrow and prescribed new faces: existential b followed by the
    projection equations identifies b with the canonical boundary cone of L,
    transporting the lower terms through `(eqToHom e).app`. The next equality
    `newInclusion K V ≫ eqToHom t ≫ b = v` is exactly its restriction to V. PASS.
14. Old summand face formula: the last equality ranges over every normalized
    label a and every `i : Fin (n+2)`. Its left side is the inclusion of U_r,j
    followed by the i-th L face and the old-degree transport. Its right side
    is the singleton inclusion followed by `operator K (δ i ≫ σ)`.
    Diagrammatic composition here is σ∘δ_i, as required. FormalCoproduct
    morphism equality includes both the index function and component arrows.
    Mathlib δ is `Fin.succAboveOrderEmb`, hence omits exactly i. PASS.

Dependency/interface and definition audit:

- Read Mathlib FormalCoproducts/Basic.lean: the family structure, Hom.f, Hom.φ,
  category composition, incl and Hom.fromIncl are exactly the SR(D) dependency.
- Read SimplicialObject/Basic.lean: Truncated and trunc are the recorded
  coskeleton dependency's restriction interface; no right Kan extension
  instances are required by this formulation.
- All twelve helpers are explicit unpackings or constructors for the data
  already specified by this node. BoundaryCone has actual projection/naturality
  fields; IsMatching states the actual universal property. No hidden choice,
  hollow data, private notion or duplicate dependency construction occurs.
  There are no new nodes or repaired dependency modules in this delivery.
- Every declaration has its owning source/blueprint docstring. The theorem's
  proof docstring follows the node's four stages: split normalization and finite
  labels; compatible boundary projections; operators by image factorization;
  composition by normalization/cancellation, transport, splitness and finiteness.
  The sole postponed proof is the named theorem, whose body is `sorry`.
  Universes u,v,w and all variables are bound; no local notation or instances
  are needed outside the module. The recorded lean.statement was compared
  programmatically with the file signature and agrees verbatim.

Edge cases independently checked:

- n=0: N_0=I_0; the boundary cone has exactly two projections and identity
  naturality, so M=K_0×K_0; the attached family is V plus one copy of K_0.
  There is no pairwise-overlap condition and no omitted n=-1 term.
- n=1: old labels in degree two give one copy of N_0 and two copies of N_1,
  not three copies of K_1. All nonidentity top endomorphisms are included
  because L is a functor on the full truncated simplex category.
- Empty V, empty old index types and zero/initial component objects are allowed.
  No Nonempty assumption appears. If all old families are empty, a boundary map
  may force V empty; the theorem imposes only the original existence of that map.
- D is not specialized to schemes or modules. Empty schemes and zero objects
  remain permitted whenever they occur as components of such a D. There is no
  characteristic restriction. Index universe w, object universe u and morphism
  universe v are independent; all test T range over the same SR(D), with no
  artificially smaller testing universe.

Independent duplicate searches (2026-10-15):

- msearch leanfinder: "Finite split simplicial skeleton extension with prescribed
  matching morphism" returned eight simplicial-set skeleton results, including
  SSet.skeleton_succ; none is a formal-family truncated attachment theorem.
- msearch loogle: `"SimplicialObject.Truncated"` returned Truncated, restriction,
  coskeleton and related instances; no split attachment theorem.
- msearch leansearch: "Adjoin nondegenerate simplices to a truncated simplicial
  family along a matching object" was unavailable (Internal Server Error).
- Independent rg on Mathlib AlgebraicTopology, upstream WeilConjectures and
  project lean/Sheaf used matching/extension, prescribed boundary, adjoining,
  attachment and truncated/split variants, as well as the actual helper names.
  No existing theorem or general truncated-family split predicate was found.
  I opened Mathlib's `SimplicialObject.Splitting`: its argument is a full
  simplicial object and it requires N in every degree, so it cannot render this
  truncated hypothesis. I also opened the project's SplitEtaleHypercover and
  IsEtaleHypercover: these concern schemes and covering conditions, not this
  arbitrary-category family construction. DAG search likewise found this owner
  and the separate etale/full-object notions, not a missing independent node.

Mismatches found: none. No Lean or node changes were needed; only this independent
review was appended. No statement correction or citer audit is applicable.
Validation: server scompile.py compiled the only delivered module cleanly in 1.0 s,
nice 19, two threads, 60-second limit per file; no warnings or errors were emitted.
