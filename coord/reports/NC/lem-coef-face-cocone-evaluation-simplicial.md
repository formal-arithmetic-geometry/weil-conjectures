## Worker report

The module `Sheaf.AlgebraicTopology.FaceCoconeEvaluationSimplicial` states
`SSet.FaceCocone.evaluation_simplicial`, with one postponed proof. All constructions have
explicit data: Mathlib subset paths and nerve restriction, face inclusions, singleton vertex
images, block restrictions, enriched mapping maps, endpoint transports, and finite ordered
composition. The shared helper declarations belong to the new definition node
`def-coef-face-cocone-evaluation`, in `Sheaf.AlgebraicTopology.FaceCoconeEvaluation`;
they are listed in that node's `lean.declarations`. Keeping these constructions below both
the present theorem and splitting-refinement permits the future refinement proof import
without an import cycle. No existing dependency is restated.

Clause-by-clause reading:

- The finite nonempty linearly ordered set is `{V : Type u} [LinearOrder V] [Finite V]
  [Nonempty V]`. The small simplicial category is `{D : SCat.{u}}`, the recorded category
  `CategoryTheory.CoherentNerve.SCat`, not a private category construction.
- `Data.faces : Set (Set V)` is the family. `nonempty`, `singleton`, and `downward` say
  precisely that its members are nonempty, every singleton belongs, and every nonempty
  subset of a member belongs. No condition on the empty face is silently imposed.
- `Data.functor F hF` has domain `SimplicialThickening F`. This is Mathlib's ordered
  simplex: its hom simplicial sets are nerves of endpoint-containing subset posets and
  composition is union, exactly the model in the dependency's `coherentSimplex`.
  `Data.compatible` is equality of enriched functors under every inclusion, including
  equality of the object maps. `inclusion` uses the recorded direct-image path functor.
- `Data.vertex v` is the image of `v` under the singleton-face functor, so is exactly
  the node's `d_v`. `Data.normalizedMap` obtains the canonical endpoint equalities by applying
  singleton inclusion compatibility to the vertices, then transports the enriched mapping
  map. It does not assume chosen endpoint identifications or add a normalization hypothesis.
- `hij : i < j` is the strict endpoint inequality. `q : ℕ` includes degree zero.
  `Flag i j q` is `ComposableArrows (SimplicialThickening.Path i j) q`, hence literally
  a simplex of the subset-poset nerve. Its objects are the subsets `S_t`, its arrows
  are inclusions, and the Path fields say each subset lies in `[i,j]` and contains both
  endpoints. These use the dependency's Mathlib definitions.
- `Splitting S` is an increasing enumeration `joint : Fin (length+1) ↪o V` with first
  vertex `i`, last vertex `j`, and every joint in `S_0`. This is precisely a finite
  splitting set, presented in increasing order. Since `i < j`, length zero is impossible;
  no separate positivity assumption is needed. Every splitting set in the node has
  such an enumeration. `IsCanonical` says its range is exactly `S_0`.
- `Splitting.support R k` is exactly `S_q ∩ [a_k,a_(k+1)]`.
  `Data.IsAdmissible R` says that every one of these supports belongs to the family.
  `blockFlag` has objects `{v : support R k | v.val ∈ S_t}`: under the support subtype
  these are exactly `S_t ∩ [a_k,a_(k+1)]`. The support condition only additionally says
  `v ∈ S_q`, which follows from the flag inclusion `S_t ⊆ S_q`.
- `Data.blockValue` applies `Data.normalizedMap` to this restricted flag, so its endpoints
  are transported by strict singleton compatibility. `Splitting.endpoints` explicitly
  constructs the two vertices of the final support; its membership proofs are projections
  of the flag inclusions and the order-embedding inequality.
  `orderedComposite` composes these values in increasing joint order using `D`'s enriched
  composition, with the enriched identity for an empty list of factors.
  `Data.evaluation R hR` is therefore exactly `E_R(S)`, with type
  `D(d_i,d_j)_q`; the final casts use `R.first` and `R.last` only.
- `hcan : R.IsCanonical` and `hR : c.IsAdmissible R` are precisely admissibility of the
  canonical splitting `S_0`; thus `evaluation R hR` is the node's `E_q(S)`.
- `α : ⦋p⦌ ⟶ ⦋q⦌`, for arbitrary `p : ℕ`, is every monotone ordinal map.
  `restrict S α` applies the nerve operator, hence has entries `S_(α(t))`.
- The first conclusion supplies an increasing enumeration of its initial subset.
  The second applies to EVERY such canonical enumeration and supplies its admissibility
  proof together with `evaluation R' hR' = (hom D (vertex c i) (vertex c j)).map α.op
  (evaluation R hR)`. Thus the canonical splitting after restriction is admissible and
  its evaluation equals `α* E_q(S)`. Presenting finite sets by increasing enumerations
  adds no mathematical condition or choice; the existence/universal clauses express
  the intrinsic canonical set without selecting data from the postponed theorem.
  First faces and degeneracies are included because `α` is unrestricted.

Dependency declarations read and used:

- New `Sheaf.AlgebraicTopology.FaceCoconeEvaluation`: `SSet.FaceCocone.Data`,
  `Data.evaluation`, `Flag`, `restrict`, `Splitting`, `Splitting.IsCanonical`,
  and `Data.IsAdmissible`. Every other construction listed above is in this definition
  node's `lean.declarations`.

- `Sheaf.AlgebraicTopology.PinchedCubeLatching`: `SSet.PinchedCube.coherentSimplex`
  and its underlying Mathlib `CategoryTheory.SimplicialThickening`, `Path`, and
  `SimplicialThickening.functor` (subset-poset simplices, union composition, direct image).
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.simplicial_interval_lifting`, with the recorded
  `CategoryTheory.CoherentNerve.SCat` and its enriched-functor category interface.
  The category and enriched axioms, rather than a model structure or Kan assumption,
  are what this statement needs.
- Proof dependency `Sheaf.CategoryTheory.EnhancedDiagramsCones` is imported without
  `public`; `CategoryTheory.nerve` implements its restriction formula. The other stated
  proof dependencies are already direct public imports. The proof dependency
  `lem-coef-face-cocone-splitting-refinement` has no Lean record at this reading, so
  there is no module to import for it. Its argument is recorded in the theorem docstring.

Searches for an existing statement/construction:

- `msearch.py ... leanfinder "Evaluation of compatible enriched simplex face functors on
  a subset flag commutes with simplicial operators"`: eight hits, headed by
  `SSet.σ_naturality_apply` and pointed-simplex relations. These assume an already given
  simplicial map; none constructs face-cocone evaluation or handles new initial joints.
- `msearch.py ... loogle "SimplicialThickening.functor, EnrichedFunctor.map"`: zero hits
  (the hosted index reports the first identifier unknown). The actual declarations were
  therefore read directly in Mathlib's `SimplicialNerve.lean` and `Enriched/Basic.lean`.
- `msearch.py ... grep "face.*cocone|splitting.*evaluation|evaluation.*simplicial"
  AlgebraicTopology`: zero hits.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` trees for face cocones,
  splitting evaluations and canonical evaluations found only unrelated constructions;
  the side `CofibrantSubsetColimitDecomposition` discusses a different containing-face
  cocone, not evaluation of flags. Searches for this node id and the proposed namespace
  found no upstream declaration or name clash. `dag/lean_names_upstream.json` has no
  matching name. DAG search found the present node, its splitting-refinement sibling,
  and their consumers, not an independent definition node. `blueprint_refs.py search
  'face cocone'` returned zero blueprint nodes.
- Read HTT online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf,
  printed page 90 (PDF page 107): the boundary mapping cube description is the source
  of the node's explicitly identified auxiliary expansion. No source-based correction
  to the node is needed.

Edge cases checked: `q = 0`, `p = 0`, arbitrary maps into degree zero, repeated entries,
first faces with `S_0` properly contained in `S_1`, and all degeneracies are permitted.
A one-vertex `V` has no `i < j`, matching the source. With a singleton-only face family
there is no admissible positive-length block, again matching the source. No nonempty
mapping-space or fibrancy assumption is added. Finite supports in any object universe
are allowed; there is no equality imposed between independent site universes.

No STATEMENT-DISPUTED flag, statement correction or dependency repair is needed.
The one new definition node is detailed below.
The only `sorry` is the statement's theorem. Compilation and delivery checks are recorded
below after they finish. The independent second reading is performed by the maintainer,
as required by this dispatcher's direct-delivery workflow.

Validation: the final module compiled cleanly with the prescribed `scompile.py` wrapper,
both as a sandbox file and at its library module path; there were no Lean warnings.
The two modules together contain exactly one `sorry` and no standalone helper theorem. All sixteen
explicit declarations have source/blueprint docstrings. The item node copy differs from the
shared base only in `lean` and the addition of the new definition id to `stmt_deps`;
its recorded theorem signature is extracted verbatim.


## New nodes

`def-coef-face-cocone-evaluation` defines the strict face family and compatible enriched
functors, their singleton images, subset flags and their restriction, increasing splitting
enumerations, admissibility, block supports and restricted block flags, and the ordered
composite `SSet.FaceCocone.Data.evaluation`. The source is the same HTT 2.2.5 boundary
mapping-cube calculation (printed page 90) expanded in the two sibling auxiliary lemmas.
There is no theorem and no `sorry` in its module. The node records the primitive operations
separately so that splitting-refinement and simplicial compatibility can both use precisely
the same evaluation. No choice from an unproved existence statement supplies any data.

Before adding it, `rg -l` on the DAG found only the two statement nodes and their consumers;
no definition node owns face-cocone evaluation. `blueprint_refs.py search 'face cocone'`
returned zero blueprint nodes; its ancestor command returned
`prop-coef-integral-exceptional-adjoint`, which is recorded in the new node's provenance.
The new id and proposed declarations had no existing matches. All prescribed Mathlib
search results are copied, as returned, into `mathlib_searches`. In particular, LeanSearch
for 'A strictly compatible family of enriched simplex face functors evaluates a subset flag
by composition along its splitting joints' returned nerve simplex elimination, split
simplicial objects and standard simplex faces, not this construction. Loogle for
`"SimplicialThickening", "map"` returned exactly `functorMap` and `functor_map`; these
provide the direct-image path primitives used here, not the cocone or evaluation. LeanFinder
and the Mathlib/upstream/side-tree grep searches are recorded above. The already available
Mathlib primitives are reused rather than redefined.

For the new definition node the hypothesis and clause correspondence is precisely the
`Data`, `vertex`, `normalizedMap`, `Flag`, `Splitting`, `support`, `endpoints`, `blockFlag`,
`blockValue`, `orderedComposite`, `evaluation`, `IsCanonical` and `restrict` readings above.
These constructions allow arbitrary ambient linear orders; their finite nonempty strict
endpoint specialization is the node's context, and the theorem retains all those binders.
No data outside the supplied family, functors, flag, splitting and admissibility proof is
assumed. Endpoint equalities follow from strict compatibility, not extra fields.

Final split-module validation: `scompile.py NC lem-coef-face-cocone-evaluation-simplicial`
compiled both `FaceCoconeEvaluation.lean` and `FaceCoconeEvaluationSimplicial.lean` in
dependency order, including their library module paths, with no warnings or errors.
The preliminary one-module dry run passed; it was superseded by this two-module packet
to keep the shared definitions below the splitting-refinement proof input.

The final two-module `deliver2.py ... --no-push` dry run passed the server preflight
and all per-file compiles (`OK (dry run)`, prepared commit `e02a0791a8`).

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
