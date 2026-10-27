## Worker report

The module `Sheaf.AlgebraicGeometry.FieldGroupoidConstantLocalDimension` states
`AlgebraicGeometry.AlgebraicSpace.fieldGroupoid_localDimension_eq_dimension` and its
explicit group specialization `fieldGroup_localDimension_eq_dimension`. Both proofs
are exactly `by sorry`. No definition, axiom, or proof is introduced. The item's
statement and proof plan are unchanged. Its `stmt_deps` gains the already landed
`def-sfb-algebraic-space-groupoid` and `def-sfb-algebraic-space-etale-dimension`.

Source read: `literature/stacks-project/spaces-more-groupoids.tex`,
lemma-groupoid-on-field-locally-finite-type-dimension (06FD), clause (1), and
lemma-group-over-field-locally-finite-type-dimension (06FE), clause (1), including
their proofs. Also read `spaces-properties.tex`, definition-dimension-at-point
and definition-dimension (04N5/04N6). The accepted node's pointed right-translation
proof, rather than the disputed double-restriction passage in the source proof,
is reproduced step by step in the first theorem's docstring. No theorem statement
is disputed or corrected.

Hypotheses and clauses, in order:

- The scheme S is `{S : Scheme.{u}}`; the field is `(K : Type u) [Field K]`.
- The S-scheme U = Spec K is represented by
  `(b : Spec (CommRingCat.of K) ⟶ S)`, with its presheaf
  `yoneda.obj (Over.mk b)`. Thus U is the specified field spectrum, not an
  arbitrary algebraic space or an extra chosen equivalent object.
- The algebraic space R is `(R : AlgebraicSpace S)`. Its underlying presheaf
  is `R.obj.obj`, as in the recorded algebraic-space definition.
- The natural source and target maps are `s t : R.obj.obj ⟶ yoneda.obj (Over.mk b)`.
  Identities and inverses are the given maps `e` and `i`, and composition is
  `c : Limits.pullback s t ⟶ R.obj.obj`. Pullback is the actual categorical
  presheaf pullback; it evaluates to composable pairs on every test scheme.
- The functorial groupoid axioms are `hgroupoid : IsPresheafGroupoid s t e i c`.
  Its source/target, identity, inverse, and associativity fields use the same
  convention c(a,b) = a after b as the node. The maps are natural transformations,
  so their functoriality is already data, not an omitted hypothesis.
- Local finite type of s is `hs`: for every S-scheme V and representable étale
  scheme chart `a : yoneda.obj V ⟶ R.obj.obj`, the representing map
  `f : V ⟶ Over.mk b` of `a ≫ s` is `LocallyOfFiniteType f.left`.
  The equation `a ≫ s = yoneda.map f` specifies exactly the composite. Yoneda
  fullness supplies such an f for every a; the hypothesis cannot become vacuous
  because no f exists. No quasi-compactness, finite presentation or separatedness
  is required. `ht` renders the identical clause for t.
- The node's point set is `Point R.obj.obj`, the existing quotient of field-valued
  representatives by common-field-extension agreement. The quantified point is
  `(r : Point R.obj.obj)`.
- The local dimension is `etaleLocalDimension R.obj.obj r`. This is the landed
  supremum over all étale chart-point pairs, each contributing the scheme's
  `topologicalKrullDimAt`. For algebraic spaces the chart values agree, so this
  equals the value in any chart required by the node. The scheme quantity is
  precisely the infimum of dimensions of open neighbourhoods, not stalk dimension.
- The global dimension is `etaleDimension R.obj.obj`, whose body is the supremum
  of those local dimensions over all point classes. The first conclusion is
  `etaleLocalDimension R.obj.obj r = etaleDimension R.obj.obj` in `WithBot ℕ∞`.
- For the final group clause the second theorem uses H in place of R and one
  structural map p in both source and target positions. Its identity, inverse
  and multiplication are e, i, c with `IsPresheafGroupoid p p e i c`. This is
  exactly a group algebraic space over Spec K: its test-point objects are maps
  to Spec K, with all arrows loops at their given object, and the natural
  operations preserve that structure. Its single chartwise finite-type condition
  `hp` supplies both hs and ht. The conclusion is the same equality for every
  `h : Point H.obj.obj`. Keeping S and b arbitrary also includes S = Spec K.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms,
  and `AlgebraicGeometry.Spec`; `Mathlib.Algebra.Field.Defs`: `Field`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, and `AlgebraicGeometry.AlgebraicSpace.IsEtale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` (exposed by the groupoid module).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`:
  `AlgebraicGeometry.AlgebraicSpace.IsPresheafGroupoid`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleDimension`:
  `AlgebraicGeometry.AlgebraicSpace.etaleLocalDimension`, `etaleDimension`.
  Its public dependency `AlgebraicSpacePointClasses` supplies `Point`,
  `PointRepresentative.Rel`, and `schemePointMap`.
- Proof-only imports preserve the node's proof dependencies:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
  (`fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`) and
  `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`
  (`AlgebraicGeometry.fibre_dimension_after_base_change`). Their full statements
  and proof docstrings were read. Neither module is publicly re-exported here.

Edge cases checked before writing:

- The identity groupoid has R = Spec K and dimension zero.
- A group such as G_m has local neighbourhood dimension one even at its generic
  point, whose local ring has dimension zero: this rules out substituting the
  existing stalk-dimension chart-invariance theorem for the required definition.
- Nonreduced groups such as alpha_p are permitted: no reducedness or smoothness
  appears, and their dimension is zero.
- Non-quasi-compact groups and unbounded-dimensional disjoint unions are not
  removed by any binder; the codomain permits infinity.
- An empty arrow space cannot have an identity from the nonempty field spectrum;
  no separate Nonempty hypothesis is added. Empty individual charts impose no
  artificial point condition. Arbitrary characteristic and arbitrary base S remain.
- Source and target field embeddings need not coincide. The general theorem
  retains both s and t. Only the explicitly requested group specialization uses p p.
- All schemes, fields and test schemes use the project's common universe u;
  `Point` retains its existing universe u+1. `autoImplicit` is disabled.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder` query: "A locally finite type groupoid in algebraic
  spaces over the spectrum of a field has constant local dimension". Eight hits,
  including `LocallyOfFiniteType`, its ring-hom property, and smooth-presentation
  facts; no statement matching this node.
- `msearch.py ... loogle` query: `"Groupoid", "krullDim"`. Zero hits.
- `msearch.py ... grep` query:
  `groupoid.*dimension|dimension.*groupoid|AlgebraicSpace`. Zero Mathlib hits.
- `msearch.py ... leansearch` query: "The local dimension of a locally finite type
  group algebraic space equals its dimension at every point". Eight hits about
  local rings, localization height, topological groups and finite-type morphisms;
  no matching algebraic-space or internal-groupoid theorem.
- `rg` of `lean/WeilConjectures` for the item id and for the groupoid/dimension
  patterns found no match. `rg` of `lean/Sheaf` found the existing stabilizer
  dimension theorem and downstream docstring references, but no constant-local-
  dimension declaration. Direct searches for both proposed theorem names in
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found none.
- The project search found `AlgebraicSpaceGroupoid.lean` and
  `AlgebraicSpaceEtaleDimension.lean`; their owning DAG nodes and full definitions
  were read and reused. `AlgebraicSpaceLocalDimensionChartInvariance.lean` instead
  treats stalk Krull dimension. `GroupScheme/IdentityLocalDimension.lean` treats
  a finite-type group scheme at the identity and does not state this general result.

Validation: the required `scompile.py Q12 lem-sfb-field-groupoid-constant-local-dimension`
compiled the file both as a sandbox and under its library module name, cleanly
(1.5 s and 1.6 s). Only the prescribed wrappers are used for validation and delivery.

## Second reading by Q12

I reopened the node and the written signatures for a separate author rereading;
no additional agent was started, as required by the dispatcher. The maintainer's
independent review remains the independent reader of this delivery.

The first signature retains S, the field K, its specified base map b, the actual
algebraic space R, all five operation maps, and both chartwise finite-type conditions.
Its point r is an existing field-valued equivalence class. The equality uses chart-
local dimension and its supremum. No stalk dimension, topology of |R|, stabilizer
dimension or identity-only equality is substituted. The chartwise conditions quantify
over every étale a and its uniquely representing composite f; there is no extra
hypothesis on those composites. The second signature renders the node's last sentence
by substituting p for both source and target, with a single finite-type assumption.
All clauses and hypotheses match; no signature change was needed on rereading.
Both proofs remain sorry. The two added dependencies are landed nodes for precisely
the definitions used, and no new/dependency modules or statement correction are needed.
