## Worker report

States `AlgebraicGeometry.AlgebraicSpace.exists_scheme_open_of_stalk_dimension_le_one`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchematicNearHeightOne`. The only theorem
has proof `sorry`; no definitions or auxiliary proof obligations were introduced.
Source checked: literature/stacks-project/spaces-over-fields.tex,
lemma-codim-1-point-in-schematic-locus, Tag 0ADD, lines 1443–1480.

Hypothesis and conclusion correspondence:
- An arbitrary scheme S is `{S : Scheme.{u}}`, and an algebraic space over it is
  `(X : AlgebraicSpace S)`. The presheaf category is schemes over S, so its product
  diagonal is precisely the relative diagonal over S.
- The diagonal is representable by closed immersions: `hsep` is
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)` applied to
  `prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)`. This uses actual representing scheme
  pullback squares, rather than an arbitrary map or an absolute-separatedness assumption.
- Locally Noetherian means every étale scheme chart is locally Noetherian: `hnoeth`
  quantifies over all `(T : Over S)` and all `t : yoneda.obj T ⟶ X.obj.obj`, and
  sends `IsEtale t` to `IsLocallyNoetherian T.left`. It imposes no surjectivity on t.
- The scheme V over S and its morphism a are `(V : Over S)` and
  `(a : yoneda.obj V ⟶ X.obj.obj)`; `ha : IsEtale a` is representable étaleness.
- The specified point is `(v : V.left)`; the local ring bound is exactly
  `hdim : ringKrullDim (V.left.presheaf.stalk v) ≤ (1 : WithBot ℕ∞)`.
- The conclusion gives an S-scheme `(U : Over S)` and a map
  `j : yoneda.obj U ⟶ X.obj.obj` representable by open immersions. Such a map is
  a monomorphism and identifies h_U with its subfunctor image: therefore this
  is precisely an open subspace represented by an S-scheme. No affine condition,
  atlas surjectivity, or global dimension bound is added to the conclusion.
- Containment of a(v) is `schemePointMap a v ∈ Set.range (schemePointMap j)`.
  These are the existing field-valued point classes and canonical residue-field maps.
- S and X have no global dimension bound. No Noetherianity or separatedness is
  assumed of S; all finiteness assumptions are exactly those stated for X.

Dependency declarations read and used:
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `AlgebraicSpace.IsEtale`, including their
  full defining pullback-square signatures and docstrings.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian`.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: `Etale`, used inside `IsEtale`.
- Mathlib.RingTheory.KrullDimension.Basic: `ringKrullDim`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses: `Point` and `schemePointMap`.
  The already landed def-a1-algebraic-space-point-classes was added to stmt_deps
  solely to cite these existing notions explicitly, without any duplicate definition.

All recorded proof dependencies having modules or Mathlib matches are imported
without `public` (except those already publicly imported for the statement).
Unstated proof nodes have no module to import: lem-sfb-etale-affine-pairs-test-quasiseparated,
lem-sfb-qcqs-space-finite-scheme-cover, lem-sfb-space-integral-qcqs-permanence,
lem-sfb-space-separated-fp-composition, lem-sfb-finite-space-morphism-topology,
lem-sfb-space-local-ring-dimension-quasifinite,
lem-sfb-finite-groupoid-height-one-affine-open, and
lem-sfb-noetherian-space-finite-affine-descent. The docstring retains all seven
steps of the node's natural-language proof, with the relevant node identifiers.

Edge cases checked before writing: stalk dimension zero is included by ≤ 1;
dimension one is included; dimension infinity is excluded only at the given chart
point. High-dimensional components elsewhere and arbitrary-dimensional bases are
allowed. Empty V cannot provide v, so the pointed statement has no instance there;
the same applies to an empty X since an étale map cannot send a point into it.
There is no nonempty or irreducible hypothesis, characteristic restriction,
quasi-compactness assumption on X, or algebraically closed field assumption.
The ring dimension is in WithBot ℕ∞, retaining the recorded dimension convention.
The single universe u agrees with the established scheme/space convention, including
all schemes and residue fields of that size; no extra equality of universes is imposed.

Searches for an existing statement:
- msearch.py LeanFinder: “A separated locally Noetherian algebraic space has a scheme
  open neighborhood at every point of local ring dimension at most one”: eight hits,
  all scheme-local-Noetherian/Artinian or scheme-local-affine declarations; no match.
- msearch.py Loogle: `"AlgebraicSpace", "IsLocallyNoetherian"`: zero hits.
- msearch.py LeanSearch: “Separated locally Noetherian algebraic spaces are schemes
  near points of local dimension at most one”: eight hits, all about already schematic
  objects; no algebraic-space schematic neighbourhood theorem.
- msearch.py grep, AlgebraicGeometry: `AlgebraicSpace|schematic.*(locus|neigh)|codimension.*scheme`:
  zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for schematicNear, schematic_near,
  schematic height, and the exact item id: no existing declaration for this item.
  Broader schematic/codimension searches found finite-flat scheme neighbourhoods,
  dense scheme opens, and dimension-chart invariance; none states the present result.
- The prescribed exact-id search in lean/WeilConjectures found no hit.
- Read AlgebraicSpaceOpenSubspace and AlgebraicSpacePointClasses, and nearby
  AlgebraicSpaceDenseSchemeOpen and AlgebraicSpaceLocalDimensionChartInvariance:
  reuse the existing representable-open-immersion and point interfaces.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED fault.

## Second reading by Q67

Author's second reading, not an independent review; the maintainer performs the
independent delivery review. Reopened the node and the completed Lean file.
Checked S, X, the relative diagonal, every (not just surjective) étale chart in
hnoeth, the selected chart a and point v, and the stalk bound against the node.
The existential open immersion from an S-scheme encodes a represented open
subfunctor, while range membership uses the actual residue-field image of v.
In particular the diagonal is relative over S, no global bound on V, X, or S is
introduced, and the neighbourhood is not required to be affine. All seven proof
steps and all currently recorded proof imports were checked. No mathematical
mismatch was found; the point-class node was explicitly added to statement
dependencies to document the already existing canonical map used by containment.
