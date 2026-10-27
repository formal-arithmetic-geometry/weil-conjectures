## Worker report

The module `Sheaf.AlgebraicGeometry.LocallySeparatedRationalPointClosedImmersion`
states `AlgebraicGeometry.AlgebraicSpace.rationalPoint_isClosedImmersion_of_locallySeparated`.
Its only theorem has proof `sorry`. There are no new definitions, new nodes, dependency
repairs, or statement corrections. Only the item's `lean` field changes.

The Lean signature matches the node as follows:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| Z is an algebraic space over Spec k | `(Z : AlgebraicSpace (Spec (CommRingCat.of k)))` |
| The relative diagonal is a representable immersion on every scheme test | `hdiag : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left) (prod.lift (𝟙 Z.obj.obj) (𝟙 Z.obj.obj))` |
| Every field extension K/k | `(K : Type u) [Field K] [Algebra k K]` |
| Z_K = Z ×_Spec k Spec K | `(Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙ Z.obj.obj` |
| A K-morphism a : Spec K → Z_K | `a : yoneda.obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ⟶` that base-change presheaf |
| a is representable and all scheme-test projections are closed immersions | `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) a` |
| The singleton image is closed in the atlas topology | `IsClosed ({schemePointMap a (IsLocalRing.closedPoint K)} : Set (Point ...))` |
| No finite-type or quasi-separatedness hypothesis | Neither occurs in the binders or assumptions. |

Here the product diagonal is over the fixed base `Spec k`, because it is taken in
presheaves on `Over (Spec k)`. `IsRepresentableWith` is the existing definition:
for every scheme T and map from its Yoneda presheaf, it supplies an actual scheme U,
projections, an `IsPullback` square, and the stated scheme property of U → T.
Thus the first conclusion includes scheme representability, not merely a property
of those tests already known representable. Its existential choice of a pullback
is equivalent to the condition for every representing square since closed
immersions are invariant under isomorphism.

The base-change expression is canonical restriction of the functor of points,
not an unspecified map or a replacement notion. A scheme T over Spec K is sent
by `Over.map` to that same scheme with composite structure map to Spec k. Giving
its point of the restricted presheaf is therefore exactly giving a map T → Z over
Spec k, equivalently a map T → Z_K over Spec K. This is also the existing encoding
used by `SeparatedGroupSpaceGeometricScheme` and its consumers. Since the Yoneda
domain of a is the identity object over Spec K, the composite to Spec K is the
identity automatically: no extra section equation is needed or omitted.

`Spec K` has one point, explicitly `IsLocalRing.closedPoint K`, so the point image
of a is exactly the singleton at its image under `schemePointMap`. The `Point` and
`pointTopologicalSpace` used here are the recorded point-class and atlas-topology
constructions, applied to the canonical base-change functor of points.

Dependency declarations read and used:

- `Field`, in `Mathlib.Algebra.Field.Defs`, for def-weil-field.
- `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, and the scheme-test
  diagonal definition in `Sheaf.AlgebraicGeometry.AlgebraicSpace`, for
  def-trf-algebraic-space. These are reexported by the two public Sheaf imports.
- `AlgebraicGeometry.Spec` and `Spec.map`, in `Mathlib.AlgebraicGeometry.Scheme`,
  for def-weil-affine-spectrum; their signatures and docstrings were read.
- `AlgebraicGeometry.IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, and `IsImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, for def-weil-closed-immersion.
- `Algebra` and `algebraMap`, in `Mathlib.Algebra.Algebra.Defs`, for
  def-pc-field-extension.
- `CategoryTheory.Limits.pullback`, its projections and universal-property
  constructors in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  for def-pc-fibre-product; they underlie the existing representability squares.
- `PointRepresentative.map`, `pointImage`, `pointTopologicalSpace`, and the
  reexported `Point`/`schemePointMap`, in
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, for
  def-a1-space-point-topology.
- `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`, in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`, for
  lem-trf-space-fibre-products-etale-covers.

The stated proof dependencies are imported privately:
`finite_of_decent_of_finite_residueField` in
`Sheaf.AlgebraicGeometry.DecentSpaceFiniteFieldMap`,
`exists_scheme_fibreProduct_point` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint`, and
`IsClosedImmersion.iff_isFinite_and_mono` in
`Mathlib.AlgebraicGeometry.Morphisms.Finite`. The two other proof-only nodes
lem-sfb-space-locally-separated-base-change and
lem-sfb-locally-separated-space-decent have no recorded Lean declaration, so have
no import yet. They are not statement prerequisites. The theorem docstring keeps
all six proof steps, their node names and Stacks sources for stage 3.

Sources read: local Stacks `decent-spaces.tex`, the statements and proofs of
lemma-locally-separated-decent (088J),
lemma-finite-residue-field-extension-finite (08AL), and
lemma-algebraic-residue-field-extension-closed-point (07U5); and
`spaces-morphisms.tex`, the relative locally-separated definition and the
base-change lemma (03KL). The final equal-residue-field clause of 08AL applies
with S = Spec K and extension K/K. These sources agree with the item.

Edge cases checked before writing: K = k gives the original rational-section
assertion; arbitrary infinite or inseparable K/k are retained because there is
no finite-dimensional or separability hypothesis. The only finite extension in
the proof is K/K. Empty Z has no such a, so the universal assertion is vacuous
without excluding empty algebraic spaces or empty test schemes. Nilpotents and
non-quasi-separated spaces are not excluded. No algebraic closedness, finite
type, quasi-compactness, separatedness, or reducedness is assumed. All schemes,
fields, and scheme tests share the existing framework universe u; no independent
smaller test universe is used. Every universe and variable is explicit.

Searches for an existing declaration:

- `msearch.py ... leanfinder "A rational point of a locally separated algebraic
  space over a field is a closed immersion"`: eight hits, including
  `AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion`,
  `IsClosedImmersion.SpecMap_residue`, and scheme separatedness results;
  all concern schemes, not algebraic spaces.
- `msearch.py ... loogle '"AlgebraicGeometry", "IsClosedImmersion"'`: twelve
  hits on scheme closed-immersion properties; no statement about algebraic spaces.
- `msearch.py ... grep 'AlgebraicSpace|LocallySeparated|rationalPoint.*[Cc]losed'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for local-separatedness,
  rational-point closedness, and `IsRepresentableWith` with `IsImmersion`:
  existing locally separated group/Picard-space statements use the same
  representable immersion diagonal, but no rational-point theorem matches.
  Broader rational/closed searches return unrelated coefficient and curve results.
- `rg` for the item id in `lean/WeilConjectures`: no occurrence.
- `rg` for the chosen declaration name in Mathlib, `lean/WeilConjectures` and
  `lean/Sheaf`: no occurrence before writing the sandbox module.
- `rg` for `Over.map` and `algebraMap` in `lean/Sheaf/AlgebraicGeometry` finds
  the canonical field-base-change expression already used in
  `SeparatedGroupSpaceGeometricScheme`, among other modules.

Validation: prescribed `scompile.py Q64` compiles both the sandbox probe and the
library module cleanly, with no errors or unexpected warnings. No global build
or direct shared-repository edit was performed. There is no statement dispute.

## Second reading by Q64

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
