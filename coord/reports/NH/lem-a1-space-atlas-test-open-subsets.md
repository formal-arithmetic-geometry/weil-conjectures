## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceAtlasTestOpenSubsets` states
`AlgebraicGeometry.AlgebraicSpace.exists_atlas_test_open_subsets`, with its entire proof
postponed by `sorry`. No definitions, dependency repairs, or new nodes are needed. The
natural-language statement and all its dependency lists are unchanged. There is no
statement dispute.

Source read: Stacks Project, `spaces-properties.tex`, Tag 03BX,
`lemma-topology-points`, especially the presentation pullback square and the paragraph
asserting that the scheme projections are continuous and open; Tag 03H4,
`lemma-points-cartesian`, including its proof by a common field extension. The latter
explains why the last image equality lifts specified pairs of points rather than requiring
uniqueness of a point of the fibre product.

Hypotheses and clauses, in their order in the node:

- The base scheme is `{S : Scheme.{u}}`, and the algebraic space is
  `(E : AlgebraicSpace S)`. Its underlying fppf presheaf is `E.obj.obj`. A single explicitly
  declared universe `u` is used for the schemes, test rings and field representatives, as
  in the recorded algebraic-space and point-class interfaces; `Point E.obj.obj` lives in
  `Type (u + 1)`. No additional size equality or smallness assumption is imposed.
- Schemes over `S` are `(W T : Over S)`. The atlas and arbitrary test map are the natural
  transformations `(w : yoneda.obj W ⟶ E.obj.obj)` and
  `(t : yoneda.obj T ⟶ E.obj.obj)`. The hypotheses `(hw : IsEtale w)` and
  `(hs : IsSurjective w)` are exactly representable étaleness and representable
  surjectivity: both predicates include actual scheme-test representing pullback squares.
  No étaleness or surjectivity is assumed of `t`.
- Representability of `T ×_E W` is the existential scheme `(Q : Over S)`, projections
  `(q : Q ⟶ T)` and `(b : Q ⟶ W)`, and
  `IsPullback (yoneda.map q) (yoneda.map b) t w`. This gives the actual universal property
  of the presheaf fibre product, hence also the fibre product of the associated sheaves.
  It supplies real scheme morphisms, rather than arbitrary maps of point sets.
- The projection assertions are `Etale q.left ∧ Surjective q.left ∧ Continuous q.left ∧
  IsOpenMap q.left`. Scheme morphisms, including `b.left`, carry their continuous
  underlying maps by the existing scheme interface.
- Every subset `A ⊆ |E|` is the binder `∀ A : Set (Point E.obj.obj)`. The first displayed
  equality is exactly
  `q.left ⁻¹' (schemePointMap t ⁻¹' A) = b.left ⁻¹' (schemePointMap w ⁻¹' A)`.
- The second displayed equality is exactly
  `q.left '' (b.left ⁻¹' (schemePointMap w ⁻¹' A)) = schemePointMap t ⁻¹' A`.
- Descent of openness is
  `IsOpen (schemePointMap w ⁻¹' A) → IsOpen (schemePointMap t ⁻¹' A)`.
- Every subset `B ⊆ |T|` is the binder `∀ B : Set T.left`. The last displayed equality is
  `b.left '' (q.left ⁻¹' B) = schemePointMap w ⁻¹' (schemePointMap t '' B)`.
- The final conditional is
  `IsEtale t → Etale b.left ∧ ∀ B : Set T.left, IsOpen B →
  IsOpen (schemePointMap w ⁻¹' (schemePointMap t '' B))`. Étaleness of `b` does not
  depend on a choice of open subset. The image equality immediately before it identifies
  this open subset with the last displayed image.
- All `IsOpen`, `Continuous` and `IsOpenMap` expressions concern the scheme spaces
  `Q.left`, `T.left`, and `W.left`. The module does not import or assume a topology on
  `Point E.obj.obj`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; schemes extend locally ringed spaces, and their morphisms
  are morphisms of locally ringed spaces. These are available through the public imports.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `AlgebraicSpace.IsEtale`, and
  `AlgebraicSpace.IsSurjective`. Their full definitions use existential `Over S` objects
  and `IsPullback` squares under Yoneda, exactly as the signature does.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `AlgebraicSpace.Point`,
  `PointRepresentative`, `PointRepresentative.Rel`, and `schemePointMap`. The map uses
  the residue-field morphism of the given scheme point. There is no private quotient
  or second definition of the scheme-source point map.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, the recorded
  scheme étaleness predicate.
- `def-weil-size-convention` is the recorded metatheoretic convention and has no module
  or declaration; the explicit universe binder implements its role here.

Proof dependencies are plain imports:
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint` supplies
`AlgebraicSpace.exists_scheme_fibreProduct_point` (its statement and proof docstring were
read); `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` supplies the Mathlib leaf
`AlgebraicGeometry.Scheme.Hom.isOpenMap`. The source and exact `mathlib_match` of
`lem-weil-pbc-etale-morphism-open-map` were read. Its `UniversallyOpen` hypothesis is
supplied for an étale map by the existing étale/flat/finite-presentation instances.
The other proof dependencies are already public statement dependencies.

Edge cases checked before writing: empty `T`, empty `W` (with surjectivity forcing the
appropriate empty tests), and empty `E`; `A = ∅` and `A = Set.univ`; `B = ∅` and
`B = Set.univ`; the identity atlas when `E` is a scheme; a test map `t` which is not étale;
and multiple fibre-product points above a given compatible pair. None is excluded.
The last identity uses existence of a lift, never a unique lift, and the final conditional
places no extra hypothesis on the preceding identities. No nonemptiness, affineness,
separatedness, finiteness, or topology on point classes is assumed.

Searches performed for this item:

- `msearch.py`, LeanFinder: “Pull back an etale atlas of an algebraic space and identify
  inverse images and images of arbitrary point subsets”. Eight results, concerning
  scheme étale categories and étale base-change stability; no algebraic-space subset
  statement.
- `msearch.py`, Loogle: `AlgebraicSpace.schemePointMap, Set.preimage, Set.image`.
  Zero results, with the explicit diagnostic that `AlgebraicSpace.schemePointMap` is an
  unknown identifier in the Loogle index. This result alone was not treated as evidence
  of absence; the source searches below located the project's actual point-map interface.
- `msearch.py`, grep: `AlgebraicSpace|schemePointMap`, restricted to Mathlib's
  `AlgebraicGeometry`. Zero results.
- `msearch.py`, LeanSearch: “Scheme test pullback of an algebraic space atlas identities
  for images and inverse images of point subsets”. Eight results, including
  `Scheme.image_preimage_eq_of_isPullback` in `Mathlib.AlgebraicGeometry.PullbackCarrier`.
  This is the scheme-target analogue, whereas our target is an algebraic-space presheaf
  with field-valued point classes, and does not directly state this item.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `atlas.*[Oo]pen|atlas_test|schemePointMap|lem-a1-space-atlas-test-open-subsets`.
  This located the point definitions, topology modules and downstream references, but
  no declaration of the present topology-free collection of subset identities.
- Exact proposed-name searches for
  `atlas_test_open_subsets|exists_atlas_test|atlasTestOpenSubsets` in both Lean trees and
  `dag/lean_names_upstream.json` found only a different private test-scheme helper in
  `SpaceLinePresentationHomDescent`. Exact node-id grep in `lean/WeilConjectures` found
  no declaration. The existing topology modules state atlas topology criteria rather
  than the present assertion about all scheme tests before defining that topology.

Validation: the complete delivered module compiled using the prescribed `scompile.py`
wrapper in both sandbox and library module modes, with no error or warning. The library
compile took 2.9 seconds under the default 60-second limit. The signature is copied
verbatim into the node's `lean.statement`. The proof docstring follows all six existing
DAG proof steps. Every theorem proof is `sorry`; there are no extra declarations.

## Second reading by NH

No independent second reading was performed by this worker. Under the dispatched
single-worker delivery instructions, the maintainer's independent review reads this
packet. During the author's final clause check, étaleness of `b` was placed outside the
open-subset binder so that it depends only on representable étaleness of `t`, and all
three displayed set identities remain unconditional in `A` and `B`.
