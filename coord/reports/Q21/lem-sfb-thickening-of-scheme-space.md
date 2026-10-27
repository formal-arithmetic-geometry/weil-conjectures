## Worker report

The module `Sheaf.AlgebraicGeometry.ThickeningOfSchemeSpace` states
`AlgebraicGeometry.AlgebraicSpace.isRepresentable_of_thickening`, with `sorry` as its
only proof. It introduces no definitions. The mathematical statement is unchanged.

Source checked: `literature/stacks-project/spaces-more-morphisms.tex`,
lemma-thickening-scheme, Tag 05ZR, lines 1730 ff.; the general affine-open proof
in `spaces-limits.tex`, lemma-reduction-scheme, Tag 07VU, lines 3482 ff.
Tag 05ZR applies to arbitrary thickenings; its later separate finite-order proof
is not an additional hypothesis. The docstring records all four DAG proof steps.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`, with arbitrary explicit universe `u`.
- The algebraic spaces over S are `(Z Y : AlgebraicSpace S)`. Their type includes
  the fppf sheaf property, representable diagonal and an etale surjective atlas.
- The closed immersion is `(i : Z ⟶ Y)` together with
  `hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`.
  Unfolding the existing predicate quantifies over EVERY `T : Over S` and map
  `yoneda.obj T ⟶ Y.obj.obj`; it supplies a representing scheme, its projection,
  a genuine presheaf pullback square, and the closed-immersion property of that
  scheme projection. Thus the fibre-product and scheme-test clauses are both
  present without imposing representability of Y beforehand.
- The induced homeomorphism is `hiTop : IsHomeomorph (mapPoint i.hom.hom)`.
  `mapPoint` applies i to field-valued representatives and descends to their
  existing quotient. The `pointTopologicalSpace` instance supplies exactly the
  final topology from etale scheme-source maps specified by the node.
- Z being representable by a scheme over S is `hZ : Z.obj.obj.IsRepresentable`.
  This is Mathlib's `CategoryTheory.Functor.IsRepresentable`, which asserts an
  object of `Over S` with natural Hom bijections, not relative representability
  of the morphism i.
- The conclusion `Y.obj.obj.IsRepresentable` asserts the identical notion for Y.
- There is no finiteness, finite-order, quasi-compactness, Noetherian, separatedness,
  characteristic, nonemptiness or affine hypothesis. All variables are explicitly
  bound and `set_option autoImplicit false` enforces that convention.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicSpace.IsRepresentableWith`. The latter's actual pullback-square
  witness expresses the requested fibre product; no second construction is made.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; their universal
  property is encoded in the existing `IsPullback` witness in IsRepresentableWith.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  using `Point`, `PointRepresentative`, `schemePointMap` from its recorded dependency.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`.
  Its already-landed node `def-sfb-proper-curve-moduli` is added to stmt_deps
  solely to cite this canonical quotient map, as in the landed point-open calculus.
- `Mathlib.CategoryTheory.Yoneda`: `CategoryTheory.Functor.IsRepresentable`.

Already recorded proof-dependency modules are imported privately:
`AlgebraicSpaceEtaleOpenImage` (`openSubspace_points_orderIso`, `etale_open_image`),
`AlgebraicSpaceOpenFactorSchemeTests` (`openSubspace_preimage_schemeTests`,
`openSubspace_factor_schemeTests`), `AlgebraicSpacePointOpenCalculus`
(`point_open_calculus`), `Mathlib.AlgebraicGeometry.Morphisms.Finite`
(`IsClosedImmersion.iff_isFinite_and_mono`, its closed-immersion finite instance),
and `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`
(`isRepresentable_of_isSheaf_of_zariskiCovers`). The two proof nodes
`lem-sfb-space-thickening-base-change` and
`lem-sfb-finite-surjective-affine-space-target` have no recorded module in the read
checkout and are not needed to state this theorem, so no import is invented.

Edge cases checked before writing:

- Identity thickenings are included and return the assumed representability.
- The empty scheme and empty affine-open covering are allowed: no Nonempty or
  irreducibility binder excludes them; a homeomorphism forces both point spaces
  to be empty simultaneously. The usual empty scheme represents the result.
- Square-zero examples such as Spec k into Spec k[epsilon]/(epsilon^2) are included.
- General nil ideals without a uniform nilpotence bound are included: neither
  finite-order nor finite-presentation is assumed. The DAG argument uses only
  finiteness of closed immersions, which holds for arbitrary ideals.
- Non-affine Z, non-quasi-compact schemes, arbitrary base and characteristic are
  included. Point classes remain in Type (u+1), scheme tests and coefficients
  retain the existing framework's universe u; no universe equality is added.

Searches for an exact existing theorem (2026-10-24):

- `msearch.py ... leanfinder "An algebraic space which is a thickening of a scheme
  is representable by a scheme"`: eight hits, including
  `Scheme.LocalRepresentability.representableBy`, its `isRepresentable` theorem,
  scheme constructors, AffineScheme, and Scheme.Etale; no thickening theorem.
- `msearch.py ... leansearch` with the same query: eight hits, all general scheme
  constructors or local representability; no algebraic-space thickening result.
- `msearch.py ... loogle '"AlgebraicSpace"'`: zero hits.
- `msearch.py ... grep 'AlgebraicSpace|thickening.*scheme|scheme.*thickening'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` for
  `thickening`, `Thickening`, `IsHomeomorph`, and scheme/thickening combinations
  found scheme-only thickening results and algebraic-space pushout and deformation
  interfaces; no theorem with the assigned conclusion for arbitrary algebraic spaces.
  The upstream `ThickeningAffineScheme` result assumes the thickening target is
  already a scheme and cannot replace this statement.
- `rg -n 'lem-sfb-thickening-of-scheme-space' lean/WeilConjectures`: no hit.
- Proposed declaration names searched in Mathlib/project sources and
  `dag/lean_names_upstream.json`: no existing declaration of this name.

No statement correction, disputed statement, new node, or dependency repair is needed.
Server validation: scompile.py compiled the sandbox and library module in 1.7 s
apiece with no errors or unexpected warnings.

## Second reading by Q21

Author's final cross-check, not a separate agent review: the dispatcher explicitly
forbids starting another agent and assigns independent review to the maintainer.
Reopened the node and the written module. The binders S, Z, Y, i, hi, hiTop, hZ
match, respectively, its base, algebraic spaces, closed immersion on every scheme
test, homeomorphism for the atlas topology, and scheme representability of Z.
The conclusion is scheme representability of Y over the same base. There are no
extra hypotheses or extra conclusions. In particular IsHomeomorph includes the
inverse continuity condition, and IsRepresentable is a predicate on the presheaf
on Over S, so it does not mistake representability of a map for that of a space.
The docstring has all four proof steps with their original node names. No
mathematical mismatch was found and no statement change was made. The only added
DAG dependency records the already-existing canonical point map used in hiTop.
