## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSmoothSourcePointLocality` states
`AlgebraicGeometry.AlgebraicSpace.smooth_at_iff_of_smooth_source` with a single
`sorry`. No definitions or auxiliary theorems are introduced. The natural-language
statement, accepted split and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- The scheme B is `{B : Scheme.{u}}`. The three algebraic spaces over that same base
  are `{X Y Z : AlgebraicSpace B}`. The universe `u` is explicitly declared;
  their field-valued point quotient has universe `u + 1`, as in the existing
  algebraic-space framework. No additional universe equality is imposed.
- The morphisms h and q are `(h : X ⟶ Y)` and `(q : Z ⟶ X)` in the full subcategory
  of fppf sheaves. Their underlying morphisms are natural transformations.
- Smoothness of q is exactly `(hq : MapIsLocally (@Smooth) q)`: every compatible
  pair of representable étale scheme charts has a smooth horizontal scheme map.
- Every point z is `(z : Point Z.obj.obj)`. `Point` is the quotient of field-valued
  representatives by agreement over common extensions, not a chosen geometric point.
  Its image q(z) is the existing canonical `mapPoint q.hom.hom z`.
- Smoothness of hq at z is the left existential: `W : OpenSubspace Z`, membership
  `z ∈ pointImage W.val.ι`, and an explicit universal chart condition:
  every `U V : Over B`, representable étale `a : yoneda.obj U ⟶ W.val.toFunctor`
  and `b : yoneda.obj V ⟶ Y.obj.obj`, and `k : U ⟶ V` with
  `a ≫ (W.val.ι ≫ (q ≫ h).hom.hom) = yoneda.map k ≫ b` satisfy `Smooth k.left`.
- Smoothness of h at q(z) is the right existential with `A : OpenSubspace X`,
  `mapPoint q.hom.hom z ∈ pointImage A.val.ι`, and the same explicit universal
  chart condition for `a : yoneda.obj U ⟶ A.val.toFunctor`, now with equation
  `a ≫ (A.val.ι ≫ h.hom.hom) = yoneda.map k ≫ b` and conclusion `Smooth k.left`.
- `OpenSubspace` is precisely a subfunctor whose every scheme pullback is an open
  immersion. Such an open is an algebraic space, so it has étale scheme charts.
  The universal presentation conditions are the chart test on its restriction;
  they are not a representability-by-schemes assumption on h or q. The existing
  presentation criterion equates the universal chart condition with a smooth
  surjective-source presentation. No surjectivity of its target chart is required.
- The `↔` has the requested orientation, hq at z iff h at q(z). There is no
  surjectivity hypothesis on q and no flatness, local finite presentation,
  separation or Noetherian hypothesis on h, X, Y, Z or B.
- The topology is the existing final topology detected by étale charts. Membership
  in the point image of an open subspace is the neighbourhood condition, by the
  existing open-subspace/open-subset correspondence. No new topology is defined.

Dependency declarations read and used (all namespace prefixes below are
`AlgebraicGeometry`, or `AlgebraicGeometry.AlgebraicSpace` for space declarations):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, the existing affine-local
  scheme smoothness predicate (the dependency record uses its deprecated name).
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  explicit `universe u` follows the already recorded algebraic-space encoding.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `pointTopologicalSpace`, `PointRepresentative.map`, using `Point` from its public
  import `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `mapPoint`; only the canonical point
  map is used, with no proper-curve assumption.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`, explicitly
  imported publicly and owned by `def-a1-algebraic-space-point-classes`.
- Proof-only: `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`,
  `etalePresentation_property_criterion` and `etalePresentation_property_iff_scheme`.
  The theorem signature no longer uses its `EtalePresentation` structure.

The five definition owners (open subspaces, point topology, chartwise morphism
properties, the canonical point map, and point classes) are added to `stmt_deps`
under the standing authorization to cite already landed declarations. The
presentation criterion is a proof dependency only, removed from `stmt_deps`.
No new node, dependency module or mathematical statement correction is needed.
All other fields of the item are unchanged.

The statement imports publicly the modules needed for its signature. Its remaining
imports preserve the recorded proof plan: `SpaceEtalePresentationPropertyCriterion`,
`AlgebraicSpaceEtaleOpenImage`,
`AlgebraicSpaceOpenFactorSchemeTests`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` (scheme source descent),
`AlgebraicSpaceFlatLfpUniversallyOpen`, `SchemeEtaleSourceTargetProperties`,
`StackChartwiseSmoothEtaleCalculus`, `AlgebraicSpaceFibreProductsEtaleCovers`, and
Mathlib's `Morphisms.Etale`. The fibred-groupoid representable calculus and
smooth-surjective fppf locality proof nodes have no recorded Lean declarations at
writing time, so there are no modules for those two proof-only inputs to import.
The docstring carries all five proof steps and identifies those pending inputs.

Source check: read Stacks `spaces-descent.tex`, definition of properties local on
the source, Tag 06ER (transfer from schemes), and Tag 06F2 (smooth locality).
The pointwise form follows by restricting to an open smooth neighbourhood, taking
its open image, and applying smooth-source descent there, as the node specifies.
The current blueprint direct-images proof (3) was also read as the inherited
ancestor context; this item is not that blueprint unit's own statement.

Edge cases checked mathematically before writing:

- Empty Z has no `z : Point Z.obj.obj`, so the assertion is vacuous as required.
- Identity q gives the same two neighbourhood conditions.
- An open immersion q need not be surjective: a proper open neighbourhood can
  witness either condition. The statement makes no assertion about points outside
  its image.
- A nonsmooth h can be smooth on just the image neighbourhood of the chosen z;
  neither side asks that h be smooth everywhere.
- A nonsmooth q is excluded by hq. For example a point mapping to the singular
  point of a singular curve would make the composite to a field smooth while
  the curve is not smooth there; its q is not smooth, so this is not a counterexample.
- No representability-by-schemes restriction is imposed on h or q. The only
  representable arrows are the étale charts and open inclusions, as in the source.

Searches for an existing exact statement (2026-10-24):

- `msearch.py leanfinder`, query “Smoothness at a point of a morphism of algebraic
  spaces is invariant under precomposition by a smooth morphism”: eight results,
  all scheme smoothness composition/base-change or relative dimension facts.
- `msearch.py loogle`, query `AlgebraicGeometry.IsSmooth,
  AlgebraicGeometry.isSmooth_comp`: no results (service reports unknown identifier
  for the historical name). Local source inspection resolves the modern name
  `Smooth`; the remote search index uses old names.
- `msearch.py grep`, query `smooth.*source|Smooth.*At|smoothLocus`, restricted to
  `AlgebraicGeometry`: twenty results on scheme/ring smoothness and loci, none on
  the space pointwise statement.
- `msearch.py leansearch`, query “Smoothness at a point of algebraic spaces is
  invariant under smooth source maps”: eight scheme/ring smoothness results,
  no exact statement.
- `rg` over project `lean/Sheaf` and `lean/WeilConjectures` for `SmoothAt`,
  `smoothAt`, `smooth_at`, `MapIsSmooth`, and the item id found scheme statements,
  stack chart predicates, and the reusable space interfaces above, no duplicate.
- `rg` over Mathlib, both project roots, and `dag/lean_names_upstream.json` for
  `smooth_at_iff_of_smooth_source` and `SpaceSmoothSourcePointLocality` found no
  existing declaration or module. DAG search located the separate maximal smooth
  open node; it does not state this smooth-source pointwise equivalence.

No disputed mathematical statement was found. The returned metadata faults are
repaired as detailed below.

## Returned-delivery repair

Compared the retained delivery at head `6c272e3d4939` with the current main node.
Only `lean` and added `stmt_deps` differed; rebased the repaired node on the current
main record, preserving its statement, split, proof and proof dependencies.

1. H2, theorem-owned `EtalePresentation`: selected the reviewer's inline alternative.
   Both neighbourhood conditions now quantify explicitly over `U V`, `a b`, and `k`,
   the two `IsEtale` hypotheses and the commutative-square equation, with conclusion
   `Smooth k.left`. These are exactly the fields of the previous presentation
   structure. No declaration is duplicated and no definition node is needed.
   Removed `lem-sfb-space-etale-presentation-property-criterion` from `stmt_deps`;
   retained it unchanged in `proof_deps` and changed its import to proof-only.
   Public imports now directly expose `AlgebraicSpaceMorphismProperties` and
   `AlgebraicSpacePointClasses`, whose declarations the signature actually uses.
2. H2, missing Point owner: read the full signature and docstring of `Point` in
   `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` and added its existing owner
   `def-a1-algebraic-space-point-classes` to `stmt_deps`. Its module is also imported
   publicly. The field-valued quotient and universe remain exactly unchanged.

Rechecked the repaired signature against the original node clause by clause above:
all hypotheses, both open-neighbourhood conditions and the equivalence are unchanged
mathematically; the empty-source, identity and non-surjective open-immersion cases
remain valid. The only postponed theorem is the original item, with `sorry`.

Validation of the repaired packet: fresh `scompile.py` server compilation passed
for both the sandbox and final module name, with no errors or unexpected warnings.
The prescribed per-file compiler limit was unchanged. Fresh
`deliver2.py --no-push` and final delivery follow this compile.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
