## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralSpaceUniversallyClosed` states
`AlgebraicGeometry.AlgebraicSpace.affine_and_universallyClosed_of_integral`, with
proof `sorry`. It introduces no definition. The node statement, proof and source
are unchanged. Its `stmt_deps` gains the two already landed definition owners
`def-sfb-space-affine-quasifinite-properties` and
`def-sfb-space-morphism-properties`, whose predicates the conclusion uses.

Hypothesis and conclusion correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. No base-field, separation,
  finite-type, quasi-compactness or Noetherian restriction is imposed.
- The algebraic spaces over S are `{Y X : AlgebraicSpace S}`. These are the
  recorded full subcategory of big-fppf sheaves with representable diagonal and
  representable surjective etale atlas. Their morphism is `(f : Y ⟶ X)`.
- Integrality is `(hf : IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left)
  f.hom.hom)`. Unfolding the existing definition quantifies over every
  `(T : Over S)` and every `(a : yoneda.obj T ⟶ X.obj.obj)` and supplies an
  actual scheme U over S, projection p : U → T and q : h_U → Y, with
  `IsPullback q (yoneda.map p) f.hom.hom a` and `IsIntegralHom p.left`.
  Thus the hypothesis says exactly that each scheme base change is represented
  by an integral scheme morphism; it does not merely assume a map with no
  connection to the fibre product.
- The affine conclusion is `MapIsAffine f`, the existing predicate which, for
  each affine scheme T → X, supplies an affine scheme representing its fibre
  product. This is equivalent to the node's all-scheme formulation: an affine
  morphism over an affine scheme has affine source; conversely these affine
  scheme tests glue over an affine open cover of any T to a scheme affine over
  T. Pullback squares identify the glued scheme with Y ×_X T. The conclusion
  neither asserts that every T is affine nor that the whole Y is affine.
- The universally closed conclusion is `MapIsUniversallyClosed f`. Its full
  definition is `∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ X), IsClosedMap
  (mapPoint (Limits.pullback.snd f.hom g.hom).hom)`. Hence its base changes
  range over arbitrary algebraic spaces, not merely schemes, and the projection
  is the second projection from Y ×_X Y'. `Point`, `mapPoint`, and the installed
  `pointTopologicalSpace` use precisely the field-valued equivalence classes and
  final etale scheme-test topology required by the node.
- The two conclusions are joined by `∧`. There are no additional conclusions
  and no extra finite-type, surjectivity, compactness or Noetherian hypotheses.
  Every universe and variable is explicitly bound (`autoImplicit false`).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, including its complete pullback-witness
  signature. This module is publicly re-exported through the statement imports.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom`, whose
  superclass is `IsAffineHom` and whose affine-open section maps are integral.
  The finite/integral node's recorded module `Morphisms.Finite` is also imported.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`, the affine-open
  inverse-image condition, through the public affine-property module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsUniversallyClosed`, including its arbitrary-space base-change quantifier.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, with its full universal-property clause.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `PointRepresentative.map`, `pointImage`, `pointTopologicalSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `PointRepresentative`,
  `PointRepresentative.Rel`, `Point`, `schemePointMap` (publicly re-exported).
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `mapPoint` (publicly re-exported).
- Proof-only `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`:
  `exists_affine_etale_cover_and_point_topology`, including its continuity clause.
- Proof-only Mathlib theorem
  `IsIntegralHom.iff_universallyClosed_and_isAffineHom`, the exact
  `mathlib_match` of `pqf-lem-integral-univclosed`, supplied by the integral import.

Source checked directly: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-integral-universally-closed` (Tag 0415, implication (1) to (2)), and
`lemma-universally-closed-local` (Tag 03IT). The theorem docstring spells out all
four DAG proof steps, including the common-field-extension argument for the
image/preimage identity. No false cartesian assertion about topological spaces
is made.

Edge cases checked before writing: the empty source or target, an empty base
change, an empty closed subset, identity morphisms and identity base change,
non-surjective closed immersions, integral morphisms which are not finite,
nonreduced schemes, arbitrary non-Noetherian or non-quasi-compact targets, and
base changes by genuinely nonschematic algebraic spaces. None is excluded.
All scheme and field tests use the same u as Scheme.{u}, so there is no
independent smaller test universe making the conditions vacuous.

Existing-statement searches (2026-10-24):

- `msearch.py ... leanfinder "An integral morphism of algebraic spaces is affine
  and universally closed"`: eight hits, led by the scheme theorem
  `IsIntegralHom.iff_universallyClosed_and_isAffineHom` and its scheme instances;
  none is the algebraic-space theorem.
- `msearch.py ... loogle '"IsIntegralHom", "UniversallyClosed"'`: three scheme
  hits (`instUniversallyClosed`, the iff, and the morphism-property equality).
- `msearch.py ... leansearch "An integral morphism of algebraic spaces is affine
  and universally closed"`: eight scheme-only hits, including the integral
  definition and its affine superclass; no duplicate.
- `msearch.py ... grep 'AlgebraicSpace|integral.*universally.closed|
  universally.closed.*integral' AlgebraicGeometry`: four scheme-only comments
  in Proper.lean, no algebraic-space declaration in Mathlib.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` for integral
  and universally-closed combinations found the scheme results and specific
  approximation/moduli uses, but no theorem with this hypothesis and these
  two conclusions. Search for the node id in `lean/WeilConjectures` found none.
- Searches of project sources and DAG records for `MapIsAffine`,
  `MapIsUniversallyClosed` and `mapPoint` found the existing predicates and their
  owner nodes, which are reused. The proposed new theorem name was searched in
  both Lean source trees and `dag/lean_names_upstream.json`, with no hit.

No statement dispute, statement correction, new node or dependency repair is
needed. Only the expected sorry warning is allowed by the compile check.

## Second reading by Q48

Final self-check by the same worker; independent review belongs to the
maintainer's delivery review. I reopened the node and the complete Lean file,
then unfolded the definitions from their source modules. S, Y, X and f match;
`hf` quantifies over all schemes and supplies actual integral pullback squares;
`MapIsAffine` is the equivalent affine-test formulation; and
`MapIsUniversallyClosed` checks closedness on the installed atlas point topology
after every algebraic-space base change. No mismatch or excluded edge case was
found. The two definition-owner dependencies were added so the conclusion
reuses the existing notions. No theorem is proved and no mathematical data are
postponed. The sole postponed declaration has the complete sourced DAG proof
in its docstring.
