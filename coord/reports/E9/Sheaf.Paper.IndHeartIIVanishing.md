## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.indHeartII_vanishing` in
`Sheaf.Paper.IndHeartIIVanishing`, retaining its complete signature and the DAG route.
The comparison is exactly `constructible_sheaf_ext_continuity` from the stated dependency
`sk-lem-constructible-ext-continuity`. For vanishing, unpack `ObjectProperty.ind` to get
its small filtered colimit presentation. Apply the supplied uniform bound to each
constructible stage. Mathlib's `Functor.isZero` and `IsColimit.isZero_pt` show that the
abelian-group colimit is zero. Transport zero across the canonical comparison
isomorphism and use `AddCommGrpCat.subsingleton_of_isZero`.

Added proof imports of `Mathlib.Algebra.Category.Grp.Zero` and
`Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`. Removed the unused proof imports
listed below. Public imports, declarations, definitions and docstrings are unchanged.
No consumer adaptations or change records are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.indHeartII_vanishing`
(node `det-ind-heart-ii-vanishing`). Added 0 holes; 0 holes remain in the delivered module.
No intermediate statements were split off. The proof uses the existing stated
`AlgebraicGeometry.ProEtale.constructible_sheaf_ext_continuity`; its pre-existing hole
in another module remains that dependency's obligation.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.UniformConstructibleExt`: the fixed uniform bound is a hypothesis;
  this theorem does not need to construct one. Its node remains a statement dependency,
  and the parent unit's uniform-bound route is preserved.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: no local-model lemma is needed;
  constructible stages are supplied by the ind-presentation.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`: no stratification
  construction is needed; its definitions are already publicly available through
  `CoefficientHeartCommonStratification`.
- `Sheaf.Topology.ProfiniteCondensedRing`: no additional condensed-ring property is used.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`: the argument uses the displayed
  integer derived Hom functor, without the nonnegative Ext API.

The only planned proof dependency is `sk-lem-constructible-ext-continuity`, and it is
used. No DAG node or module is withdrawn. No claim is made that removing a direct
import makes its module unreachable from all other target imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The constructible-sheaf clause of the
continuity dependency already supplies the degree-zero reduction in the first two
DAG steps, so no complex-level colimit construction needs to be repeated here.
The final zero-colimit argument is formal for arbitrary diagrams; filteredness is
used by continuity and by the ind-presentation. The proof does not assume the existence
of a uniform bound beyond the explicitly supplied hypothesis.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
