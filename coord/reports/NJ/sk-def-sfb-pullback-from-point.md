## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtalePointPullback` exposes the canonical
inverse image from the profinite point.  `sfbPullbackFromPoint X` is the published
`AlgebraicGeometry.ProEtale.upperStarFromPoint X`, namely the composite of
`pointUpperStar` with the finite pro-etale pullback along `toSpecZ X`.
The companion `sfbPullbackFromPointRightAdjoint X` is the composite of the
finite pro-etale direct image and `pointLowerStar`.

The specification theorem records the node clause by clause.  Its first
conjunct is terminality of `specZ` (`f ≫ toSpecZ Y = toSpecZ X`).  The next
four conjuncts are, respectively, weak étaleness of `Spec LC(S, Z)`, finite
limit preservation, preservation of finite jointly-surjective coverings, and
continuity of `profiniteToProEt`.  The following equality identifies the test
object with the canonical base-change object
`(MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).obj
(profiniteToProEt.obj S)`, i.e. `X[S]`.

The point clauses use `pointUpperStar`, `pointLowerStar`, and
`pointUpperStarLowerStarAdjunction`: the theorem records the adjunction,
left-adjoint structure, and strong monoidal and braided structures.  The
scheme clause records the composite definition of `sfbPullbackFromPoint`, its
left-adjoint, monoidal, and braided structures, and its adjunction with the
explicit right adjoint.  The final equality evaluates that right adjoint at
`S` as `G((profiniteToProEtOf X).obj S)`, matching `G(X[S])`.  No hypotheses
are added; `X`, `Y`, `f`, `S`, and `G` are all universally quantified, and
empty or singleton profinite sets are included.

Dependency declarations used:

- `sk-def-sfb-condensed-ring`: source declarations
  `Profinite.continuousMapRingSheaf` and the condensed-site convention, in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`.
- `def-weil-pbc-proetale-site`: Mathlib `AlgebraicGeometry.Scheme.ProEt` and
  `AlgebraicGeometry.Scheme.ProEt.topology` from
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `sk-def-sfb-sheaf-tensor`: `CategoryTheory.sfbSheafTensor_properties` from
  `Sheaf.CategoryTheory.SheafTensor`; the published point construction uses
  this sheafified objectwise tensor on `Ab`.
- `def-sfb-finite-upper-star`: `AlgebraicGeometry.ProEtale.upperStar` from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.

Searches for an existing complete declaration found no single declaration
for the complete item: `msearch.py ... leanfinder` for “pullback from a
profinite point to pro-etale sheaves with monoidal adjunction”; `msearch.py ...
loogle` for `profiniteToProEt pointUpperStar upperStarFromPoint`; grep in
Mathlib for `profiniteToProEt|pointUpperStar|upperStarFromPoint`; grep in
`WeilConjectures/` for the same names; and grep in `lean/Sheaf` for the item
id.  The source module `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
contains the component constructions but no umbrella declaration, so the
module uses canonical aliases and a specification theorem rather than a
second implementation.  `scompile.py` compiled the module cleanly.

## Second reading by NJ

I reread the node and the module together.  Part 1 maps to the weakly-etale,
finite-limit, covering, and continuity conjuncts; part 2 maps to the relative
base-change object equality; part 3 maps to the point pullback, its adjunction,
and monoidal/braided structures; part 4 maps to the composite pullback, its
adjunction, monoidal/braided structures, and evaluation formula.  The aliases
refer directly to the published canonical constructions, so no private copy of
`LC`, a site, a tensor, or a Kan extension is introduced.  No mismatch was
found.

## Maintainer review fix (cc reviewer, 2026-10-18)

Two clause-level gaps in `sfbPullbackFromPoint_spec` were closed; the definitions
`sfbPullbackFromPoint`, `sfbPullbackFromPointRightAdjoint` and the recorded
`lean.statement` are unchanged.

1. The node's displayed formulas `Spec LC(S,Z) = lim_i ∐_{S_i} Spec Z` (part 1) and
   `X[S] = lim_i ∐_{S_i} X` (part 2) were not stated.  Added: the image of
   `Profinite.asLimitCone S` under `profiniteToScheme`, resp. under
   `profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙ Over.forget X`, is a limit cone;
   both functors preserve finite coproducts; and the structure morphism at the
   one-point space is an isomorphism (to `Spec Z`, resp. `X`).
2. `Nonempty pointUpperStar.Braided` and `Nonempty (sfbPullbackFromPoint X).Braided`
   asserted only some braided structure.  Replaced by the braiding equation for the
   canonical (instance) tensorators, and for `p^*` added invertibility of the unit and
   tensor comparisons of the oplax structure of `pointUpperStarLowerStarAdjunction`.
   Added `public import Mathlib.Topology.Category.Profinite.AsLimit`.

The fixed module compiles cleanly with `nt_compile.py` (only the `sorry` of the
specification theorem).
