## Worker report

The module `lean/Sheaf/AlgebraicTopology/InvertibleIntervalProductProjection.lean` states
`SSet.Enhanced.invertible_interval_product_projection`.  It quantifies an arbitrary small
simplicial set `R : SSet.{u}` and every test `C : SSet.{max u v}` with
`C.Quasicategory`, and asserts that precomposition along the degreewise product projection
`CartesianMonoidalCategory.fst R SSet.coherentIso : R ⊗ SSet.coherentIso ⟶ R` induces an
ordinary equivalence after `SSet.hoFunctor`.

The Lean rendering of each clause is:

* “For every small simplicial set `R`” is the explicit binder
  `{R : SSet.{u}}`.
* “for every test quasicategory” is
  `∀ (C : SSet.{max u v}), C.Quasicategory →`.
* “categorical equivalence in the Joyal test-functor convention” is the conclusion
  `((hoFunctor.map ((MonoidalClosed.pre
  (SSet.uliftFunctor.{v, u}.map
  (CartesianMonoidalCategory.fst R SSet.coherentIso))).app C)).toFunctor).IsEquivalence`.
  This is exactly the homotopy-category test used by `SSet.exists_joyal_model_structure` and
  `SSet.joyal_functor_equivalence_test`.

The interval is Mathlib's `SSet.coherentIso`, an abbreviation for the nerve of
`CategoryTheory.WalkingIso`, the codiscrete two-object groupoid with one morphism in every
hom-set.  Products are the existing Cartesian monoidal product on simplicial sets, and
`CartesianMonoidalCategory.fst` is its first projection; no private notion is introduced.

Dependencies used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, including the enhanced simplicial-set
  conventions recorded by `def-cbc-enhanced-diagrams-cones` (`SSet.Enhanced.coneCategory` and
  its helper declarations).
* `Sheaf.AlgebraicTopology.JoyalModelStructure`, declaration
  `SSet.exists_joyal_model_structure`, recorded by `lem-coef-joyal-model-structure`.
* `Sheaf.AlgebraicTopology.JoyalFunctorEquivalenceTest`, declaration
  `SSet.joyal_functor_equivalence_test`, imported for the proof route.
* `Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso`, declarations
  `CategoryTheory.WalkingIso` and `SSet.coherentIso`.

Edge cases checked before writing: `R = ∅`; `R = Δ[0]`; arbitrary input universe `u` and
larger test universe `max u v`; no finiteness or nonemptiness assumption on `R`; and the
empty test simplicial set (when it satisfies the quantified quasicategory premise).  The
product and projection are degreewise, so these cases are included by the existing
constructions.

Searches made:

* `msearch.py ... leanfinder "For every small simplicial set R, projection from R times the
  nerve of the two-object walking isomorphism to R is a categorical equivalence"`: returned
  nerve and truncation declarations, with no exact product-projection equivalence.
* `msearch.py ... loogle "SSet.coherentIso, CartesianMonoidalCategory.fst, categorical
  equivalence"`: no hit (the tool reported `CartesianMonoidalCategory.fst` as an unknown
  Loogle identifier); the declaration was checked directly in Mathlib and compiles.
* `msearch.py ... grep "coherentIso|WalkingIso|invertible_interval_product_projection"
  AlgebraicTopology`: returned only Mathlib `CoherentIso.lean` definitions and no theorem for
  this projection.
* `rg` over `lean/Sheaf` and the slopmaster2 `WeilConjectures/` source found no existing
  declaration of this item.  `grep -rl` over `dag/nodes` found only this node and its citer
  `lem-coef-join-slice-cocone-comparison`; no duplicate DAG statement exists.

No new definition node, dependency repair, statement correction, or
`STATEMENT-DISPUTED` flag is needed.  The file compiles with `scompile.py` with no errors or
warnings.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
