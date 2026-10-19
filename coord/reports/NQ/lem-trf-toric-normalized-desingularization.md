## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SmoothFunctorialNormalizedToricDesingularization.lean`
records the statement of `lem-trf-toric-normalized-desingularization` and leaves its
proof as `sorry`.  It uses the dependency module
`Sheaf.AlgebraicGeometry.MonoschemeToricRealization`.

The item statement is represented by the following declarations in the owning module:

* `AlgebraicGeometry.Monoscheme.NormalizedToricTower` is one finite normalized tower
  over a fine monoscheme.  Its `baseIso` renders `X_0 = X`, its `tower` is the recorded
  `NormalizedTower`, and `centers` renders finite-type (coherent), nonempty and nowhere
  dense closed zero schemes.  `desingularization` renders regularity of `X_n`.
  `toBase` and `toBase_comp` give the structural maps over `Spec (ULift Q)`.
* `action`, `action_base`, `action_naturality`, and `center_preserved` render extension
  of each connected torsion-free component torus action to every stage and preservation
  of every center.  The stage-zero equation is written using the dependency's canonical
  `torusAction`, `componentι`, and `baseIso`.
* `AlgebraicGeometry.Monoscheme.NormalizedToricComparison` renders the smooth pullback
  tower, its pulled-back centers and commuting squares via `NormalizedPullback`, and the
  contraction to the source tower via `NormalizedContraction`.  The two base equations
  identify its level-zero map with the given smooth morphism of toric realizations.
  `NormalizedToricComparison.levelMap` is the canonical map obtained from the contraction
  isomorphism followed by the pullback lift.
* `AlgebraicGeometry.Monoscheme.SmoothFunctorialNormalizedToricDesingularization` is the
  single rule on all fine torsion-free monoschemes (including disconnected finite
  disjoint unions).  Its `comparison` quantifies over every smooth scheme morphism
  between the corresponding rational toric realizations.  `identityIndex` and
  `identityMap` render identity compatibility; `compositionIndex` and `compositionMap`
  render compatibility with composites; `surjective_no_contraction` says that a
  surjective smooth map has an injective contraction index, hence contracts no stage.
* The theorem
  `AlgebraicGeometry.Monoscheme.exists_smooth_functorial_normalized_toric_desingularization`
  states exactly the node's existence conclusion.

Every node hypothesis and conclusion is rendered as follows.  “Fine torsion-free
monoscheme with finite affine cover” is `M : Fine.{u}` together with
`hM : M.IsTorsionFree`; the finite-cover field is part of `Fine`, and disconnected
finite unions are therefore included.  “Write `X = Q[M]`” is the level-zero
isomorphism `baseIso : tower.level 0 ≅ realization (ULift.{u} ℚ) M`.  “Finite normalized
blowup tower” is `tower : NormalizedTower`; its `blowup` field says each arrow is the
normalized blowup of the displayed center.  “Each center is a coherent ring ideal
whose closed zero scheme is nonempty and nowhere dense” is the conjunction in
`centers`, namely `ofFiniteType`, `Set.Nonempty support`, and `IsNowhereDense support`.
“Terminal scheme is regular” is `desingularization`.

“For every smooth `Q`-morphism `h : Y -> X`” is the explicit map
`h : realization (ULift.{u} ℚ) N ⟶ realization (ULift.{u} ℚ) M` and hypothesis
`Smooth h` in `comparison`.  “Canonically the contraction of the pullback tower,
with pulled-back ideals retained in order” is the `pulled`, `pullback`, and
`contraction` fields; `NormalizedPullback.centers` gives the pulled ideals and
`NormalizedContraction.keptCenter` preserves their order.  “No stage is contracted
for surjective `h`” is `Surjective h -> Function.Injective ...contraction.index`.
“Identifications respect identities and composition” is rendered by the two identity
fields and the two composition fields, with the composite equality `_hc : k = h ≫ g`.
“At every stage each connected toric component acts and preserves the center” is
rendered by `action`, its stage-zero extension equation `action_base`, the arrow
compatibility `action_naturality`, and `center_preserved` for every
`C : ToricComponent M` and every center index.

The dependency declarations used are:

* `Fine`, `Fine.IsTorsionFree`, `ToricComponent`, `realization`,
  `realizationToBase`, `componentι`, `componentToBase`, `torusToBase`, and
  `torusAction` from `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`;
* `NormalizedTower`, `NormalizedPullback`, `NormalizedContraction`,
  `NormalizedTower.IsDesingularization`, and `IsNormalizedBlowup` from the same
  module;
* `Scheme.IdealSheafData.ofFiniteType`, `Scheme.IdealSheafData.support`, and
  `Scheme.IdealSheafData.comap` from the imported Mathlib/WeilConjectures ideal-sheaf
  declarations.

No dependency module or new DAG node was needed.  The recorded dependency declaration
is used directly; it supplies the exact fine monoscheme and toric-realization notions.

Edge cases checked before writing:

* `length = 0`: `Fin length` is empty, so there are no centers or blowup arrows and
  the regularity clause applies to level zero.
* The empty monoscheme is permitted by `Fine.finiteCover` with an empty cover; the
  component/action quantifiers are then vacuous.
* Disconnected finite unions are covered by the same `Fine` object and the component
  quantifier ranges over every torsion-free connected component.
* A unit center can only be deleted when its normalized blowup arrow is an isomorphism,
  exactly as required by `NormalizedContraction.deleted`; a nontrivial normalization
  stage is retained.
* `ULift.{u} ℚ` supplies the rational field in the scheme's universe, so no universe
  case is excluded.
* A surjective pullback has no contracted stage because the index is required to be
  injective; identity maps and composite maps are included explicitly.

Searches made:

* `msearch.py ... leanfinder "smooth-functorial normalized toric
  desingularization over Q with normalized blowup towers"` returned only generic
  smoothness and normalization declarations; none states this rule.
* `msearch.py ... loogle "SmoothFunctorialDesingularization, NormalizedTower,
  NormalizedContraction"` returned no match (and reported
  `SmoothFunctorialDesingularization` as unknown to Loogle).
* `msearch.py ... grep "toric.*normalized|normalized.*toric|SmoothFunctorialNormalized"
  AlgebraicGeometry` returned zero hits.
* `rg -n 'toric-normalized-desingularization|SmoothFunctorialNormalized|NormalizedToric'`
  in the source checkout found no existing declaration.  The project search found
  only the stage-1 DAG node and the dependency framework; no duplicate statement
  module exists.

## Second reading by NQ

I reread the node statement and the dependency module against the compiled file.  The
`Fine`/`IsTorsionFree` binders are exactly the node's domain; `baseIso`, `NormalizedTower`,
`centers`, and `desingularization` match the tower, center, and regular-terminal clauses.
The smooth-map binder is an arbitrary smooth morphism between realizations, as the node
requires, rather than a restricted monoscheme map.  `NormalizedPullback` and
`NormalizedContraction` match ordered pullback centers, canonical level identifications,
and deletion only of unit-isomorphism stages.  The identity, composition, torus-action,
and surjective clauses are all explicit fields of the rule structure.  The file compiles
cleanly with `scompile.py`; no statement correction, dependency repair, or new node was
made.
