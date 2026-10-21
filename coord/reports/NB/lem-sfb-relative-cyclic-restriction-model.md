## Worker report

The module `Sheaf.CategoryTheory.RelativeCyclicRestrictionModel` states the relative cyclic
restriction model, its normalized comparison equations, residual-action forgetting,
coefficient compatibility and the bar evaluation identity. Every postponed theorem has
proof `sorry` and a source/proof docstring carrying this node's blueprint id. Helpers belong
to the canonical constructions in this item, with seven missing definition interfaces
recorded below under §1(A). The source, unit, target and item statement are unchanged.
The item gains precisely these definition dependencies; there are no dependency repairs.

The input `A : CategoryTheory.CondensedBar.Ring.{u}` is the already recorded bundled
commutative ring object on the coherent profinite site. Its internal modules and actions
are `CondensedBar.Modules` and `CondensedBar.Equivariant`, transparent abbreviations of
`Profinite.CondensedAction.Modules` and `.ActionModule` from the recorded action dependency.
They retain all generalized profinite sections and their restriction naturality. This
includes coefficients with no topological-ring presentation. `u` is arbitrary. The cyclic
group `Z` is the universe lift of the discrete additive integers in multiplicative notation;
`generator` is positive one. Profinite residual and source groups use Group,
TopologicalSpace, IsTopologicalGroup, CompactSpace, T2Space, TotallyDisconnectedSpace.
The map `v : Z →ₜ* H` is the node's continuous homomorphism, and `v generator` is tau.

Clause correspondence:

- `invariants A G J` is the recorded `ProductInvariants` specification, realized by
  `productInvariantsExist`. Its image quantifies over every profinite base change; its
  residual, transpose and untranspose fields are precisely the invariant-inclusion
  normalization. Exact projection inflation and Grothendieck action-category instances
  come from the recorded scalar action calculus and product-action theorem. The discrete
  factor is included: no assertion that G times Z is profinite is used.
- `derived A G J` right derives that functor in the full ordinary action category.
  `productMap v` is identity on G and v on the second factor. `invariantRestriction`
  is uniquely determined by the invariant inclusions, and `beta` is its canonical
  right-derived pullback. `unit` and `scalarUnit` are the actual recorded computation
  units with explicit endpoints. `betaNormalization` is its actual computation-unit equation;
  `betaShift` records compatibility with canonical shifts and triangle boundaries.
  `degreeZeroUnit` is the canonical unit transported through the single-complex and
  homology identifications. `degreeZeroExist` fixes its inverse by eta-zero followed
  by e equals identity, and `betaDegreeZero` states the actual invariant inclusion.
- `TotalModel` has terms N^n plus N^(n-1), the exact matrix
  (d_N x, (T-1)x - d_N y), diagonal maps on the two summands, and the actual invariant
  row inclusion. `generatorEndExist` fixes T on every generalized section.
  `descent` is ordinary relative derived invariants restricted to D+, with its canonical
  triangulated structure. `HasComparison` specifies a natural
  isomorphism whose inverse satisfies theta alpha = Qb on EVERY bounded-below complex.
  This pins higher degrees as well as H-zero. `relative_cyclic_restriction_model`
  asserts existence of this explicit total and its normalized comparison with that descent.
  The comparison predicate also pins the signed shift coordinates (x,(-1)^s y).
- `lambda` includes the canonical Qh-Q comparison. `cyclicMap` is beta followed by
  lambda inverse, with the exact restriction/single-complex comparison, so its target
  is precisely the two-column complex with differential tau-1 on a module.
- `forgettingProperties` states exactness and conservativity of residual forgetting on
  modules and ordinary derived categories, and preservation of injectives when the
  residual group is profinite. `forgetInvariants` is fixed on the actual inclusions;
  `forgetDerived` is fixed by its computation units on all complexes. `forgetBeta`
  is equality of derived arrows with the recorded scalar restriction, not merely
  equality on cohomology. `forgetDerivedShift` supplies the canonical shift compatibility.
- `forgottenLambda` is the actual forgotten comparison. `forgetLambda` identifies it
  on EVERY bounded-below complex with the scalar comparison realized by a trivial
  residual group, using the unique two-coordinate chain isomorphism.
  `addTrivialResidual`, `unitResidualIso` and `scalarizationIso` supply the canonical
  projection/inclusion identity, with identity underlying module maps.
  `DiscreteBridge` fixes the
  equivalence with the recorded rank-one lattice action by its underlying module,
  positive-generator action and invariant inclusion. `lowerDerived`/`lowerQ` are the
  canonical localization transport from the lattice's standard larger universe to
  the scalar calculus's smaller Hom universe. `DiscreteDerivedBridge` fixes the
  corresponding derived transport by units on all complexes. `latticeCompatibility`
  compares with the recorded `KoszulModel` and `Comparison`, choosing the scalar
  witness by the SAME row construction as the node's proof requires. It does not infer
  uniqueness from H-zero alone. The two module coordinates are pinned explicitly.
- `HasCoefficientComparison` pins the underived invariant comparison on its inclusions
  and its derived comparison on computation units. `coefficientBeta`,
  `coefficientLambda`, and `forgetCoefficient` state the actual coefficient squares,
  without a flatness or preservation-of-injectives hypothesis for scalar restriction.
  The scalar comparison's shift condition and the shift-compatible relative comparisons
  retain canonical boundaries. Naturality of c follows by composing these squares.
- `trivialCyclic` is the real complex [R -> 0 R]. `evaluation` is specified on all
  generalized sections: the canonical degree-zero identification, evaluation at
  v(generator) in degree one, and zero in degrees at least two. It is constructed as
  the unique cochain map with these equations. `barAugmentation` is the canonical map
  into the resolution-zero row of the EXISTING compatible bar total. `barEta` is the
  EXISTING invariant-inclusion bar comparison, expressed in the scalar localization
  using its injective resolution and normalized invariant-functor comparison.
  `trivialCyclicMap` is the relative c with residual group PUnit, transported along
  the original module identity and the coordinate-normalized trivial total iso.
  `barEvaluation` says Q(j) followed by eta inverse followed by c is Q(evaluation),
  for EVERY compatible nonnegative equivariant injective resolution. Neither j nor
  beta is asserted invertible. Only the bar augmentation from invariants is inverted.

Recorded dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its action and regular module.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `inflate`,
  `ProductInvariants` and its inclusion/image/residual/adjunction fields.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `Q`, its localization, signed shifts and cone triangles; the size convention is expressed
  by arbitrary explicit universes rather than an extra object.
- `Sheaf.CategoryTheory.CondensedProductActionInflation`: `product_action_inflation`.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: scalar restriction and
  coefficient calculus; its imported `CondensedDerivedInvariants` provides the recorded
  normalized `invariants`, `derived`, `scalarAction`, `scalarGroupDerived`, `groupMap`,
  `coefficientMap` and the exact-action instances. Their signatures/docstrings were read.
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`: the actual `Equivariant`,
  `invariants`, `derivedInvariants`, `derivedUnit`, `KoszulModel`, `Comparison`, and
  `discrete_lattice_koszul_resolution`, including all ordered-subset coordinates.
- `Sheaf.CategoryTheory.CondensedDerivedInvariantBar`: `condensed_derived_invariant_bar`;
  `CondensedEquivariantBarData` supplies `InternalFunctions`, `BarDiagram`, `cochains`,
  `doubleComplex`, `totalCochains`, `Model` and its normalized total augmentation. `BarModel` supplies the recorded
  larger localization explicitly; `barFunctions`, `barInvariants`, `barDiagram`,
  `barAugmentationData` and `barTotalAugmentation` project exactly that existing data.
  `LargeDerived` and `largeQ` likewise supply the recorded scalar universe explicitly.

Edge cases checked: trivial residual/source groups, the homomorphism sending the cyclic
generator to identity, a nonfaithful cyclic action, zero coefficients and zero modules,
and complexes with negative but finite lower bounds. The second total coordinate in degree
n is n-1, so for modules the generator differential is in degrees zero to one with the
positive sign. In the bar identity the original coefficient action is trivial although
resolution terms need not be; the proof uses their action-dependent bar differential.
No dense-image or beta-isomorphism assumption appears. Lattice and scalar localization
universes are transported, not identified. The coefficient ring and site universes have
not been collapsed.

Searches performed through the prescribed msearch wrapper:

- LeanFinder, `Relative derived invariants with a residual condensed group action are
  computed by the two term cyclic complex and forgetting preserves normalized derived
  restriction`: eight hits, ordinary group-cohomology inflation/restriction and
  continuous topological-module cochains; none is this internal condensed relative model.
- Loogle, `groupCohomology, rightDerivedFunctor`: zero hits; the service reports
  unknown identifier rightDerivedFunctor. This is not recorded as evidence of absence.
- Mathlib grep, `cyclic.*(invariant|derived)|(invariant|derived).*cyclic`: three finite
  cyclic representation/homology hits; no internal condensed relative cyclic model.
- `rg` in the project's WeilConjectures and Sheaf source for relative cyclic names and
  this blueprint id: no existing declaration for the item. The later
  `IndUnipotentProcyclicDifference` proof docstring names this node as its prerequisite.
  The exact id grep in WeilConjectures has no hits. The imported scalar nodes provide
  the component APIs, not the relative statement, so none is rebound as existing.

Compilation: all eight delivered modules passed separately through scompile.py against
the live published library; only expected sorry warnings occur. The final main module
also passed after replacing statement-level lets by the named scalarCyclicInput and
trivialResidualCyclicInput constructions. Delivery dry run: deliver2.py --no-push returned OK, confirming server preflight
and compilation of all eight modules (dry-run commit 60d130b3c2e). The preflight
signature records exclude the terminating := / where, as its exact comparison requires.

## Second reading by NB

The dispatcher explicitly prohibits starting other agents and assigns independent delivery
review to the maintainer. This section records the final in-worker clause check, not an
independent worker review. The source blueprint paragraph (3) and the node's agent-formulated
18-step expansion were read. The module keeps the node statement unchanged. The checks
above distinguish generalized condensed actions from abstract discrete actions, fix every
comparison by its inclusion/units, retain the signed two-column total and actual derived
bar identity, and include the source's trivial-group/zero-ring cases. Compilation fixes
must preserve these correspondences; final validation is recorded above once complete.

## New nodes

All seven nodes use the source paragraph and the assigned node's explicit relative
rank-one construction. They do not assert that the blueprint paragraph already states
this auxiliary theorem. Their nearest blueprint ancestor is null, as verified by
`tools/blueprint_refs.py ancestor`. They are coherent definition interfaces needed by
the theorem; the original statement remains unchanged.

- `def-sfb-relative-derived-invariants`, module `RelativeDerivedInvariants`: the
  normalized product invariant functor, ordinary derived functor, actual relative
  restriction beta, cyclic generator, and underlying forgetting functors. Existing
  `ProductInvariants` is reused, with no private action-category definition.
- `def-sfb-relative-cyclic-total`, module `RelativeCyclicTotal`: the explicit total
  coordinates, differential and augmentation, bounded-below localization, canonical
  descent, invariant-normalized comparison predicate, lambda and c.
- `def-sfb-relative-invariant-forgetting`, module `RelativeInvariantForgetting`: the
  unique inclusion-normalized invariant and computation-unit-normalized derived
  forgetting isomorphisms, their restriction square, forgotten lambda, and the
  identity-normalized inflation/forgetting transport for a trivial residual group.
- `def-sfb-relative-coefficient-comparisons`, module `RelativeCoefficientComparison`:
  the normalized underived/derived relative scalar comparisons and coefficient total.
- `def-sfb-relative-bar-data`, module `RelativeBarData`: the actual trivial cyclic
  complex, evaluation and resolution-zero-row augmentation maps, and canonical
  invariant-normalized bar comparison in the scalar localization.
- `def-sfb-relative-trivial-cyclic-map`, module `RelativeTrivialCyclicMap`: the
  original-module and coordinate identifications transporting relative c for G=1.
- `def-sfb-relative-lattice-bridge`, module `RelativeLatticeBridge`: the exact
  underlying-module/generator-normalized lattice equivalence datum, canonical
  localization-universe transport, its all-complex derived-unit bridge, and the
  two actual module coordinates.

Searches for these interfaces: LeanSearch on condensed relative derived invariants,
cyclic total, residual forgetting, coefficients, bar evaluation and lattice bridge
returned ordinary-ring condensed modules and continuous topological modules; LeanFinder
returned abstract ordinary-ring finite cyclic representations and bar resolutions.
Neither supplies these internal-module relative interfaces. Mathlib grep for
`relative.*(cyclic|invariant|bar)|Relative(Cyclic|Invariant|Bar|Lattice)` returned two
unrelated metric/Haar references. Source and DAG searches found the assigned theorem
and its downstream citer, with no definition node or declaration for these interfaces.
The exact queries and returned declaration/file lists are in each node's mathlib_searches.
