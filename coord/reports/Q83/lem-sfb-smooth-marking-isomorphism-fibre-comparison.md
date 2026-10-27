## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothMarkingIsomorphismFibreComparison` states
`AlgebraicGeometry.smooth_marking_isomorphism_fibre_comparison`. Its sole postponed
proof is `sorry`. Definitions contain actual scheme maps, actual functors and structures;
none chooses data from an existence theorem. The node statement is unchanged. Its statement dependencies gain the already-landed
`def-sfb-moduli-chart-normalization`, whose canonical `moduliTwoFiberLift` constructs
the specified comparison functor without duplicating the generic 2-product lift.

Source read: Knudsen II, Section 2, Corollary 2.6, printed p.179 (PDF page 58
of the linked combined scan), states the inverse relationship of contraction and
stabilization. The following proof explicitly uses the universal-curve interpretation.
The node's five-step argument supplies the iterated comparison. I read the recorded
Knudsen declaration and its complete proof docstring, and the stable moduli objects,
cartesian arrows, actual pullback constructions, and 2-fibre-product definition.

Hypothesis and clause correspondence:

- Fields `k`, `F` and the field extension are `[Field k] [Field F] [Algebra k F]`.
  The scheme map is `Spec.map (CommRingCat.ofHom (algebraMap k F))`. The single universe `u`
  is the recorded scheme-universe convention: any given fields, schemes and test
  schemes can be placed in a common universe; no bound between independently
  quantified smaller test universes is introduced.
- `g n : ℕ` and `hg : 2 ≤ g` render the nonnegative marking count and genus bound.
- The given `T_r`, classifying maps and stable families are `D.family r`, with base
  `(D.family r).base : Over (Spec (.of k))`. The actual classifying functor is the
  dependency's `StablePointedModuli.familyMap`. `Fin (n+1)` includes both endpoints.
- The maps `q_r` are `D.transition r`. `D.knudsen r` packages exactly the witnesses
  and all normalization clauses of the recorded Knudsen existential theorem,
  including its actual contraction, section equations, inverse functors, representing
  comparison, smooth identity, fibre geometry, and stability under base change.
  It adds no geometric hypothesis: those are the specified forgetful-and-stabilizing
  maps in the node. A different arbitrary functor cannot masquerade as forgetting.
- `D.comparison r` is the specified natural 2-isomorphism from the classifying map
  after `q_r` to the forgetting of the next family. `squareComparison` sends a test
  map to that very triple in `moduliTwoFiberProduct`, including that isomorphism.
  The functor is the existing `moduliTwoFiberLift`, using Mathlib's
  `BasedNatIso.mkNatIso` to package the recorded `ModuliTwoIso`.
  `D.cartesian r` says this comparison functor is an equivalence, precisely the
  specified 2-cartesian square, rather than an unrelated equivalence of categories.
- `D.baseToZero (Fin.last n)` is `q`: its recursion composes each `q_r` toward zero,
  starting with the identity. `D.curveToZero` similarly composes the actual
  contraction maps. `stepContraction` uses the contraction on the identity pullback,
  the inverse of the given comparison at the identity test map, and the first
  pullback projection, so it is the induced curve map, not an arbitrary substitute.
- The fixed curve is `C` with structural morphism `f`. `IsConnectedCurve f` means a
  nonempty connected separated finite-type curve of dimension exactly one;
  `Smooth f`, `IsHProjective f`, `GeometricallyConnected f` give the remaining
  hypotheses. `hgenus` is `Scheme.arithmeticGenus F C = g`, namely dimension of
  H^1 of the structure sheaf; on smooth projective connected curves this is genus.
- The points are `p : Fin n → (Spec F ⟶ C)`, `hp` says they are F-sections, and
  `Function.Injective p` is ordered distinctness. For rational sections over a
  field, distinctness gives disjoint images; this remains disjoint after base change.
- Every F-scheme is `B : Over (Spec (.of F))`. `IsoPair` stores an actual k-map
  `map`, a scheme isomorphism `iso` from the dependency's actual family pullback
  to `pullback f B.hom`, its base equation `base_equation`, and each labelled equation
  `markings`. The unpointed side uses the same definition with `Fin 0` and the
  empty family of points. There are no orbit sets, skeletons or permutations.
- `∃ e : ∀ B, IsoPair ... n ... B ≃ IsoPair ... 0 ... B` is the bijection of sets,
  with actual two-sided inverses supplied by `Equiv`.
- The first conjunct's map equation is `(e B x).map = x.map ≫ D.baseToZero ...`.
  Its second equation says that the pointed identification followed by the actual
  composite contraction is the unpointed identification, after projection from
  the canonical pullbacks. These projections plus the base equation determine the
  map to the pullback uniquely, so this specifies exactly the induced beta.
- The second conjunct is the inverse-marking formula: the base-changed `p_i`
  followed by `y.iso.inv` and the projection to `X_0` equals the inverse pair's
  i-th marking followed by the actual contraction to `X_0`. This is the node's
  identification of sections with `beta^{-1} p_i` on the unchanged smooth curve.
- The last conjunct is naturality for every `a : B' ⟶ B`. `IsPullbackPair` spells out
  both precomposition of the map and the canonical cartesian-arrow equation for
  the isomorphism, using the dependency's `pullbackCurveMap` and the explicit
  `fixedCurveMap`. The equivalence of these pullback relations expresses pullback
  compatibility in both directions of the bijection. It is not just a bijection
  after passing to isomorphism classes or after restricting to geometric points.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (exposed by the Knudsen
  module): `StablePointedModuli`, its `.Hom`, `.forget`, `.pullback`, `.sections`,
  `CategoryTheory.ModuliTwoIso`, `moduliTwoFiberProduct`, `discreteModuli`,
  `discreteModuliMap`. These are used directly, not copied.
- `Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve`:
  `StablePointedModuli.based`, `.familyMap`, `.totalScheme`, `.pullbackCurveMap`,
  `StablePointedUniversalCurve`, `.based`, `.forgetful`, `.representedPoint`,
  `.HasFiberGeometry`, and the witness signature of
  `exists_knudsen_pointed_forgetful_universal_curve`.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `CategoryTheory.moduliTwoFiberLift`.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, `pullback.map`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsConnectedCurve`; its imported
  `Cohomology.EulerChar`: `Scheme.arithmeticGenus`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`.

Auxiliary declarations all belong to the item's isomorphism-fibre comparison:
`Contraction` is a bundling of the existing Knudsen witnesses, `Tower` the specified
finite diagram, `IsoPair` the node's pair set, and the remaining definitions its
canonical maps and comparison relation. No independent new mathematical notion or
DAG definition node is introduced, and no dependency interface repair is needed.

Edge cases checked: `n=0` leaves an empty transition index and both composite maps
are identities; its pair sets coincide and there is no inverse-marking condition.
`n=1` composes exactly one specified comparison and contraction. Empty and nonreduced
B are allowed by unrestricted `Over (Spec F)` and scheme pullbacks. No rational point
on a fixed ground field is assumed except the explicitly supplied points; for `n=0`
there are none. A curve with nontrivial automorphisms gives distinct `IsoPair.iso`
values, and none is quotiented out. Characteristic is unrestricted. Distinctness of
points excludes collisions exactly as in the node, while the tower families may be
singular: the smoothness assumption is only on the fixed comparison curve.

Searches made (raw remote-search output is in `searches.jsonl`):

- LeanFinder: “Natural bijection between actual labelled smooth curve isomorphism
  pairs and unpointed pairs in a cartesian forgetful tower”: eight hits about
  Weierstrass variable changes, affine-space maps and elliptic j-invariants; none
  states this genus-at-least-two tower comparison.
- Loogle: `"StablePointedModuli"`: zero hits.
- LeanSearch: “isomorphism fibre of a cartesian square of groupoids is a bijection”:
  eight hits, including categorical-pullback comparisons and generic fibre lifts;
  these supply category vocabulary, not the marked stable-curve assertion.
- msearch grep: `forget.*mark|pointed.*isomorph|stabili[sz].*curve`: zero Mathlib hits.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for smooth marking,
  stable pointed, Knudsen, isomorphism fibres, forgetful towers, and the item id:
  found the two recorded dependency modules and related contraction evaluations;
  no existing statement of this comparison. The generic comparison-construction
  helper `moduliTwoFiberLift` was found in ModuliChartNormalization and is reused. The exact item-id search in
  WeilConjectures and `dag/lean_names_upstream.json` found no declaration.

No STATEMENT-DISPUTED issue or node fault found. The former example CompactObject
module is withdrawn; its node now records the canonical upstream declaration.
The delivered module follows current module-mode conventions instead.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
