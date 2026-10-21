## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalShift` states
`AlgebraicGeometry.Scheme.coefficientProEtaleTor_interval_shift`, with `sorry`, and defines
only the helper `coefficientProEtaleTorTensorTest`. That helper composes the existing
single-complex functor and derived localization in the second argument with the existing
ringed-site derived tensor. It has real functor data; it makes no arbitrary choice of maps
or resolutions and introduces no alternate tensor product.

The mathematical node is unchanged. The small site used is the recorded
`coefficientProEtaleModelTopology.{u,v} Y`, the original small pro-etale site transported
by `AsSmall`. Its coefficient universe is `max v (u+1)`, independently of the scheme
universe `u`. `ConstantCompletion.constant` is precisely its constant commutative ring
sheaf; `ConstantCompletion.Mod` is its ordinary `SheafOfModules` category, and
`ConstantCompletion.D` is the unbounded standard derived localization. No constructibility,
Noetherian, finite-ring, boundedness, or flat-cohomology hypothesis appears.

Clause-by-clause rendering:

- A scheme Y: `(Y : Scheme.{u})`; an arbitrary commutative ring A:
  `(A : Type (max v (u+1))) [CommRing A]`. Smaller coefficient rings are represented by
  their usual universe lift, as in the recorded coefficient-sized interface. There is
  no equality imposed between independent site and coefficient sizes.
- K and L range over `ConstantCompletion.D (ConstantCompletion.constant ... A)`.
  The second variable of `coefficientProEtaleTorTensorTest` ranges over all
  `ConstantCompletion.Mod` objects and is sent to the single complex in degree zero
  and then to its derived object.
- For every integer m, the first conjunct is `Nonempty` of a natural isomorphism
  from `(shiftFunctor D m).prod (𝟭 Mod) ⋙ coefficientProEtaleTorTensorTest Y A` to
  `coefficientProEtaleTorTensorTest Y A ⋙ shiftFunctor D m`. Its component at `(K,N)`
  is exactly `(K[m]) tensor^L N ≅ (K tensor^L N)[m]`. The source category is the
  product category, so naturality includes arbitrary morphisms in both K and N.
- For every i,m, the second conjunct similarly gives a natural isomorphism from
  the shifted tensor test followed by `coefficientModelCohomology R i` to the
  tensor test followed by `coefficientModelCohomology R (i+m)`. This abbreviation
  is exactly Mathlib's `DerivedCategory.homologyFunctor`, on the standard localization.
  Its components are the stated cohomology-sheaf isomorphisms, natural in both variables.
- The third conjunct quantifies over every K and every integer a,b,m, takes precisely
  `a ≤ b`, and states
  `HasCoefficientProEtaleTorAmplitude Y A K a b ↔
   HasCoefficientProEtaleTorAmplitude Y A (K⟦m⟧) (a-m) (b-m)`.
  Both directions and the negative sign on both translated endpoints are explicit.
- The fourth conjunct quantifies over every K,L and isomorphism `_e : K ≅ L` and
  every ordered interval, and gives the corresponding equivalence with unchanged bounds.
  `_e` is a genuine isomorphism hypothesis; its name is unused only because this
  statement asserts the equivalence rather than the map inducing it.
- The fifth conjunct quantifies over every N and asserts
  `Nonempty (T.obj (0,N) ≅ 0)`, with the mixed-universe product category, its
  factor types, and the codomain supplied explicitly to `Functor.obj`. These are
  the categorical zero objects in the same standard derived category. This avoids
  Lean selecting the uniform-universe product category for factors with different
  Hom sizes. No equality of these universes is imposed.
- The last conjunct is `HasCoefficientProEtaleTorAmplitude Y A 0 0 0`.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasCoefficientProEtaleTorAmplitude`,
  `CategoryTheory.HasCoefficientModelTorAmplitude`, and
  `CategoryTheory.coefficientModelCohomology` (the last is a direct abbreviation for
  the Mathlib cohomology functor).
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, the existing ordinary
  K-flat tensor on intrinsic module-sheaf derived categories, already recorded by
  proof dependency `lem-weil-pbc-site-derived-tensor-descent`. The item's `lean.note`
  explains this presentation; `def-weil-derived-tensor` retains its live NE record.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its representing-complex comparison
  `DerivedCategory.homologyFunctorFactors`, already the dependency node's
  `mathlib_match`. The dependency's sf-Weil cohomology record is not applicable to
  arbitrary ordinary ringed sites, but its exact Mathlib match is usable and unchanged.
- Proof-only imports retain `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`,
  `SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`, the descent theorem,
  `CochainComplex.mapBifunctor` and `Functor.shiftIso`, following every stated proof dependency.
  The theorem docstring reproduces the five proof steps with their dependency ids.

Edge cases checked before writing: m=0 gives the unchanged interval; m=1 sends [0,0]
to [-1,-1]; m=-1 sends it to [1,1]. Singleton intervals a=b remain allowed. The
converse follows by i=j-m, not merely by an inclusion of intervals. A=0 and an empty
scheme cause no restriction: the quantifiers and zero conclusion remain meaningful.
There is no nonempty-site or nonzero-ring hypothesis. Arbitrarily unbounded K and
arbitrary N remain allowed. The ordered-interval hypothesis is exactly the one in the
node and in Stacks 08FZ.

Searches for an existing full statement:

- `msearch.py ... leansearch 'Derived tensor commutes with shifts and Tor amplitude interval shifts by minus m'`:
  eight hits, including `Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt`,
  adjunction shift comparisons, and `NatTrans.CommShift₂.commShift_app`. None states
  the complete Tor-amplitude result for the recorded intrinsic module-sheaf category.
- `msearch.py ... leanfinder 'Tor amplitude interval of shifted derived tensor sheaves translates by minus m'`:
  eight hits, including `CochainComplex.isLE_shift`, t-structure bounds and derived
  single-complex bounds. No full matching statement.
- `msearch.py ... loogle '"torAmplitude"'`: zero hits. The earlier combined
  `"torAmplitude", "shiftIso"` query likewise yielded no usable matching result.
- `msearch.py ... grep 'Has.*TorAmplitude|torAmplitude.*shift'`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  found no declarations with either proposed new name. Searching the item id in
  `lean/WeilConjectures` found no match. Concept searches found the recorded Tor
  predicates and upstream `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn.shift`;
  the latter is only the forward implication in an abstract coefficient category,
  not this node's complete statement. Existing `PullbackTorAmplitude.lean` has a
  private proof of ordinary Tor invariance, not a public matching statement.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`definition-derived-tor` (Tag 06YU) and `definition-tor-amplitude` (Tag 08FZ).
The source defines exact tensor on the unbounded category and tests all module sheaves.
No mathematical statement correction, new nodes, or disputed assertion is needed.

## Second reading by Q33

I re-read the node and the finished signature separately after drafting, checking each
conjunct against its clause: both natural isomorphisms use product-category functors;
the cohomology target is i+m; the translated bounds are a-m,b-m; the interval assertion
is an iff; the isomorphism assertion keeps a,b unchanged; and both zero clauses are
present. The tensor helper uses degree zero, the same intrinsic coefficient ring and
standard localization as the Tor predicate. The initial compile exposed unresolved
universe choices in that helper and missing scoped zero-object notation; these were
made explicit without changing any mathematical hypothesis. The zero tensor clause
uses the actual mixed-universe product instance and the categorical derived zero. No clause mismatch was
found. This is a worker self-review; the dispatcher prohibited starting other agents,
and the maintainer performs the independent review of the delivery.

## Repair of return L, head c5a5b60e3bd7

H13 repaired: restored `def-weil-derived-tensor.json` byte-for-byte from the live
repository, retaining NE's `existing: true` binding to
`AlgebraicGeometry.ProEtale.derivedTensor`. Removed the Dependency modules section.
The item's `lean.note` now explains the already published intrinsic tensor used
directly by its helper and by `HasCoefficientProEtaleTorAmplitude`, citing the
existing proof-dependency record `lem-weil-pbc-site-derived-tensor-descent`.
There is no dependency-record change in this delivery. The Lean file is unchanged.

Self-check after the repair: re-read the complete node statement and the Lean
signature. The comparisons are natural isomorphisms on D × Mod, expressed by
`Nonempty` as the node's existence wording requires; cohomology changes i to i+m.
The ordered interval translates to [a-m,b-m] in an iff; isomorphism invariance
keeps [a,b]; zero tensor and amplitude [0,0] are both stated. The proof-only imports
remain, and `coefficientModelCohomology` is the standard homology functor recorded
in the cohomology dependency's Mathlib match. No further mathematical change is
needed. The initial saved-packet dry run passed; the repaired packet is compiled
and dry-run checked again before delivery.
