## Worker report

The module `Sheaf.Paper.PurityTensorMapNaturality` states
`WeilConjectures.PurityFiniteSetting.purityTensorMap_naturality`. Its sole theorem
has proof `sorry`. The two other declarations contain real data: the inverse
ordinary adjunction image of the existing specified theta, and the coefficient-square
proposition. No new independent notion or dependency replacement is introduced.
The natural-language statement, proof and proof dependencies remain unchanged.

### Hypotheses and clauses

- The fixed primes, finite-field power and algebraic closure are the existing
  `P.field : FiniteFieldDatum`: `prime`, `exponent_pos`, `cardinality_eq`,
  `card_base` and `isAlgClosure` supply precisely those conditions.
  `P.coefficients` fixes the prime ell distinct from p and its coefficient closure.
  `P.extension` is an intermediate field in that fixed closure, with the existing
  `P.finiteExtension` instance; `P.level_pos` says `1 ≤ P.level`.
  `P.Ring` is the existing `Padic.coefficientExtensionRing`, not an arbitrary ring;
  `P.Coefficient = ULift P.Ring` is its standard size lift. There is no ramification
  divisibility restriction. In particular n=1 and all ramified extensions are included.
- X and Y are `Scheme.{u}` over `Spec (.of P.field.k)` using the `Over` instances.
  Each structure morphism has `LocallyOfFiniteType`, `QuasiCompact` and
  `IsSeparated`, exactly separated finite type over k.
- `f : X ⟶ Y` and `f.IsOver` retain the specified k-morphism;
  `IsSeparated f`, `LocallyOfFiniteType f` and `QuasiCompact f` are its stated
  separated finite-type conditions. `d : ℕ` and `SmoothOfRelativeDimension d f`
  give pure nonnegative relative dimension and smoothness. The declaration of
  `SmoothOfRelativeDimension` and the lemma `SmoothOfRelativeDimension.smooth`
  were read in Mathlib; no additional definition of smoothness is made.
- The constant-module derived categories are literally
  `DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u+1} P.Coefficient))`.
  These are the ordinary small pro-etale sites with objects in universe u+1 and
  morphisms in u. No equality of site universes is imposed.
- K and K' range over the ORIGINAL pro-etale objects. `_hK` and `_hK'` use the
  existing finite-coefficient `ProEtale.DerivedCategory.constructibleFiniteTor`,
  as the recorded cohomological-smoothness interface does. `u : K ⟶ K'` is
  arbitrary; it is never required to be an isomorphism.
- K0, K0', e, e' and u0 give any compatible etale presentation of those objects
  and the arrow. `_hu` says exactly `nu_Y^*(u0) ≫ e'.hom = e.hom ≫ u`.
  This is a coordinate description, with every original u retained, not a new
  mathematical restriction: finite constructible objects have etale origins, and
  comparison is fully faithful on their bounded-below representatives. Thus u0
  exists uniquely for each e and e'. The assertion is for EVERY such presentation,
  rather than a fixed chosen lift, so it also covers identity presentations and
  arbitrary changes of representing isomorphism.
- The compactification is supplied explicitly as
  `(P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification`.
  Its declaration constructs the existing Nagata compactification from the given
  finite-type target. No `HasCompactification`, compactness or dimension-bound
  assumption is added to the theorem.
- The relative dualizing object is the existing `P.diagonalDualizing f`, whose
  DEFINITION is exactly the transported exceptional image of the degree-zero
  coefficient unit. Despite its name, it contains no diagonal orientation:
  the body applies `sfFiniteExceptionalAt` to the constant unit. The existing
  canonical `diagonalDualizingComparison` identifies it with the etale model.
- `P.smoothPurityPullback f` is the existing ordinary fixed-scalar derived pullback,
  and `smoothPurityTensor P.Coefficient X` is the existing pro-etale derived tensor.
  The first conclusion uses its `.map ((P.smoothPurityPullback f).map u)).app omega`,
  which is precisely m tensor identity on omega.
- The map in that conclusion is the EXISTING `P.smoothPurityTheta f K K0 e`.
  Its full definition was read: canonical pullback/tensor comparison, comparison
  of `smoothPurityEtaleTheta`, and the right-adjoint comparison unit. The etale
  helper inserts source symmetry before `Etale.dualizingComplexTensorMap` and
  the canonical degree-zero-unit identification. Expanding the latter map gives
  the inverse projection, counit tensor identity and left unitor. Thus it is
  exactly the specified counit mate, not an arbitrary morphism or endpoint iso.
- The first conjunct reads theta_K followed by `(P.smoothPurityExceptional f).map u`
  equals `(m tensor identity)` followed by theta_K'. In Lean composition order
  this is exactly the first displayed equality in the node.
- `purityTensorCoefficientInput` is the inverse adjunction image of this already
  specified etale theta. Inverse adjunctness cancels its defining transpose, so
  its value is exactly the displayed inverse-projection/counit/unitor input a_K,
  with the unit normalization and source ordering retained. It uses no `sorry`
  and no mere existence choice.
- The second conjunct is `PurityTensorCoefficientSquare`. Unfolding it gives
  `nu_Y^*(a_K0 ≫ u0) = nu_Y^*(F(m0 tensor identity) ≫ a_K0')`.
  Both sides are actual pro-etale derived morphisms. The natural normalized
  compact-support site comparison identifies their common source with
  `Rf_!(M_K tensor omega)`; the representing isomorphisms identify the target
  with K'. Its naturality and `_hu` identify this equality with exactly
  `a_K ≫ u = Rf_!(m tensor identity) ≫ a_K'` on the original objects.
  This is the equivalent coefficient square in the same comparison coordinates
  as the recorded `def-pur-co-smoothness`. The natural bounded Hom bijection
  identifies it with the first conjunct, and its injectivity gives the converse.
  Asserting both equations therefore adds no stronger conclusion.
- No Tate twist, orientation, diagonal-purity isomorphism or smooth-purity map
  occurs in the assertion or in the definitions of the map helpers it uses.
  The helper theta already lives in the larger `SmoothPurityMap` module; that
  is a file location, not use of its orientation-dependent declarations.

### Dependency declarations

All three original statement dependencies and their full relevant declarations were read:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`, `.Ring`, `.Coefficient` and their ring
  instances, with the field/coefficient structure in `Sheaf.Paper.FiniteFieldFiber`.
- `def-pur-co-smoothness`: `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`,
  `AlgebraicGeometry.ProEtale.IsCohomologicallySmoothFiniteCompared`,
  `finiteComparedDualizing`, `finiteComparedTensorClause`, and
  `WeilConjectures.PurityFiniteSetting.finiteComparedCompactification`.
  This uses the actual named etale tensor counit mate in comparison coordinates.
- `def-sbc-smooth-morphisms`: Mathlib `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.SmoothOfRelativeDimension`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (the node also records `Etale`).

The item gains the already landed `def-pur-smooth-purity-map` in `stmt_deps` solely
to reuse its canonical, orientation-free helpers instead of defining theta again:
`Sheaf.Paper.SmoothPurityMap`, `WeilConjectures.PurityFiniteSetting.smoothPurityTheta`,
`smoothPurityEtaleTheta`, `smoothPurityExceptional`, `smoothPurityPullback`,
`smoothPurityTensor`, and the canonical unit/tensor comparisons they use.
`P.diagonalDualizing` and its unit comparison come through that module from
`Sheaf.Paper.PurityDiagonalDualizingObject`. There is no path from that added
node through statement/proof dependencies to the item (checked by traversing the
live JSON graph), so this does not close a dependency cycle.

All recorded stated proof modules are imported without `public`:
`Sheaf.Paper.SfPreservationClass`, `Sheaf.Paper.PullbackTorAmplitude`,
`Sheaf.Paper.FiniteCoefficientTensorCtf`,
`Sheaf.Algebra.Homology.RingedDerivedTensorNative`,
`Sheaf.Paper.CompactSupportProjectionFormula`,
`Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.
The theorem docstring gives the node's four proof steps, including the finite-Tor
operation-domain check, naturality of symmetry/inverse projection, the coefficient
square, and the two Hom-naturality identities with injectivity for the converse.

### Edge cases

Checked before writing and again against the final signature: d=0, empty X,
empty Y (and hence empty X for a morphism to Y), zero K or K', u=0, u=identity,
non-invertible u, the smallest level n=1, and ramified E. No `Nonempty`, positive
dimension, nonzero object or etale-morphism assumption excludes these cases.
All representing isomorphisms e/e' and their compatible morphism lifts are allowed;
none is forced to be identity. The canonical quotient and original site universes
are retained. `set_option autoImplicit false` ensures every binder/universe is explicit.

### Searches

Searches used the prescribed `msearch.py NE lem-pur-tensor-map-naturality` wrapper.

- LeanFinder: `The projection formula and counit tensor transpose from derived pullback
  tensor the dualizing complex to exceptional inverse image is natural in the coefficient
  complex`. Eight results: `SheafOfModules.pullbackObjUnitToUnit`, the
  `pullbackObjFreeIso_hom_naturality` family and `CategoryTheory.ExponentiableMorphism`
  evaluation/coevaluation results. None states this square.
- Loogle: `CategoryTheory.Adjunction.homEquiv_naturality_right`. One result, the
  expected generic Hom-naturality theorem. Its signature and neighboring left-naturality
  formulas in Mathlib were read. It is one ingredient, not the present statement.
- Mathlib grep: `tensor.*(counit|exceptional)|exceptional.*tensor`, in `CategoryTheory`.
  Fourteen hits in Comon_, monoidal functors, closed functors and Hopf_. None has
  these finite-coefficient functors and specified canonical maps.
- LeanSearch: `Naturality of the adjoint transpose of the projection formula counit
  tensor map in cohomologically smooth sheaf theory`. Eight hits, headed by
  `CategoryTheory.Adjunction.counit_naturality_assoc` and `counit_naturality`,
  with generic presheaf/closed-category results. No exact match.
- Project/source rg: `coSmooth|CoSmooth|co_smooth|tensorMap|tensor_map|Tensor.*Naturality|pur-tensor-map-naturality`
  and narrower `dualizingComplexTensorMap|tensorTraceTranspose|tensorFormula|tensorTranspose|finiteComparedTensor`
  in the prescribed `lean/Sheaf`, `lean/WeilConjectures/SixFunctors` and related
  modules. Read `UpperShriekCanonicalMaps`, `ProjectionTensorMap`,
  `CohomologicalSmoothnessFiniteComparison`, `TensorTraceTranspose` and the
  orientation-free helpers in `SmoothPurityMap`. The generic
  `projectionTensorMap_naturality_right` is an ingredient but does not state both
  present squares on arbitrary original pro-etale objects. `tensorTraceTranspose`
  concerns tensoring an arbitrary trace with additional trace/projection-domain data;
  it neither states this exact theorem nor provides the named theta naturality square
  with both equivalent formulations. Existing map helpers are reused.
- Exact item-id search in both Lean roots found no declaration. DAG search finds
  the item and its existing citer `prop-pur-smooth-purity-naturality-cover`.

The blueprint source was read at main-20261015,
`sec-smooth-purity/sk-thm-smooth-purity/prop-pur-smooth-purity-naturality-cover.proof.md`:
its first sentence invokes precisely naturality in K of the tensor formula.
No statement correction or disputed assertion is needed. The previous worker's
stage-1 live-wins message is not a stage-2 obstruction: the live item has a PASS
stage-1 split and no Lean binding, and this delivery does not alter that split.

### Validation

The module passed the prescribed server `scompile.py` in both sandbox and library
module names, with no warnings or errors. The only theorem has `sorry`; both
helper definitions have concrete bodies. Diagnostic `#check` commands were removed.
The delivery dry run and final delivery are performed after writing this report.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
