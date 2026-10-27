## Worker report

The item is stated in `lean/Sheaf/Paper/SmoothPurityCompositionFactors.lean`.
The module contains the finite and tower constructions named by the source and the
item theorem `AlgebraicGeometry.ProEtale.SpCompositionFactors.finite`, with every
proof postponed as `by sorry`.  The theorem statement is unchanged from the DAG
statement; no `statement_change` was made.

The finite declarations render the source clauses as follows.

* `finiteCompositor A f g` is the unique right-adjoint comparison obtained from the
  actual proper/open lower-shriek compositor and the composite adjunction.
* `finiteTensor`, `finiteRho`, and `finiteMu` are respectively the published smooth
  tensor duality map, its value on the dualizing complex of `g`, and the specified
  unit compositor followed by the inverse of `rho`.
* `finiteLineSplit` recursively gives the ordered shifted Tate-line splitting.  The
  zero case is the unit/trace comparison; the successor case tensors the previous
  split with the even shift and reassociates.  Thus the `d=0`, `e=0`, and both-zero
  cases are represented explicitly.
* `finiteReassociate` is the actual pullback compositor followed by inverse tensor
  associator and inverse pullback tensorator.
* `FiniteEquations` is the conjunction of the orientation equation, tensor-mate
  equation for every intrinsic finite-Tor constructible input, and the gamma
  consequence, all transported through the published comparison functor.
* `finite` binds the finite-field datum, prime `ell` with `ell ≠ D.p`, positive level
  `r`, separated finite-type `X,Y,Z` over `D.k`, the `IsOver`, Noetherian,
  separatedness and quasi-compactness hypotheses on `f,g`, smooth relative
  dimensions `d,e`, the annihilating ring equation `hA`, the three deformation
  geometries `df,dg,dh`, the three dualizing identifications `af,ag,ah`, and the
  three `OrientationNormalized` hypotheses `_hf,_hg,_hh`.  Its conclusion is exactly
  `FiniteEquations A f g (ell ^ r) ... d e af ag ah`.

The tower declarations render the tower part of the source statement.
`towerTensorF/G/H` are the three actual gamma tensor mates; `towerOmegaG` is the
coefficient object obtained from `Pg.right` applied to the original unit;
`towerRho` evaluates `towerTensorF` at that object; and `towerMu` is the `c` map at
the unit followed by the inverse of this specified `rho`.  `towerReassociate` is the
canonical pullback/tensor reassociation.  `TowerSplitNormalized` states the
canonical finite-level word comparison for every positive level, including the
rank-zero line.  `TowerEquations` states the normalized splitting, invertibility of
`rho`, the orientation equation, the tensor-mate equation for every full uniform
constructible finite-Tor input, and the gamma consequence.  The theorem `towers`
quantifies the finite-field datum, `ell ≠ char(D.k)`, the three base schemes and all
separated/finite-type/quasi-compact/over hypotheses, the smooth dimensions,
compactification equation, calculus/preservation data, compositor `alpha`, and its
left and counit equations, then concludes `TowerEquations`.

The recorded dependency declarations used by the module are:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`;
* Mathlib smooth, finite-type and proper morphism classes;
* `Sheaf.Paper.SmoothPurityCoefficientTowers`,
  `SmoothPurityCoefficientTowersAbelian`, and `SmoothPurityNormalizedTowers` for
  the ordinary tower categories and `spConstructibleTorTowers`;
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor` for the
  ordinary derived tensor and pullback maps;
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `SmoothPurityMap`, and
  `FiniteSmoothPurityMaps` for coefficient lines, `IsCtf`, gamma and normalized
  orientations;
* `Sheaf.Paper.SmoothPurityTowerGluing` and `SmoothPurityTowerGamma` for support
  adjunctions, tensor mates, finite evaluations and tower gamma;
* the canonical finite prime setting construction copied verbatim from
  `Sheaf.SecSmoothPurity.FiniteGeneralRingData` as
  `AlgebraicGeometry.ProEtale.finiteGeneralRingPrimeSetting`;
* the statement-level `TowerAdjointCompositor.Pair` and `left` interface copied from
  `Sheaf.Paper.TowerAdjointCompositorRealization`.

The published aggregate imports `FiniteGeneralRing` and
`TowerAdjointCompositorRealization` currently fail independently in the server
overlay (`NormalizedCompletionRealization` refers to the missing
`SemilinearSections.moduleAbelian` and has a malformed `generalize`).  The module
therefore imports the smaller healthy sources and contains only the two exact
statement interfaces above; their data and types are unchanged.  The recorded
`det-sp-composition-comparisons` dependency is proof-only for this item statement,
so its broken aggregate module is not imported.

Edge cases checked while writing the signatures were `d=0`, `e=0`, both dimensions
zero, empty schemes, the zero coefficient ring, non-flat finite scalar extensions,
all positive quotient exponents, and an unnormalized tower input.  The recursive
splitting has an explicit zero branch, and no flatness or normalization predicate
is added to the tower input.

Searches were run before writing the module: LeanFinder for composition of smooth
purity orientations and exceptional tensor maps, finite rings and ordinary towers;
Loogle for `CategoryTheory.Adjunction.comp`, `rightAdjointUniq`, and monoidal
associators; `msearch.py grep` for orientation/composition and tensor-duality names;
project `rg` searches for composition-factors, finite general-ring, tower gamma and
existing composition declarations; and `tools/blueprint_refs.py search` for the
blueprint node and its dependencies.  Results were generic category/scheme/tensor
lemmas or no exact match; no existing declaration states this item.

The full module was compiled with the prescribed `scompile.py` against the live
published build after each repair.  The final compile completed with exit code 0,
with no warnings.  The required `deliver2.py --no-push` was then rerun after
removing the trailing `:=` from the recorded `lean.statement` (the preflight parser
records the signature before `:=`); the packet is ready for the final delivery run.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
