## Worker report

This repairs the H2 return on immutable delivery head 440b00881860.
The main declaration is
AlgebraicGeometry.ProEtale.SpTowerGamma.tower_gamma in
Sheaf.Paper.SmoothPurityTowerGamma. Its proof is sorry, as required in stage 2.
The real definitions construct the projection/counit composite, its adjunction
transpose, and their tensor-orientation composite in the ordinary derived category
of strict towers. The Purity structure states the three requested conclusions.

Hypotheses: FiniteFieldDatum supplies the finite base and algebraic closure;
CharP D.k D.p states its characteristic and hne states ell differs from it.
Fact ell.Prime, Field E, Algebra (Padic ell) E and FiniteDimensional give exactly
an arbitrary finite coefficient extension. Base, Operations and Coordinates are
the section-normalized presentations of the recorded coefficient-tower calculus.
X and Y are separated finite-type schemes over D.k. The noetherian witnesses
are the consequences of these conditions used by the finite diagonal interface.
The factorization j followed by p is a compactification of the smooth morphism,
with relative dimension d a natural number. The given hF, G, adj, lv are the
compact-support functor, its right adjoint and all finite adjunction comparisons
of det-sp-tower-gluing. Twists uses the recorded strict coefficient Tate towers.

Clause (1): Purity.orientation is an isomorphism from the ordered tensor of d
shifted degree-one Tate lines to G of the coefficient unit. Its finite_levels
field uses OrientationNormalized, which retains the diagonal mate, Rees
specialization at t=1, and Kummer-normalized bundle integration. The unit
comparison ui is fixed by the actual evaluation of the coefficient unit.
WordComparison specifies the inverse finite orientation through these fixed
comparison maps. Ordered tensor convention is the one in finite smooth purity.

Clause (2): projectionCounit is inverse projection after source symmetry,
followed by target symmetry, identity tensor the actual counit, and right unitor.
tensorMate applies the given adjunction Hom equivalence, using full inclusion
and the fixed realization only. gamma tensors the orientation then applies
this transpose. Purity.source_mem and tensor_mem assert uniform ctf membership;
projection_iso asserts invertibility on that domain. purity_iso and naturality
quantify over every object and arrow of C_Y; no normalization hypothesis occurs.
finite_levels fixes its ordinary etale-origin map to FiniteSmoothPurity.gamma,
with canonical right-adjoint uniqueness comparison and actual pull/tensor word
comparisons. The finite map is `FiniteSmoothPurity.gamma` over O_E/ell^(n+1),
using positive exponent n+1. The older `def-pur-smooth-purity-map` interface
uses uniformizer-power quotients O_E/varpi^n; this module uses the general
finite-ring map owned by `def-pur-finite-smooth-canonical-maps` for the
ell-power quotients required by this node.

Clause (3): support_normalized and exceptional_normalized test every actual
quotient reduction, including equal indices, via IsSpNormalizedTower. Membership
in the uniform constructible category is already retained by the functors.

Dependencies used: SmoothPurityTowerGluing supplies C, support, Levels and finite
origins. SmoothPurityCoefficientTowers and SmoothPurityNormalizedTowers supply
the ordinary strict-tower category, uniform ctf domain, and normalization.
SmoothPurityTowerShriekLevels supplies pull, tensor and projection. The coefficient
twist dependency supplies the actual positive line. TowerP1CoefficientCoordinates,
TowerP1TensorCoordinates, TowerP1GeometricCoordinates and TowerP1LevelWords supply
normalized site, scalar, tensor and evaluation coordinates; no arbitrary endpoint
isomorphisms are introduced. SmoothPurityMap and FiniteSmoothPurityMaps supply
the specified finite tensor transpose and diagonal normalization. DerivedCategory
and the published derived-tensor construction are used throughout.

Edge cases inspected: the natural index zero means exponent one, never the zero
coefficient quotient; d=0 uses the coefficient unit with no Tate factors; empty
schemes and zero objects are allowed. Neither connectedness, a common finite
stratification, normalization, nor E embedded into a chosen algebraic closure is
assumed. All quotient reduction indices, including identity reductions, are tested.

Searches: msearch leanfinder queried smooth exceptional pullback purity orientation
on strict towers and returned ordinary ring/scheme smoothness only. The inherited
LeanSearch and Loogle searches in searches.jsonl and the node return no tower purity
match. rg in Mathlib, WeilConjectures and Sheaf for det-sp-tower-gamma and tower
orientation/purity found only downstream references, no declaration of this result.
The existing normalized-adic lift concerns integral reductions, not this assertion
on all unnormalized uniform finite coefficient towers.

## H2 return repaired

Removed exactly these five ids from the item's added `stmt_deps`:

- lem-pur-etale-support-map-compatibility
- det-thm-sfb-proper-base-change-integral
- det-thm-sfb-proper-base-change-finite
- def-sfb-finite-proper-exchange
- def-weil-pbc-finite-index-splitting

They had only carried compile repairs; no declaration in the item uses them
directly. They already belong to the base statement/proof dependency closure,
so carrying them as new statement dependencies was incorrect. The four
`def-sp-p1-*` additions and `def-pur-finite-smooth-canonical-maps` remain.

Tested the item alone, with none of the five old dependency modules supplied:
`scompile.py ND det-sp-tower-gamma lean/Sheaf/Paper/SmoothPurityTowerGamma.lean`
passed without errors or warnings on the current live published library.
The wrapper reported 23.4 seconds for the sandbox check and 18.1 seconds for
the library module check. Consequently all five dependency modules and their
node copies are removed from this delivery. Their retained versions are
archived under the sandbox scratchpad only. In particular no `no_expose`,
`finiteProperExchange_eq` sorry, irreducibility change, splitting import or
FreeSheaf import change is proposed by this repaired delivery. The item Lean
source is unchanged from the independently approved returned head.

The delivery wrapper refreshes the current main branch and reapplies the
item's authorized record fields. Comparing the saved nodes and modules with
the current read clone confirms that the withdrawn dependency changes were
only the previously reported repairs; the remaining item changes concern its
Lean record and the statement dependencies described here. The mathematical
statement and proof plan remain unchanged.

## Definition owners cited

Added the definition owners advised by the independent reviewer. These are
recorded existing interfaces, used through the public dependency imports:

- def-sp-tower-p1-adjunction-data: `Sheaf.Paper.SmoothPurityTowerP1Adjunction`,
  `SpTowerP1.TensorData`, its symmetry and right-unit isomorphisms.
- def-sp-coefficient-tower-shriek-interfaces:
  `Sheaf.Paper.CoefficientTowerShriekInterfaces`, `SpTowerCalculus.Coordinates`,
  realization, C, inclusion and level comparisons.
- def-sp-chart-tate-tower-data: `Sheaf.Paper.SmoothPurityTowerChartAdmissibility`,
  `SpChartAdmissibility.Twists`.
- def-sp-coordinate-adjunction-categories:
  `Sheaf.Paper.SmoothPurityCoordinateCategories`,
  `SpCoordinateAdjunction.supportRealization`.
- def-sp-coordinate-tate-tensor-comparisons:
  `Sheaf.Paper.SmoothPurityCoordinateTensorComparisons`,
  `SpCoordinateAdjunction.line`.
- def-sp-coordinate-right-comparisons:
  `Sheaf.Paper.SmoothPurityCoordinateRightComparisons`,
  `SpCoordinateAdjunction.RootLines`.
- def-sp-tower-class-systems: `Sheaf.Paper.TowerClassSystems`,
  `SpTowerClasses.unit`.
- def-sp-tower-class-coefficients: `Sheaf.Paper.TowerClassCoefficients`,
  `SpTowerClasses.Arings`.

All abbreviated declaration namespaces in this list are under
`AlgebraicGeometry.ProEtale`. The corresponding signatures and docstrings
identify the same strict coefficient tower and canonical comparison data
used by the module; no replacement definitions were added.

## Second reading by ND

No second reading by a worker: the worker delivers directly and the
maintainer's independent review is the review of this delivery. The return
on 440b00881860 checked the mathematical substance and found it sound. This
repair addresses H2 and its advisories without changing that Lean statement.

## Repair validation

The repaired one-module packet passed `deliver2.py ND det-sp-tower-gamma
--no-push`: `OK (dry run): commit 2ad1a731e80 passes the preflight and
compiles; nothing pushed`. The staged paths were exactly this report, the
item node and `lean/Sheaf/Paper/SmoothPurityTowerGamma.lean`. No dependency
module or dependency node is included.
