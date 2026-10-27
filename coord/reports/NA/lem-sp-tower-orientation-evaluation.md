## Worker report

The delivery states `AlgebraicGeometry.ProEtale.SpCompositionFactors.tower_orientation_evaluation`
in `lean/Sheaf/Paper/TowerOrientationEvaluation.lean`. Its only postponed proof is that
named theorem; every helper has actual data or is an explicitly defined predicate.
The natural index `n : ℕ` always means the positive exponent `n+1`, so the theorem
includes the first quotient. The item's natural-language statement is unchanged.

The current blueprint source read was
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/`
`sk-prop-sp-composition-factors.proof.md`, (1), especially its parenthesis on tower
sheaves and removal of the common twist and shift; the unit `_section.md` was also read.
The accepted DAG proof expands that paragraph without claiming derived-Hom faithfulness.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field, characteristic p | `D : FiniteFieldDatum.{u}`; its recorded field and algebraic-closure structures are used unchanged. |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime]`, `_hl : l ≠ D.p`. |
| Arbitrary finite extension E of Q_ell | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; no unramified restriction. |
| Separated finite-type k-schemes X,Y,Z | For each scheme, `Over (Spec (.of D.k))`, `IsSeparated` on its structure map, `LocallyOfFiniteType`, and `QuasiCompact`. |
| Smooth separated k-morphisms f,g, pure dimensions d,e >= 0 | f=`jf ≫ pf`, g=`jg ≫ pg`, `(d e : ℕ)`, their `IsOver`, `IsSeparated`, and `SmoothOfRelativeDimension` instances. The open/proper factors are presentations of arbitrary compactifiable maps, not a restriction to open or proper f,g. |
| h=gf, dimension d+e | h=`jh ≫ ph`; `hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph`. The composite's smoothness and relative dimension follow from the recorded Mathlib permanence result. |
| Strict varying-coefficient tower, ordinary derived category, unnormalized uniform Dctf | Published `SpTowerShriek.D`, `SpTowerCalculus.C`, `b`, `o`, `q`; the full category is based on `spConstructibleTorTowers`, with no `IsSpNormalizedTower` condition on inputs. |
| Rings O_E/ell^n and quotient transitions | The existing `SpTowerShriek.R l E n` is O_E/ell^(n+1), not O_E/uniformizer^(n+1). `b.ideals` retains the ramification factor. `SpTowerCalculus.quotient` is the actual quotient map. |
| Exact evaluations and levelwise ordinary derived tensor/pullback | Published `SpTowerShriek.ev`, `Ev`, `tensor`, `pull (o.geometry ...)`; the finite words retain the site, scalar and K-flat comparisons. No completed tensor is introduced. |
| Given exceptional adjoints G_u and omega_u=G_u A | `Pf,Pg,Ph : TowerAdjointCompositor.Pair ...`; `right`, `adj`, `levels`; `towerOmegaG` and the published `exceptional`/`originalUnit`. `Pair.levels` includes the actual finite units, counits and canonical coefficient mates. |
| L_u=A(d_u)[2d_u] and prescribed diagonal orientation a_u | `SpTowerGamma.orderedLine` with `d,e,d+e`, and `af,ag,ah : SpTowerGamma.Purity ...`; their `orientation` and `finite_levels` are reused. The recursively ordered line includes the zeroth coefficient unit and the even shifts. |
| Specified counit tensor maps t_u | Existing `towerTensorF/G/H` use the published `SpTowerGamma.tensorMate`, its actual adjunction, the projection inverse and the actual counit. |
| Counit-normalized c, not a free automorphism | `c : Ph.right ≅ Pg.right ⋙ Pf.right`; `alpha`, `_ha` pin the proper/open left compositor to `cal.composition.composition`; `_hc` is exactly its right-compositor counit normalization. These are supplied coordinates of det-sp-composition-comparisons, not an extra geometric assertion. |
| W=f*omega_g tensor omega_f and rho=t_f(omega_g) | `towerOrientationTarget` is the actual `tensorSource` at `towerOmegaG`; existing `towerRho` is that particular tensor mate. |
| rho invertible, mu=rho inverse after c_1 | The conclusion supplies `hR : IsIso (towerRho ...)`; existing `towerMu ... c hR` is c at the coefficient unit followed by the inverse of that rho. |
| Actual Phi=mu a_h | `towerOrientationPhi` has body `ah.orientation.hom ≫ (towerMu ...).hom`. Its type is a morphism in the ambient ordinary tower derived category. |
| Actual Psi=f*a_g tensor a_f, using shifted-Tate splitting | The conclusion supplies a derived isomorphism `s` with `TowerSplitNormalized ... s`; `towerOrientationPsi` is `s.hom` followed by the published tensor functor on the pullback of `ag.orientation.hom` and `af.orientation.hom`. |
| Evaluations use precisely the finite diagonal arrows | For every `n`, the conclusion supplies `F,G,H : TowerOrientationLevel ... n`. These contain the diagonal geometry, `OrientationNormalized`, the normalized finite unit, and the actual orientation evaluation square. The data are conclusions, not added assumptions. |
| ev_n(Phi)=mu_n a_h,A_n | The first `SpTowerP1.WordComparison` uses `H.orientation.inv`, the canonical `rightDerivedUpperShriekCongr` for `hcomp.symm`, and `(finiteMu ... hr).hom`. `hr` proves invertibility of the actual finite `finiteRho`, whose inverse defines finiteMu. |
| ev_n(Psi)=f*a_g,A_n tensor a_f,A_n | The second `WordComparison` uses the existing `finiteLineSplit`, followed by actual finite pullback of `G.orientation.inv` and finite tensor with `F.orientation.inv`. |
| Exact identified endpoints of the evaluation formulas | The source is the prescribed `coefficientWord` of ah. `towerOrientationTargetWord` is the tensor of pulled-back `dualizingWord` for g and `dualizingWord` for f, retaining the counit-normalized finite right-adjoint comparisons. `WordComparison` asserts both endpoint comparisons invertible and the equality of arrows, not just isomorphic endpoints. |
| Both L_h and W concentrated only in degree -2(d+e) | `TowerOrientationConcentrated` is asserted separately for the ordered L_h and `towerOrientationTarget`; it requires `IsZero (homologyFunctor ... i).obj M` for every `i ≠ -2*((d+e : ℕ) : ℤ)` in the ambient tower derived category. |
| Surviving cohomology sheaves have locally free rank-one finite evaluations | The other clause of `TowerOrientationConcentrated` is `∀ n, ((SpTowerShriek.ev ... n).obj ((homologyFunctor ... (-2*(d+e))).obj M)).IsFiniteLocallyFreeOfRank 1`. It evaluates the actual tower cohomology sheaf. |
| Quotient transitions, including identity reductions | `TowerOrientationReduction` is concluded for each constructed arrow, using the inverse section-preserving realization and the published reduction with `q.scalar`. It quantifies over every m<=n, including m=n. |
| Actual units and counits | Retained by Pair.levels, the normalized units in `TowerOrientationLevel`, the definition of `tensorMate`, and `_hc`. The canonical equality comparison for a different presentation of h is also retained in Phi's finite formula. |
| No faithfulness or normalization assertion | There is no evaluation-faithfulness hypothesis or conclusion, no equality Phi=Psi, and no normalized-input hypothesis. All equality assertions are forward evaluations of constructed arrows. |

The `IsNoetherian` instances and quasi-compact/compactification instances in the section
are the standard consequences/presentations of separated finite-type maps over a field,
as in the dependency APIs. They exclude no maps covered by the node. The coordinate
arguments `z,pres,cal` are those of the existing tower calculus; their preservation and
coherence are supplied by its recorded interfaces. The theorem works for all such supplied
presentations and all prescribed Purity structures, without choosing arbitrary maps.

Dependency declarations reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.Proper`, `.Separated`,
  `.Smooth`, `.Etale`: `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`,
  `SmoothOfRelativeDimension`, `smoothOfRelativeDimension_comp`, and separated composition.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its `.CoefficientExtension`
  import: `Padic.finite_coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`; the tower uses the existing ell-power quotient.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spEllIdeal`, `spCoefficientTowers`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`: `SpCoefficientTowersAbelian`,
  `spCoefficientEvaluation`; `SmoothPurityNormalizedTowers`: `spDerivedCoefficientTowers`,
  `spDerivedCoefficientEvaluation`, `spConstructibleTorTowers`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: finite intrinsic pullback/tensor;
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`: `derivedTensor`;
  `IntrinsicCoefficientTwistsUnrestricted`: the existing signed coefficient twists.
  Ordinary tower realizations are the published `SpTowerShriek` operations built on them.
- `SmoothPurityTowerGamma`/`SmoothPurityTowerGammaData`: `tower_gamma`, `Purity`,
  `orderedLine`, `tensorMate`, `coefficientWord`, `inputWord`, `exceptional`, `originalUnit`.
- `SmoothPurityTowerGluing`/its public data module: `tower_gluing`, `Levels`, `support`.
- `CompositionComparisons` and its public `TowerAdjointCompositorRealization`:
  `compositionComparisons_towers`, `Pair`, `left`, and the counit-normalization interface.
- `Sheaf.SecSmoothPurity.FiniteGeneralRing`: `finiteGeneralRingSmoothPurity`.
- `TowerTensorTransposeWords`: `SpTensorTranspose.dualizingWord`;
  `TowerP1LevelWords`: `LevelWord`, `WordComparison`, `pullWord`, `tensorWord`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality`:
  `Etale.rightDerivedUpperShriekCongr`, the canonical comparison for hcomp.
- The existing composition-factor arrows listed under New nodes below.

The proof-only imports include every already-stated non-Mathlib proof dependency:
`TwistedPullbackTowerDomain`, `TowerTensorTransposeEvaluation`, `SemilinearDerivedSections`,
`DiagramPullbackMonoidalShiftModels`, `EtaleFiniteTwistPullback`, `PurTwistSheafLocallyFree`,
and `FiniteGeneralRing`; shared gamma/gluing/compositor modules are publicly available.
Mathlib permanence comes from the imported morphism modules.

Edge cases checked before and after drafting:

- d=e=0 and either one zero: the ordered lines and finite splitting use their coefficient
  unit/zero recursion branches, so concentration is degree zero and no positive-dimension
  assumption appears.
- Empty X (or empty Y,Z where a map permits it): concentration permits all cohomology zero;
  local rank-one assertions are vacuous on the empty site. No nonzero conclusion is added.
- n=0 means exponent one, and all finite levels occur. m=n occurs in both reduction squares.
- Ramified E is retained: ell-power and uniformizer-power levels differ by b.ramification;
  nothing equates these exponents. Finite levelRing uses only the existing universe lift.
- Unnormalized tower inputs remain in the full uniform category; no derived reduction
  isomorphisms are required of them.
- A separate chosen factorization jh,ph of h is retained. The finite formula explicitly
  uses the canonical exceptional comparison for hcomp, rather than silently assuming
  definitional equality of the two maps.

Searches made on 2026-10-26:

- `msearch.py ... leanfinder` with "Composite smooth purity tower orientation maps exact
  finite evaluation and concentration in a shifted rank one Tate line": 8 unrelated
  linear-algebra/number-field hits; no statement match.
- `msearch.py ... loogle` with `CategoryTheory.Functor.mapIso, DerivedCategory.homologyFunctor`:
  0 hits.
- `msearch.py ... grep` with `tower.*orientation|orientation.*evaluation` in CategoryTheory:
  0 hits.
- `msearch.py ... leansearch` with "Canonical shifted Tate tensor splitting and counit
  normalized composite exceptional orientation arrows": 8 hits on shift adjunctions,
  algebra tensor equalizers and short-complex splittings; no statement match.
- `rg` on tower orientation/evaluation in `lean/WeilConjectures` and `lean/Sheaf`, and
  literal node-id grep in `lean/WeilConjectures`: no exact existing statement. The existing
  `SmoothPurityCompositionFactors` theorem asserts the later composition equality, whereas
  this item proves the endpoints, concentration and forward evaluations without that equality.
- `rg` on `towerRho|TowerSplitNormalized|towerMu` in dag/nodes found only the composition
  theorem node. `blueprint_refs.py search 'composition orientation arrows'` found 0 blueprint
  nodes. Definitions in `SmoothPurityCompositionFactors` provide the exact helper notions,
  so they are reused via an existing-definition node, never copied.

There is no mathematical statement correction or disputed statement.

Validation: the required scompile.py server compile passed without errors or warnings.
Its final run reported sandbox 14.5 s and library module 15.7 s, both below 60 s.
The initial compile exposed two interface errors (raw reductions versus their canonical
scalar transport, and a missing hcomp comparison); both were corrected with the published
comparison maps. No definitions, hypotheses or limits were weakened.

## New nodes

`def-sp-composition-orientation-arrow-data` binds the existing data-only declarations
`finiteCompositor`, `finiteTensor`, `finiteRho`, `finiteMu`, `finiteLineSplit`,
`towerTensorF/G/H`, `towerOmegaG`, `towerRho`, `towerMu`, and `TowerSplitNormalized` in
`Sheaf.Paper.SmoothPurityCompositionFactors`. Its source is the composition-factors
statement's definitions and shifted-Tate splitting. It is `existing: true` and adds no
Lean file or copied definition. The searches above found these definitions already in
Sheaf but no independent definition node; it reuses them through their own definition
record. The item cites this new node directly. The data node depends on the published
gamma-data, adjoint-compositor-data, finite canonical maps and finite comparison words,
and never on the downstream composition-equality theorem.

Module-cycle note for the maintainer: the existing data definitions live in the same
module as the downstream `SpCompositionFactors.towers` theorem. This delivery imports
that module for definitions only and never invokes `towers` or `finite`. The automatic
reverse proof-dependency import of TowerOrientationEvaluation into
SmoothPurityCompositionFactors must be omitted, since it would close a module cycle
(stages/2-statements.md section 3 rule 7). Extracting those existing data to a lower module
is a possible later library refactor; no DAG dependency on the downstream theorem is added.

## Review handoff

The dispatcher instructed this worker to deliver directly and prohibited starting other
agents. No independent second-worker reading is claimed. The maintainer's independent
review should check the clause correspondence above and the existing-helper import-cycle
note, in addition to the Lean statement. The worker's own semantic reread checked the
actual node, helper definitions, and module, including the finite orientation direction
(alpha.inv), coefficient-unit normalization, surviving degree sign and ramification index.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
