## Worker report

The module states `AlgebraicGeometry.ProEtale.SpCoordinateAdjunction.tower_coordinate_adjunction`.
Its sole postponed proof is `by sorry`; all helper definitions have actual data.
`Construction` is an existential proposition packaging the simultaneous chart adjunctions and the equations fixing
their construction. It does not assume these adjunctions as hypotheses.

The node's statement is unchanged. The only additional statement dependencies are
already-landed `def-amb-affine-trace-tower`, `def-sp-tower-class-pullback`, and
`def-sp-tower-class-diagonal`, for the concrete ordered coordinate scheme and the
normalized root-section interfaces. Three new definition nodes own the comparison interfaces split into separately compiled modules; no dependency repairs.

Hypotheses and clauses, in the order of the node:

- The prime characteristic is `(pchar : ℕ) [Fact pchar.Prime]`, the field is
  `(k : Type u) [Field k] [CharP k pchar]`. The prime ell is `(l : ℕ) [Fact l.Prime]`
  and `_hl : l ≠ pchar`. The finite extension is `E : Type u`, `Field E`,
  `Algebra (Padic l) E`, `FiniteDimensional (Padic l) E`.
- `Bases k` bundles exactly separated finite-type schemes over k; its structure
  maps supply `Over`. A chart has the explicit equality `e ≫ proj ≫ Y.hom = U.hom`.
  Etaleness, separatedness, local finite type and quasi-compactness are explicit.
  Local finite type plus quasi-compactness means finite type.
- `SpTowerShriek.R l E n` is O_E/(ell^(n+1)); thus `n : ℕ` covers precisely the
  node's positive levels. The coefficient extension's ramification and ideal
  equalities are retained in `Base.ramification_eq` and `Base.ideals`.
- `spDerivedCoefficientTowers` and its section-preserving realization are the
  ordinary derived category of the recorded strict varying-ring systems.
  `P`, used for every `RestrictedPair`, is literally `spConstructibleTorTowers`.
  This predicate includes intrinsic constructibility, bounded cohomology and Tor
  amplitude in common intervals. It has no normalization conjunct. It is not the
  similarly named normalized subcategory.
- The finite categories are literally `spFiniteConstructibleTorCategory` over the
  actual constant quotient ring. `LevelCompatibility.finite` is an adjunction on
  the entire finite full categories, not only objects in an evaluation image.
- `SpTowerCalculus.F ... c` is the fixed compactification open/proper composite.
  The compactification `c` has no level parameter. Arbitrary choices are included.
- `space` and `proj` reuse `affineTraceTower` and `affineTraceProjection`, the
  existing ordered coordinate model, canonically identified with ordinary affine
  space by `affineTraceAffineSpaceIso`. Its zero stage is literally the base.
- `Construction.domains`, `affine_source`, and `affine_target` retain the
  bounded-below and separate finite etale-origin witnesses of chart admissibility.
  No compatible choice of witnesses and no normalized tower is requested.
- `chartRight` is the stated two pullbacks followed by tensor with the degree-zero
  d-th Tate tower and shift 2d. `ChartPair` is the adjunction with this actual right
  functor, transported through the fixed realization. `RestrictedPair.homEquiv`
  is its natural ambient Hom bijection; its inverse has exactly the direction
  displayed in the node. Mathlib's `Adjunction` supplies naturality and triangles.
  `RestrictedPair.unit` and `.counit` are actual ambient tower arrows.
- `ProjectivePresentation` retains the recorded P1 presentation, normalized unit
  and trace counit. The equality transports `projectivePush` and `projectiveTensor`
  put it in the common geometry without choosing unrelated maps. `affine_hom`
  is explicitly `projectiveHom` followed by `openHom`, followed by the normalized
  affine-chart right comparison. The former uses the recorded P1 adjunction;
  the latter uses the actual `Open.derivedAdjunction`.
- `projection_successor` is `CompositeEquation` with the canonical calculus
  composition isomorphism. Its counit is the line counit followed by the preceding
  integration. `orderedRight`, `iteration_successor`, and `step_normalized` fix the
  order of the coordinates and the successive pull/tensor/shift identification.
- `RootLines.normalized` specifies the finite Kummer identification by the actual
  root-limit projection and multiplication of the coefficient scalars.
  `pulled_one` specifies root restriction on every finite pure root tensor;
  `pulled_zero` fixes scalar pullback, and `pulled_product` fixes higher powers.
  `Products` fixes ordinary multiplication on all finite pure tensors and its
  derived map on K-flat single-complex representatives. `PullTwist.normalization`
  uses the already normalized geometric tensor-pullback comparison.
  `TensorShifts` uses the actual signed total-complex shift maps on all K-flat
  representatives. The tower morphisms include strict transition compatibility;
  the given `Twists.transition` is the quotient/root power transition. The finite
  root projection formula therefore retains z -> z^ell, including ramification.
- `chart_counit` displays exactly compact-support transport, the actual etale
  sum-extension counit, then the ordered projection counit. `etalePair` is the
  canonical restricted etale adjunction of the recorded calculus.
- `projection_levels`, `chart_levels` assert the finite adjunctions.
  `LevelCompatibility` states unit, counit, transpose and inverse-transpose
  evaluation equations. Left normalization is `supportEvaluation`; right
  normalization is the explicit realization/pullback/tensor/shift evaluation
  word `projectionEvaluation` or `rightEvaluation`.
- `ZeroComparison`, `iteration_zero`, and `zero` fix d=0 by ordinary identity
  pullback, the coefficient unit, zero shift, and calculus identity compact
  support. Only the etale adjunction remains in a zero-dimensional chart.
- No joint faithfulness or detection of equality by derived evaluations occurs
  anywhere in the statement. Ordinary-section equations only normalize the
  ordinary line and identity maps before deriving them.

Recorded dependency declarations used:

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `sk-def-sp-coefficient-towers`: `Sheaf.Paper.SmoothPurityCoefficientTowers`, `AlgebraicGeometry.ProEtale.spCoefficientTowers`.
- `det-sp-coefficient-towers-abelian`: `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`, `AlgebraicGeometry.ProEtale.sp_coefficient_towers_abelian`.
- `sk-def-sp-normalized-towers`: `Sheaf.Paper.SmoothPurityNormalizedTowers`, `AlgebraicGeometry.ProEtale.spNormalizedConstructibleTorTowerCategory`.
- `def-weil-proetale-constructible-sheaf`: `Sheaf.Paper.ProEtaleFixedModuleConstructible`, `AlgebraicGeometry.Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `def-weil-proetale-tor-amplitude`: `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`, `AlgebraicGeometry.Scheme.HasFixedCoefficientProEtaleTorAmplitude`.
- `det-sp-tower-shriek-levels`: `Sheaf.Paper.SmoothPurityTowerShriekLevels`, `AlgebraicGeometry.ProEtale.SpTowerShriek.tower_shriek_levels`.
- `lem-sp-tower-chart-admissibility`: `Sheaf.Paper.SmoothPurityTowerChartAdmissibility`, `AlgebraicGeometry.ProEtale.SpChartAdmissibility.tower_chart_admissibility`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `WeilConjectures.sfQbarTwistingFunctor`.
- `det-sp-tower-p1-adjunction`: `Sheaf.Paper.SmoothPurityTowerP1Adjunction`, `AlgebraicGeometry.ProEtale.SpTowerP1.exists_towerP1Adjunction`.
- `lem-sp-coefficient-tower-shriek-calculus`: `Sheaf.Paper.CoefficientTowerShriekCalculus`, `AlgebraicGeometry.ProEtale.SpTowerCalculus.coefficient_tower_shriek_calculus`.
- `lem-pur-finite-kummer-level`: `Sheaf.Paper.PurityFiniteKummerLevel`, `WeilConjectures.PurityFiniteSetting.finiteKummerLevel`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `def-amb-affine-trace-tower`: `Sheaf.AlgebraicGeometry.AffineTraceTower`, `AlgebraicGeometry.affineTraceTower`.
- `def-sp-tower-class-pullback`: `Sheaf.Paper.TowerClassPullback`, `AlgebraicGeometry.ProEtale.SpTowerClasses.LinePullback`.
- `def-sp-tower-class-diagonal`: `Sheaf.Paper.TowerClassDiagonal`, `AlgebraicGeometry.ProEtale.SpTowerClasses.Diagonal`.

The coefficient tower calculus reexports its `CoefficientTowerShriekInterfaces`;
the statement uses its normalized realization, compact support, composition,
etale extension and etale adjunction rather than redefining any operation.
The P1 module supplies its `Presentation`, `Maps`, `AdjunctionData`, and domains.
The root pullback module supplies `chart`, `restrictRoot`, and `adjointSection`.
The additional modules imported only for the postponed proof are the recorded
finite Kummer, canonical tensor-pullback, root-projection-reduction, root-site,
finite-etale-line, and finite-root-tensor dependencies.

Edge cases read against the formulas: d=0; d=1; d=2, with the first coordinate
integrated after the last coordinate; identity etale chart; empty source and
empty base (all section formulas are still meaningful); zero objects; first
positive coefficient level; ramification index greater than one. No nonempty,
normalization, algebraic closure, compatible origin, or unramified-extension
hypothesis was added. The coefficient-size universes remain u+1 on the pro-etale
site of object size u+1 and morphism size u.

Searches: msearch LeanFinder for the natural tower-chart Hom bijection returned
only standard-etale and affine-space algebra hom equivalences. Loogle for
`CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.homEquiv` found the
generic composite Hom formula. msearch grep for
`coordinate.*adjunction|tower.*adjunction|Adjunction.comp` in CategoryTheory found
generic categorical composition. LeanSearch for ordinary derived strict towers
with ordered integration returned generic derived-adjunction declarations.
The actual search digests are in `searches.jsonl`. Local rg of both project source
roots for coordinate/chart/affine adjunctions and grep for the exact node id found
finite-ring affine-chart adjunctions and the recorded P1/tower calculus, but no
statement for this ordinary strict-tower chart assertion. Those finite-ring
statements do not provide the entire tower adjunction with actual tower arrows.

No `STATEMENT-DISPUTED` finding and no statement correction.

## Second reading by Q31

Independent second reading (maintainer reviewer NT-cc-Q31-7ab12251e). I read the node, the
source place (gluing.proof.md, Local pairs and Levels) and the four delivered modules
against the recorded dependency declarations. The earlier self-audit paragraph in this
section is replaced by this reading.

Node clauses and their Lean:

- k a field of characteristic p > 0, a prime ell ≠ p, and E/Q_ell finite: `pchar`,
  `Fact pchar.Prime`, `CharP k pchar`, `_hl : l ≠ pchar`, `Fact l.Prime`, `Algebra (Padic l) E`,
  `FiniteDimensional`. OK.
- Separated finite-type k-schemes: `Bases k`, the Over objects with separated, locally
  finite type and quasi-compact structure maps. The ordered coordinate spaces get these
  instances through `coordinateBase`. OK.
- A_n = O_E/ell^n for n ≥ 1: `SpTowerShriek.R l E n` = O_E/ell^(n+1), with n : ℕ. This is
  the recorded convention of the dependency. OK.
- D(Tow(T,O_E)) and C_T (uniform, unnormalized): `spDerivedCoefficientTowers` with
  `P` = `spConstructibleTorTowers` (sk-def-sp-normalized-towers). No normalization conjunct. OK.
- C_{T,n}: `spFiniteConstructibleTor` over the constant quotient ring. OK.
- F_h for a coefficient-independent compactification: `SpTowerCalculus.F … c` with
  `c : Compactification (e ≫ proj …)`, for every c. OK.
- p_d : A^d_Y → Y: `affineTraceProjection` (def-amb-affine-trace-tower). The last coordinate
  is the newest one, so `orderedRight` matches r_i and p_i = p_{i-1} r_i. At d = 0 it is
  literally the identity. OK.
- e : U → A^d_Y separated étale of finite type over k: `[Etale e] [IsSeparated e]
  [LocallyOfFiniteType e] [QuasiCompact e]` with `hOver`. OK.
- Chart-admissibility domains: `affine_source`, `affine_target` and `_domains` are the
  dependency's `SpTowerP1.domain` and `SpChartAdmissibility.domain`. Each is asserted only
  for objects of P, which is what `tower_chart_admissibility` gives. OK.
- Tate twists: `w : TwistFamily` = `SpChartAdmissibility.Twists`. The level isomorphisms to
  `spEllTwistLine` and the transition equation pin it up to unique isomorphism, as in the
  landed chart-admissibility statement. OK.
- The natural bijection with actual unit and counit: `ChartPair` = `RestrictedPair` with
  Mathlib `Adjunction`. `homEquiv` is (F_h M ⟶ K) ≃ (M ⟶ e^*p^*K(d)[2d]), whose inverse
  has the displayed direction. `unit` and `counit` are ambient tower arrows. OK.
- Affine-line factor: `_affine_hom` gives the projection Hom map for d = 1 at the trace
  compactification. It is the P1 Hom bijection `projectiveHom` (AdjunctionData of
  det-sp-tower-p1-adjunction), then `openHom` (j_! ⊣ j^*), then the normalized restriction
  `affine.comparison`. Other compactifications are pinned by `_projection_successor` at
  d = 0. OK.
- Composition with the compact-support composition maps: `_projection_successor` is
  `CompositeEquation` with `cal.composition.composition` and the pinned `step`. In the final
  clause the chart counit is α^{-1}, then F_cp(e_! counit), then ε_{p_d}, after the
  `pulled … d` right comparison. So fibre summation precedes ordered integration. OK.
- Twist identification at level n: `RootLines.normalized` (root-limit projection, scalar
  multiplication); `_pulled_zero/_one/_product`; `Products` (pure tensors, the degree-0
  chain map, K-flat derived map); `TensorShifts` (total-complex shifts on K-flat
  representatives); `step`/`_step_normalized`/`_iteration_successor`. The tower morphisms
  are strict, so the transitions z ↦ z^ell are respected. Every existential comparison is
  fixed by an equation; I found no free iso. OK.
- Evaluation at each n: `projection_levels`/`chart_levels` (`LevelCompatibility`: unit,
  counit, transpose and inverse transpose). Left normalization is `supportEvaluation`;
  right normalization is `projectionEvaluation`/`rightEvaluation`. The finite pair is on
  the whole finite ctf categories. No faithfulness of evaluation is asserted. OK.
- d = 0: `zeroComparison`, `_iteration_zero` and `_zero` give the identity adjunction
  transported by `cal.composition.identity`. OK.

Edge cases checked: d = 0; d = 1 (the affine Hom clause and the successor at d = 0 must
agree); e = id; U or Y empty (statements over empty schemes remain meaningful); n = 0
(level 1); ramified E (Base.ideals); zero objects. No universe restriction beyond the
dependencies' Scheme.{u} with Type u fields.

Advisories (not faults of this delivery):

- `h : Preservation` and an arbitrary `cal`, `b`, `o` are inherited from the recorded
  calculus interface (lem-sp-coefficient-tower-shriek-calculus), as in the landed
  chart-admissibility and P1 statements.
- The new definition nodes use declarations whose owners are not in their stmt_deps:
  `spEllTwist*` (def-sp-ell-twist-quotient-data), `SpEllTwistProducts` (owned only by the
  theorem lem-pur-tower-operations-ground-field-retagging), `tateFiniteTensor`,
  `proEtaleRootsOfUnity*`, `purTwist*`, `SignedLineProductNormalized` and semilinear models.
- The three definition modules privately import proof-only theorem modules (Kummer level,
  root projection reduction, etc.) that their declarations do not use.

## New nodes

`def-sp-coordinate-adjunction-categories` (`Sheaf.Paper.SmoothPurityCoordinateCategories`) defines the coordinate interfaces described by its self-contained statement. Its source is the Local pairs and Levels paragraphs. LeanSearch returned unrelated manifold coordinates, Loogle returned the generic Mathlib adjunction API, and Mathlib grep returned no exact tower comparison. Project/DAG grep and blueprint search found the dependent theorem and general notions, but no existing owner for these normalized coordinate interfaces. The generic Mathlib adjunction and existing tower operations are reused. All definitions have actual data; these nodes assert no existence theorem.

`def-sp-coordinate-tate-tensor-comparisons` (`Sheaf.Paper.SmoothPurityCoordinateTensorComparisons`) defines the coordinate interfaces described by its self-contained statement. Its source is the Local pairs and Levels paragraphs. LeanSearch returned unrelated manifold coordinates, Loogle returned the generic Mathlib adjunction API, and Mathlib grep returned no exact tower comparison. Project/DAG grep and blueprint search found the dependent theorem and general notions, but no existing owner for these normalized coordinate interfaces. The generic Mathlib adjunction and existing tower operations are reused. All definitions have actual data; these nodes assert no existence theorem.

`def-sp-coordinate-right-comparisons` (`Sheaf.Paper.SmoothPurityCoordinateRightComparisons`) defines the coordinate interfaces described by its self-contained statement. Its source is the Local pairs and Levels paragraphs. LeanSearch returned unrelated manifold coordinates, Loogle returned the generic Mathlib adjunction API, and Mathlib grep returned no exact tower comparison. Project/DAG grep and blueprint search found the dependent theorem and general notions, but no existing owner for these normalized coordinate interfaces. The generic Mathlib adjunction and existing tower operations are reused. All definitions have actual data; these nodes assert no existence theorem.


Further clause audit: every finite object can be viewed as a strict tower supported
at its single chosen level, with zero transitions and zero objects elsewhere. The
embedding is exact, so its derived image has the same bounded cohomology and Tor
intervals at that level and vanishes elsewhere. Thus this unnormalized uniform
domain includes a lift of every finite constructible finite-Tor object. The four
evaluation equations determine the finite adjunction maps on the entire finite
category; they do not merely compare maps on a smaller normalized-image domain.
This argument does not infer equality of tower morphisms from evaluations.
The successor equation at d=0, with arbitrary line compactification and arbitrary
output compactification, also transports the normalized affine pair to every
chosen compactification, starting with the specified identity pair.

Compilation layout: the category, normalized tensor, and right-comparison interfaces
are separate modules owned by the three new definition nodes. The final theorem
uses an existential proposition instead of a large data structure; the binders
and all equations are unchanged mathematically. This avoids expensive generated
recursors and keeps the same chart adjunction existence statement.

All four files compile within 60 seconds after the existential reformulation.
Unused names of existential proof binders were prefixed with `_`; their exact
propositions are retained. No linter is disabled to hide these warnings.
