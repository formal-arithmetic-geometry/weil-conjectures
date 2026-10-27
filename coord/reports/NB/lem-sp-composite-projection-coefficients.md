## Worker report

`Sheaf.Paper.CompositeProjectionCoefficients` states the finite-ring and ordinary
varying-coefficient-system clauses of `lem-sp-composite-projection-coefficients`.
The source is the current blueprint `literature/blueprint/latest/`,
`sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md`,
proof (2). The node's mathematical statement is unchanged. The module's named
statements jointly render it; `finite_composition` is the primary record entry.
All theorems have `sorry` proofs with source and complete proof plans. Definitions
have real data: canonical functor/comparison words, explicit predicates, or records
specifying normalized ordinary and representative comparisons. There is no bare
choice of an object, tensorator, compositor or comparison from existence.

Hypotheses and clauses correspond as follows.

- The finite-field datum is `D : FiniteFieldDatum`; the characteristic and
  algebraic closure are its recorded data. `ell`, `Fact ell.Prime`, and
  `ell ≠ D.p` give the prime distinct from the characteristic.
- Schemes are `Scheme.{u}` with their `Over (Spec (.of D.k))` structures.
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on the structure maps
  express separated finite type. Morphisms retain `IsOver`, `IsSeparated`, and
  `SmoothOfRelativeDimension d f` / `SmoothOfRelativeDimension e g`, with natural
  `d,e`. Composition is literally `f ≫ g`. Explicit quasi-compactness and local
  finite-type instances used to type canonical formulas follow from this setting;
  `geometry` states Noetherianity, all three compactifications, and dimension d+e.
- Finite coefficients are arbitrary `A : Type (u+1)` with `CommRing` and `Finite`;
  `∃ n, 0 < n ∧ ((ell^n : ℕ) : A) = 0` is the positive annihilating ell-power.
  There is no DVR, field, nonzero-ring, or coefficient-normalization hypothesis.
  `Etale.FiniteSmoothPurity.proCategory` and `IsCtf` are the recorded ordinary
  constant-coefficient category and intrinsic bounded constructible finite-Tor
  predicate. No copy of that predicate is introduced.
- Tower coefficients retain `E : Type u`, its field and `Algebra (Padic ell) E`
  structures, and finite dimensionality. `SpTowerShriek.D` is the actual ordinary
  derived category of sheaves on the ringed sequence site. `towerCtf` transports
  the existing `spConstructibleTorTowers` through the fixed exact realization.
  That predicate has separate common cohomological and Tor intervals and does not
  contain `IsSpNormalizedTower`. `towerTorIn` and `towerCohIn` spell out a specified
  interval at every actual quotient level n+1.
- `finiteProjection` is the published `projectionMapOfCompactification`, with
  finite-ring Noetherianity supplied internally. `SpTowerShriek.projection` is
  the simultaneous system map: the proper counit projection followed by the open
  tensor comparison and pullback compositor. All tensor functors, shifts and
  Tate lines come from the dependency modules. `finitePullTensor` and
  `finitePullUnit` only supply the required finite Noetherian-ring instance.
- `finite_domains` states membership of omega_g, G_g K and
  f^* omega_g tensor omega_f using the published exceptional functor and
  the exceptional functor applied to `finiteGeneralRingUnit` directly.
  `tower_domains` states precisely these three memberships in section coordinates,
  using `SpTowerGamma.exceptional` directly at the original coefficient unit. The pairs are the counit-normalized adjunction
  data of the recorded composition interface, not arbitrary extra functors.
- `finite_orientation_and_tor` identifies omega_f with the published ordered
  A(d)[2d] line. Its negative even shift gives the unshifted degree-zero Tate
  line. Tensor with that line keeps [a,b]; tensor with the shifted line has
  [a-2d,b-2d]. This quantified one-map statement applies separately to f,g,h.
  `tower_orientation_and_intervals` uses the actual strict degree-d Tate tower
  and states both uniform Tor and cohomological interval effects. The twist
  data retain their quotient transitions and finite-level normalization.
- `ProjectionLaws` explicitly spells out invertibility on the displayed ctf
  inputs, joint naturality, the right-unit equation, and tensor associativity.
  Its associator and inverse pullback tensorator are explicit morphisms.
  `finite_projection_laws` and `tower_projection_laws` apply it to the actual
  projections and canonical pullbacks. In the tower clause a coherent monoidal
  pullback structure is part of the conclusion, with its tensor comparison fixed
  to `o.geometry.tensorPullback`; its unit cannot be independently chosen.
- `finite_composition` states the first displayed equation with the published
  `SpTowerCalculus.finiteCanonicalComposition` and the actual derived pullback
  compositor. Its etale-origin witnesses are propositions only, needed to type
  the already recorded restricted compositor; they choose no maps or objects.
  `towerCompositor` transports the recorded proper/open compositor through the
  fixed realization counits. `towerCompositionLaw` and `tower_composition` state
  the same equation with this very arrow, for arbitrary retained cf,cg,ch.
  The tensor-source ctf witness is a conclusion. Neither equality is tested only
  after finite evaluation; all arrows belong to the coefficient derived category.
- `finite_site_projection` gives the actual etale/pro-etale projection square,
  with `compactSupportSiteComparison` at retained bounded-below witnesses and
  the canonical tensor/pullback comparisons. That support comparison is assembled
  from the fixed proper counit mate and exact open comparison. The compositor in
  `finite_composition` is exactly its recorded proper/open transported compositor.
  The exceptional counit is the published `FiniteSmoothPurity.proCounit` word;
  the recorded composition data retain its counit normalization. There is no
  replacement of these maps by unspecified isomorphisms.
- `ArithmeticRestriction` records the order embedding n ↦ e(n+1)-1, so that the
  selected positive uniformizer exponent is e(n+1). Its section, restriction,
  and morphism normalizations retain every product-site arrow and actual quotient
  transition. `derived` is exact termwise localization. `ArithmeticComparisons`
  fixes ordinary direct image on sections, pullback by its adjunction mate,
  proper direct image by its derived counit mate, open extension by its unit mate,
  and tensor by pure sections and the actual signed K-flat representative model.
  `uniformizerTensorModel` only repackages that published record at the equivalent
  coefficient-universe parameter; it changes no representative comparison.
- `uniformizerCtf` spells out the same two uniform intervals on all original
  uniformizer levels, without normalization or completion. This differs from
  `sfIntegralConstructible`, which concerns derived-complete integral objects,
  and is not used as a substitute for ordinary strict systems.
  `arithmetic_restriction_ctf` states preservation under actual selected evaluation.
  `ArithmeticComparisons.support` is the specified proper/open comparison word.
  `arithmetic_projection` asserts existence of the normalized restriction and
  comparisons and their explicit projection square. `arithmetic_composition`
  identifies the actual uniformizer proper/open triangle compositor with the
  ell-power compositor. The equality is in the system derived category before
  evaluation. The ordinary normalizations and counit mates also preserve the
  common-refinement factors used for arbitrary retained compactifications.

Dependency declarations used (module and principal names):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- Mathlib finite-type, proper, and smooth morphism modules: `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, `IsProper`, `SmoothOfRelativeDimension`.
- `Sheaf.SecSmoothPurity.FiniteGeneralRing`: `finiteGeneralRingSmoothPurity`;
  its canonical data module supplies `Etale.FiniteSmoothPurity.proCategory`,
  `comparison`, `exceptional`, `IsCtf`, `line`, `proCounit`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`, `SmoothPurityCoefficientTowersAbelian`,
  and `SmoothPurityNormalizedTowers`: `spCoefficientTowers`,
  `SpCoefficientTowersAbelian`, `spDerivedCoefficientTowers`,
  `spConstructibleTorTowers`, `spFiniteConstructibleTor`.
- `Sheaf.Paper.DerivedPullbackTensorHom` and the upstream
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`: the
  ordinary derived pullback and tensor constructions used by the recorded maps.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and tower Gamma imports:
  `SpChartAdmissibility.Twists`, `SpCoordinateAdjunction.line`.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`, `SmoothPurityTowerGluing`,
  `SmoothPurityTowerGamma`: the fixed smooth exceptional adjunction/orientation
  and `SpTowerGamma.exceptional`.
- `Sheaf.Paper.CompositionComparisons`: `SpCompositionFinite`,
  `SpTowerCalculus.finiteCanonicalComposition`, and the normalized tower calculus.
- The exceptional-unit expressions are inlined from their identical definitions:
  finite omega is `exceptional.obj (finiteGeneralRingUnit A target)`; tower omega
  is `SpTowerGamma.exceptional.obj` at `SpTowerGamma.originalUnit`. The membership
  proof is `SpFiniteOrientation.unit_tower_mem` from
  `Sheaf.Paper.FiniteOrientationReduction` (`lem-sp-finite-orientation-reduction`);
  its conclusion is genuinely used to type the coefficient object in the full
  subcategory. The domain theorem module is only a proof import.
- `Sheaf.Paper.CoefficientTowerShriekInterfaces`: `SpTowerCalculus.Coordinates`,
  `FiniteCoordinates`, `Preservation`, `Calculus`, `realization`, and
  `SpCoordinateAdjunction.supportRealization`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`; `FiniteRingSiteTensorTransposeData`:
  `finiteRingSiteTensor`, `finiteRingSitePullback`, `finiteRingTensorPullbackComparison`,
  `finiteRingEtalePF`, and `finiteRingProPF`.
- `Sheaf.Paper.SemilinearSystemModels` and `CoefficientRingedTensorHomModel`:
  `SemilinearSections.TensorComparisonModel`, `Models`, `tensorSection`,
  `ordinaryTensor`, and `CoefficientTensorModels`.
- `Sheaf.SixFunctors.IntegralSystemOperations` and
  `Sheaf.SixFunctors.IntegralCompactificationRealizationData`:
  `IntegralSystemRealization.Operations`, `Realizations`, `Compositors`,
  `OpenComparisons`, `compactificationProjection`, `pull`, and `calculus`.
- `Sheaf.Paper.TowerAdjointCompositorRealization`: `TowerAdjointCompositor.Pair`,
  cited through `def-sp-adjoint-compositor-data`.
- The compact-support functor and proper/open compositor used by
  `ArithmeticComparisons.CompositionLaw` are now inlined from the operation and
  realization data: exact open extension followed by proper image, and the
  specified Gamma followed by open and proper composition. Equality transport
  of the open arrow is expressed by `eqToHom` on the subtype of open immersions;
  by equality elimination this is the identity-isomorphism transport in the old
  helper. Its construction uses no theorem conclusion or extra comparison map.
  Open quasi-compactness is supplied by `c.quasiCompact_openImmersion`, exactly
  the word of the old helper instance. The completed-composition theorem module
  is no longer imported.
- Arithmetic proof interfaces are imported from `SystemDerivedSubsequence`,
  `SystemRingedSequenceSite`, and `ArithmeticSystemRightAdjoint`, including
  `SheafOfModules.arithmeticSystemRightAdjoint`. All original proof-dependency
  modules are imported for the proof plans. Existing newly used definition
  owners are added to stmt_deps; a transitive dependency audit found no cycle.

Edge cases checked: zero coefficient ring; empty source or target schemes; d=0,
including both identity maps; zero derived objects; distinct cohomological and Tor
intervals; positive coefficient exponents represented by n+1; arbitrary unnormalized
strict towers and their actual skipped uniformizer levels; ramification index one;
nontrivial ramification; shift convention H^i(K[s])=H^(i+s)(K). No nonvanishing,
normalization, DVR presentation of A, equality of site universes, or compatibility
of chosen finite-level etale origins is assumed. No STATEMENT-DISPUTED issue found.

Searches performed before drafting:

- `msearch.py NB ... leanfinder`, query “compact support projection formula
  coherent under composition and tensor product for finite coefficients and
  varying coefficient towers”: eight unrelated tensor/coalgebra results.
- `msearch.py NB ... loogle`, query
  `AlgebraicGeometry.Etale.projectionMapOfCompactification,
  AlgebraicGeometry.ProEtale.derivedTensor`: zero results; first identifier not
  known to that service.
- `msearch.py NB ... grep`, query
  `projectionMapOfCompactification|ProjectionFormula`, directory `CategoryTheory`:
  zero results.
- `rg` in the upstream `lean/WeilConjectures` and project `lean/Sheaf` found the
  individual canonical projection, tensor, proper/open and system interfaces,
  but no statement combining this node's clauses. Node-id search upstream found
  no existing declaration for this item. Searches for system/constructible
  predicates distinguished ordinary uniform systems from derived completion.

## Repair of returned head 58b658965b49

H2, ownership of definitions: the names `CtfPullbackDomains.finiteOmega` and
`towerOmega` are removed from statements; their identical exceptional-unit words
are inline. The actual coefficient-unit membership proof is taken from its
recorded owner, as detailed above. `completedShriekF` and `completedShriekA` are
also removed; the functor word and the entire Gamma/open-compositor/proper-compositor
word are inline in `ArithmeticComparisons.CompositionLaw`. No new definition
node or duplicate alias is introduced. The corresponding two theorem citations
are removed from stmt_deps. The imported domain theorem remains available only
for the proof plan, as does the other proof machinery required by the original
node's proof_deps.

H2, definition citations: replace `lem-pur-finite-ring-site-tensor-transpose` by
`def-pur-finite-ring-site-tensor-transport-data`; replace
`lem-sf-composition-projection-mate` by `def-sf-integral-system-operations` and
`def-sf-integral-system-realization-data`; add `def-sp-adjoint-compositor-data`
for `TowerAdjointCompositor.Pair`. The first two unused theorem modules are plain
proof imports, while their actual definition-owner modules are public imports.
The original mathematical statement, proof, and proof_deps are unchanged.

Stale dependency packet: removed both sandbox files for
`SfP1ChartMapComposition` / `lem-sf-p1-chart-map-composition`. Current main already
contains the stage-2 sorry and the local irreducibility attributes, so this
packet makes no change to that module or node. The current main item has no Lean
record yet; this repair retains its statement and original fields and supplies
the repaired Lean record. The prescribed delivery wrapper builds one fresh
commit over current main. It does not replay an unchanged delivery.

H11: the following second-reading section replaces the previous general account
with explicit verdicts for every hypothesis and clause. The maintainer's return
also records an independent clause-by-clause mathematical check with no mismatch.
No mathematical statement correction is required.

## Second reading by NB

I reopened the node and the repaired module and checked the following clauses.
These are explicit additional worker-reading verdicts; the independent reading
is the maintainer's immutable-head review quoted in the return, not a fabricated
second agent. The dispatcher forbids starting another agent.

| Node hypothesis or clause | Lean checked and verdict | Change on this repair |
| --- | --- | --- |
| Algebraic closure of a finite field, characteristic p, prime ell distinct from p | `FiniteFieldDatum`, `[Fact ell.Prime]`, `_hne : ell ≠ D.p`: MATCH. | None. |
| Separated finite-type k-schemes; smooth separated maps of pure dimensions d,e; h=gf | The three `Over` structures, separated/locally-finite-type/quasi-compact structure maps, `IsOver`, separated morphisms, and `SmoothOfRelativeDimension` with natural d,e match each hypothesis. Every composite is `f ≫ g`: MATCH. | None. |
| Arbitrary finite ell-primary commutative coefficients, ordinary pro-etale Dctf | `A`, `[CommRing A]`, `[Finite A]`, positive annihilating exponent, `proCategory`, intrinsic `IsCtf`: MATCH. No nonzero, DVR, or field restriction is added. | Inline finite omega as the same exceptional-unit expression. |
| Ordinary varying-coefficient towers; separate uniform cohomology and Tor intervals; normalization not required | Actual `SpTowerShriek.D`, fixed realization in `towerCtf`, and existing `spConstructibleTorTowers` have two independent uniform intervals, with no normalized-tower predicate: MATCH. | Inline tower omega; use the existing unit membership theorem solely for the subtype proof. |
| Noetherianity, compactifications for f,g,h, dimension d+e | `geometry` has all seven conclusions, including dimension `(d + e)` at `f ≫ g`: MATCH. | None. |
| F_u adjoint to G_u, omega_u=G_u(unit), prescribed counits and compositor | Published finite exceptional/compact-support data, actual tower pairs, finite canonical compositor, and `towerCompositor` through the fixed realization counits use exactly these maps: MATCH. | Cite the definition owner of `Pair`; inline the identical exceptional-unit words. |
| omega_g, G_g K and f^*omega_g tensor omega_f in the ctf domains | The three conjuncts of `finite_domains` and `tower_domains` have precisely these objects, at Y,Y,X respectively, for K in C_Z: MATCH. | Object expressions expanded, not mathematically changed. |
| omega_u is B(d_u)[2d_u]; unshifted Tate line keeps [a,b], shift gives [a-2d_u,b-2d_u] uniformly | `finite_orientation_and_tor` uses the published ordered shifted line and its negative shift; `tower_orientation_and_intervals` uses the degree-d strict line and even shift. Endpoint signs and universal interval quantifiers agree: MATCH. | None. |
| Actual proper-counit/open projection is invertible, natural, unital and tensor associative | `finiteProjection`, `SpTowerShriek.projection`, `ProjectionLaws`, and the two law theorems use the proper/open word with explicit unit and associators. The last conjunct has the correct tensor-variable order: MATCH. | Cite the finite transport data rather than its unused theorem. |
| Composition equation with alpha, P_g then F_g(P_f), and alpha at the tensor source | `finite_composition` and `towerCompositionLaw` compose in this order and retain the pullback compositor. cf,cg,ch are arbitrary, not restricted to a composite compactification: MATCH. | None. |
| Equations before evaluation; finite site comparison preserves the same alpha and counits; tower transitions are actual quotient maps | Equalities lie in the actual derived categories; `finite_site_projection` uses the fixed support comparison and actual tensor/pullback comparisons. The tower compositor is not chosen from its evaluations, and the sequence-site operations retain transitions: MATCH. | Point public imports and stmt_deps to definition data; remove unused theorem citations. |
| Arithmetic restriction at positive exponents e(n+1), preserving projection and composition | `ArithmeticRestriction.index_eq` is `e*(n+1)-1`, so its level exponent is exactly e(n+1). Sections, restrictions and maps retain actual quotient transitions. `ArithmeticComparisons` fixes mate and K-flat normalizations; its projection and composition laws are equalities in the system category: MATCH. | Inline the exact open/proper functor and Gamma/open/proper compositor words; equality transport retains the same map. |
| Edge cases: empty schemes, zero ring/object, d=0, unnormalized towers, ramification e=1 | No nonemptiness, nonzero, positive-dimension, normalization or ramification-greater-than-one condition appears. Both uniform intervals apply to all original uniformizer levels, including skipped levels: MATCH. | None. |

All clause verdicts are MATCH. The changes address ownership/citation and report
specificity; the maintainer found no mathematical mismatch, and this reading
found none introduced by expansion. All explicit maps have the same endpoints
and order as on the returned head. There are no new nodes or dependency modules.

## Validation

The repaired module passed the prescribed scompile.py server compile with no
errors or warnings beyond expected sorry declarations: sandbox 34.2 s, library
32.9 s, below the 60-second limit. Its primary signature is verbatim in the node
record, line width is at most 98, and the additional definition-owner citations
have no transitive path back to this item. Only lean and stmt_deps differ from
current main's item node; its mathematical statement and proof are unchanged.
The obsolete dependency module and node are absent. The prescribed deliver2.py
--no-push dry run passed server preflight and compilation at 6377575f6f0, staging
exactly the item module, item node, and this report.
