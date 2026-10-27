## Worker report

The delivery states `WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates`
and the cofinal-system clause `ramifiedRecovery` in
`Sheaf.Paper.ExceptionalIntegralScalarMates`. Both proofs are `sorry`. Every other
new declaration constructs a type, predicate, abbreviation, inherited instance, or
projection with real data; there is no postponed data definition.

The helper records are the owning theorem's explicitly typed conclusion and its
stipulated transport input, as allowed by the launcher's helper-declaration rule.
No parent construction theorem is imported. The parent data module is reused only
for its existing `FieldStage`, `RingStage`, `Operation`, `Scalar`, `Allowed`,
`Comparison`, `LeftRealization`, `QNormalized`, `ScalarComposition`, `ScalarIdentity`
and `Cocycle`. In particular this delivery does not assert `RingSystem` or assume
its coefficient comparisons.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Finite-field datum, prime ell distinct from p | `D : FiniteFieldDatum`, `[Fact l.Prime]`, `hl : l ≠ D.p`. |
| Every finite coefficient extension with the recorded integers, uniformizer, positive quotients | `FieldStage l` retains `Field`, `Algebra (Padic l)`, and `FiniteDimensional`; `RingStage` uses the recorded `Padic.coefficientExtensionRing`. Finite exponents are `ℕ+`, and natural n consistently means n+1. |
| Finite-type X,Y over k | `X.Over`, `Y.Over`, `LocallyOfFiniteType` and `QuasiCompact` on their structure arrows. |
| Separated finite-type k-morphism f | `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`. There is no separatedness instance on either structure arrow. |
| Fixed compactification | `c : Compactification f`, with its existing `c.i`, `c.g`, `c.Z`. |
| Full bounded constructible derived-complete category, common cohomology/Tor bounds | Integral `C` reduces to `finiteTorConstructibleIntegralCategory`; its inclusion is `RingStage.inclusion`. `sequenceProperty` explicitly has normalization and common a,b,c,d at every n. `systemProperty` is its selected strict-system presentation and `systemBounds` retains the actual endpoints. |
| Actual reduction and total limit | `Reconstruction.calculus`, its existing `reduction`, `adjunction`, and `coefficientSequenceLimit`; `Reconstruction.reduction`, `limit`, `unit`, and `counit` require precisely these functors and maps under full inclusions. The calculus's unit-model and counit-projection equations are retained, rather than new arbitrary reconstruction arrows. |
| Take the ordinary proper/open system adjunction transported by reduction/limit | `operation`, `left`, `transport : Transported ...` are the stipulated inputs. `Transported.support` fixes the existing whole-system open-then-proper word. `realizeF`, `realizeG`, `adjunction_eq`, `reductionF_eq`, and `reductionG_eq` fix the actual conjugated adjunction, units and counits. Finite adjunctions are its evaluated adjunctions via `evaluation_unit` and `evaluation_counit`, and `evaluation_support` fixes their proper/open realization. |
| Identified with the prescribed integral compact support and specified realization | `Transported.integralLeft` and `integralLeft_normalized` use `sfCompactSupportFiniteIntegralFunctor` and `sfQcqsCompactSupportRealization` with `coefficientPrimeUnit l D hl`. |
| Cofinal restriction to en is an equivalence | `ramifiedRecovery` returns `Recovery` for the existing `Etale.SystemProjection.cofinalRamification e ...`, whose zero-based formula is e(n+1)-1. `Recovery.restricts`, `recovers`, `unit`, and `counit` state preservation and invertibility of the actual subsequence adjunction maps. These are the unit/counit criterion for the restricted adjoint equivalence. |
| Inverse at m is derived tensor from the least selected level, with normalization transitions | Recovery is the specified `(S.selected B r).derived`, not an arbitrary inverse. Its `selectedDerivedBelow` is exactly evaluation at `systemNextSelected r m` followed by `systemDerivedTensor S.scalar B (systemNextSelected_spec r m).1`; `systemNextSelected_spec` includes minimality. `selectedTransition` and `selectedDerivedTranspose` fix all transition and counit maps, including repeated least indices. |
| Common intervals retained by restriction and recovery | `Recovery.restriction_bounds`, `recovery_bounds` retain the same four endpoints. Finite constructibility is part of `systemBounds`, with no new levelwise bound choices. |
| Literal ordinary extension for reduction and finite targets, with equality realization | `Mates.finiteScalar_eq` and `finiteScalar_normalized`, for every allowed map with finite target. This includes integral reduction and finite quotient/ramified maps. |
| Published strict-tower completed scalar, theta = chi inverse | `Mates.integralScalar_eq` uses `integralScalarExtensionOfUniverses`. `integralScalar_normalized` equates the inverse realization component to `completedScalarComparison`. |
| Same Tor interval under completed extension | `Mates.tor_interval` quantifies the original a,b and every target reduction n, on the very scalar functor in `Mates.scalar`. |
| All generators, identities and actual-map composites | `Allowed` has quotient, ramified, reduction, integral, identity and composition constructors. `Mates.scalar` and `comparison` quantify every map and every allowed witness, not one preselected factorization. |
| Invertible q,b and displayed counit equation | `Mates.comparison` is the existing `Comparison`: q and b are natural isomorphisms and its `counit` is `q ≫ F_t(b) ≫ epsilon_t = T_Y(epsilon_s)`. Its `unit` is the equivalent unit normalization. |
| Canonical ambient proper scalar mate followed by open tensor | `Mates.comparison_normalized : QNormalized` uses the literal `PurCompactSupport.comparison a c`, defined as the mate of the normalized proper/open restriction square. |
| Actual reduction-system evaluation, units and counits | `ReductionMates.evaluation_normalized` is the calculus's actual reductionEvaluation; `q_evaluation` and `b_evaluation` identify the integral comparisons with `Transported.evaluationF/G`. The latter carry both displayed unit and counit equations. |
| Completed extension agrees with whole finite-free coefficient systems through chi | `SystemMates.coefficient` uses `CoefficientExtensionSystems` for the actual quotient maps. `coefficient_model` retains its ordinary balanced tensor, strict representative, transition, Roos-projection, and coherent counit normalizations. `reduction_normalized` identifies the scalar reduction isomorphism with exactly `coefficientExtensionReductionIso`. |
| Equations before total limit | `SystemMates.q`, `b`, and `counit` live in the derived category of whole normalized strict systems. `q_reduction` and `b_reduction` conjugate these actual system maps to the chosen integral comparisons. This is an equation of system maps, not a family of cohomology isomorphisms. |
| Selected finite-free maps and full L tower, never en=n | `RamifiedMap.exponent` states m+1=e(n+1), and `actual` requires the exact published ramified sheaf map. The main theorem supplies such a record at every n. `SystemMates.selected`, `selected_square`, `selected_balanced`, `q_selected`, `b_selected` relate the full system's selected evaluations to these finite maps with the actual balanced tensor square. Together with `Recovery` these retain full-tower recovery. |
| Canonical shifts | `Operation` fixes coherent integer shifts and shift-compatible adjunction maps. `Transported.leftShift`, `Mates.scalarShift`, `Comparison.qShift/bShift` make all realization and mate maps compatible with the inherited full-inclusion shifts. `Mates.completed_shift` records exactly `completedScalarShiftConeFormula` and the cochain comparison equation, so the second cone coordinate has the canonical sign. |
| Actual-map scalar identity/composition isomorphisms and balanced formulas | `ScalarIdentity.normalized` uses the actual multiplication unitor; `ScalarComposition.normalized` uses `PurCompactSupport.tensorComposition`, the balanced formula on flat models. `Mates.scalarIdentity`, `scalarComposition` retain those structures. |
| Pasted q is canonical composite and pasted b has the same counit equation | `Mates.cocycle : Cocycle` gives both component equations under those scalar associators; `identityLeft/Right` give the identity cases. Every comparison, including the composite map, has the same defining counit equation. |

The auxiliary parameter Ω in the reused coefficient-stage API is an algebraic
closure of Q_l in the coefficient universe. Only finite and integral stages are
used here, and both of their categories, inclusions and scalars reduce
independently of Ω. It introduces no hypothesis on E, L, X, Y or f and no closed
coefficient stage in the assertion.

### Dependency declarations used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the recorded coefficient
  rings, uniformizers and finite-quotient instances.
- Mathlib scheme property typeclasses and
  `WeilConjectures.Compactification.RefinementCategory`: `Compactification` and its
  recorded open/proper factors.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites` (retaining `FiniteTorAmplitude`):
  `finiteTorConstructible`, `finiteTorConstructibleIntegral`, and their full categories.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, its actual reduction, evaluation and
  adjunction, with their retained projection and representative formulas.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`; the retained compact-support module supplies
  `sfCompactSupportFiniteIntegralFunctor`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses`.
- `Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic`:
  `SystemLevelLeftExtensionTheory`, `selectedSystemRings`,
  `derivedSystemEvaluation`, `derivedSystemSubsequence`, `systemDerivedTensorAdj`,
  `systemNextSelected`, and `systemNextSelected_spec`.
- `Sheaf.Paper.EtaleSystemCofinalMate`:
  `AlgebraicGeometry.Etale.SystemProjection.cofinalRamification`.
- `Sheaf.Paper.CoefficientExtensionReductionData`:
  `CoefficientExtensionSystems`, `CoefficientExtensionReductionData`, and
  `coefficientExtensionReductionIso` with all its actual model normalizations.
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`:
  `PurReconstruction.realized` and `realizedAdjunction`.
- `Sheaf.SixFunctors.IntegralSystemOperations`:
  `IntegralSystemRealization.Operations`, its open/proper functors and
  `supportEvaluation`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedScalarComparison`.
- `Sheaf.Paper.CompletedScalarChainShift`: the exact cone formula and comparison
  types used in its `completedScalarChainShift` theorem.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`: the existing
  ring-stage data listed above, using no existence theorem from the parent node.

Every already-stated proof dependency is imported (plain imports when only needed
for the proof plan); the two Mathlib shift dependencies import
`Mathlib.CategoryTheory.Shift.Adjunction` and `Shift.CommShift`.
The reconstruction proof node currently has no Lean declaration; this lemma takes
its specified transport as its node expressly says to do, exposing its functors
and equations in `Reconstruction` and `Transported`. Its existence is not silently
assumed as a new scalar hypothesis, nor is any postponed reconstruction theorem
used to define data by a choice.

### Edge cases checked

Identity extensions and maps use `Allowed.identity` with actual sheaf-map equality;
e=1 and arbitrary e>1 retain the formula e(n+1)-1, not n. Level one and quotients
at equal indices are retained. `systemNextSelected` treats adjacent full levels
with the same selected index using the existing transition formula. Zero complexes
and empty schemes are not excluded. Common intervals are independently chosen and
ordered; no extra equality of cohomological and Tor endpoints is imposed. Neither
scheme is assumed absolutely separated. Scalar composition quantifies any actual
composite map and every allowed witness; no extra flatness of finite quotient
maps is a premise. Site objects have universe u+1, morphisms u, and sheaf modules
u+1 throughout; they have not been forced into one universe.

### Searches

- `msearch.py leanfinder`, query “Integral coefficient extension scalar mates for
  compact support and exceptional inverse image with ramified normalized towers”:
  eight irrelevant norm/trace/Galois restriction results, no matching statement.
- `msearch.py loogle`, queries `Adjunction, NatIso, CommShift` and
  `CategoryTheory.Adjunction, CategoryTheory.NatIso`: service replied unknown
  identifier (Adjunction / CategoryTheory.NatIso), no matches. These are recorded
  as failed name searches, not evidence that the categorical notions are absent.
- `msearch.py grep`, `scalar.*[Mm]ate|[Mm]ate.*scalar` in Mathlib CategoryTheory:
  zero results; `normalized.*system|system.*normalized` there: zero results.
- `rg` in the prescribed `lean/WeilConjectures`, `lean/Sheaf`, and DAG nodes for
  the item id, integral scalar mates, reconstruction and ramified system APIs:
  no exact existing item theorem. Found and reused the finite scalar theorem,
  parent data definitions, selected left-extension API, completed comparison,
  coherent quotient model, system transport, and proper/open realization.
- Read the recorded signatures and docstrings for every statement dependency;
  fetched the parent data source with `scompile.py --source` to check the live
  interface. The absent reconstruction module was checked with `--source` too.
- Read Zheng's local PDF (printed pp. 36–37, Lemma 5.22, Proposition 5.24,
  Construction 5.25, Proposition 5.26) and the current `blueprint/latest`
  exceptional paragraph and tensor/Hom unit; the auxiliary tower construction
  concerns the same ordinary-etale finite/integral operations.

No statement correction and no STATEMENT-DISPUTED finding.

## Second reading by Q22

A second pass by the same dispatched worker, with both the node and final module
open; no independent worker was started, as the launcher's brief forbids agents.
The maintainer's independent delivery review remains the independent reading.

The first draft omitted system equations and unchanged interval endpoints. It was
expanded to include `Recovery.restriction_bounds/recovery_bounds`,
`Mates.tor_interval`, `ReductionMates`, and `SystemMates`. The integral comparison
is now tied to the actual coherent counit and its Roos-projection-normalized model,
and its selected finite-level comparison has an explicit balanced-square equation.
The nonempty selected-map family at every source level is also stated, so these
normalizations cannot hold merely because there are no ramified witnesses.

Checked all rows of the table against the actual field signatures. In particular,
the displayed counit equation has q at G_s(N) first, then F_t(b), then epsilon_t;
no inverse q was substituted. Completed normalization uses realization.inv=chi,
which is exactly theta=chi inverse. The full and selected categories remain
different types. The original positive m,n are represented by zero-based indices
plus one, and the least-selected formula is the existing `systemNextSelected`.
The given transport does not contain the scalar mates which the theorem asserts.
The only additional output beyond q,b is their unit equation, which is equivalent
to the counit normalization by the triangle identities, as already recorded in
`Comparison`. The final statement keeps the actual composite maps, both endpoint
associators and identity equations. No mismatches remain from this reading.

The ten original proof steps are preserved, verbatim, in the main theorem's
source/proof docstring; the separate ramified theorem has its complete unit,
counit, normalization and bounds proof description. The source's “returned steps
13–16” are the scalar-mate obligations covered by these ten node steps.


## Repair of returned immutable head 078042861d9f

The live local item differs from the retained delivery only in `lean` and
`stmt_deps`; all mathematical statement/proof fields are preserved. The delivery
wrapper rebuilds this changed sandbox on the current server main branch.

1. H2, left-extension ownership: replaced `lem-pur-system-level-left-extension`
   in `stmt_deps` with `def-pur-system-level-left-extension-basic`. The former
   stays in `proof_deps` and its import is plain; Basic is publicly imported.
   The theorem's `Nonempty` conclusion is not a statement input.
2. H3, sign freedom: `Transported.realizations` retains the published
   `IntegralSystemRealization.Realizations` for its very `operations`.
   `inputGood` and `openGood` record the actual canonical realization domains.
   The new `integral_system_normalized` equation states, on every integral K,
   `I(realizeF.inv) ≫ left.integral.hom = properRealization ≫
   Rp_*(openRealization ≫ j_!(inverse reconstruction unit))`.
   The proper realization is `RealizationModel.push`; the open realization is
   `Realizations.openRealization`, fixed by its reduction-mate normalization.
   The inverse unit is that of the given reconstruction equivalence, with only
   its `limit` equality transported by `eqToIso`. The source and target objects
   are the equal presentations identified by `support` and `limit`; `HEq`
   transports that equality and does not forget the map. Thus changing both
   `realizeF` and `realizeG` by minus signs while holding `left` fixed violates
   this equation whenever the relevant identity is nonzero. Changing `left`
   with them is the consistent transport and changes both prescribed reduction
   comparisons together. `integralLeft_normalized` still identifies the very
   same left realization with the recorded integral compact support.
3. Carried H2: added the landed definition owners
   `def-pur-finite-compact-support-scalar-data` (actual ramified changes,
   balanced tensor squares and proper/open scalar maps),
   `def-weil-compact-support-finite-action` (recorded integral functor),
   `def-sf-integral-system-realization-data`, its canonical-bridge owner and
   expression-domain owner. Replaced the generic theorem-owned ConeFormula
   specialization and product comparison by the existing definition-owned
   `completedScalarShiftConeFormula` of
   `def-pur-completed-scalar-shift-coordinates`, for every P,m. Its explicit
   two-coordinate equations have the identical product reindexing and (-1)^m
   sign; the chain comparison equation is retained unchanged.
   The three remaining published definition families have new `existing:true`
   owners below, with no copied declarations. The existing proof-dependency list
   is unchanged, and the source theorem nodes are untouched. No reviewed Mates/SystemMates/Recovery equation,
   counit order, ramified exponent formula or geometric hypothesis was altered.

Additional edge check: the sign twist raised by the return is ruled out by the
new square before any reduction q is constructed. It also works for the identity
compactification, zero objects, empty schemes and every positive ramification.
The input/open Good fields retain compatible etale origins and the same common
finite bounds on the very systems used by the canonical open comparison; they
are part of the specified ordinary-etale system transport, not scalar hypotheses.

The repair searches ran through msearch LeanSearch, LeanFinder, Loogle and
Mathlib grep. Their exact queries/results are in each new node. LeanSearch gave
eight generic equivalence/adjunction declarations, Loogle six generic adjunction
ones, LeanFinder eight arithmetic/ramification results, and Mathlib grep no hits.
`rg` found the exact existing definitions only in the three published modules;
DAG declaration scans found only their theorem-node owners. Blueprint searches
for reconstruction transport, cofinal ramification, and finite Tor integral
inclusion all returned zero matches. Generic Mathlib equivalence adjunctions
are reused by the published realization definitions themselves.

## New nodes

`def-sf-positive-ramification-subsequence` registers the existing
`AlgebraicGeometry.Etale.SystemProjection.cofinalRamification` from
`Sheaf.Paper.EtaleSystemCofinalMate`. It is exactly n ↦ e(n+1)-1 with its
strict-monotonicity proof. Zheng Construction 4.1/Proposition 5.24 provide the
positive cofinal indexing convention. Searches found no definition owner;
no new embedding or recovery theorem is defined.

`def-sf-equivalence-adjunction-realization` registers the existing
`PurReconstruction.realized` and `realizedAdjunction` from
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`. Their definitions
are R_X ⋙ F ⋙ L_Y and the actual triple composite adjunction, as used in Zheng
Construction 5.25/Proposition 5.26. Searches found generic Mathlib adjunction
composition and the exact project definitions, but no definition-node owner.

`def-sf-finite-tor-integral-inclusion` registers the existing
`PurCompactSupport.finiteTorIntegralInclusion` and the unchanged proved
`coefficientPrimeUnit` from
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`. The former forgets
only the Tor condition, preserving the complex and map; the latter supplies
the source-implied prime-unit proof for the recorded compact-support functor.
The node cites the existing finite-field, coefficient, integral constructible
and finite-Tor owners. Searches found these exact declarations only under the
compact-support comparison theorem, with no definition owner. No data is
selected from an undetermined existence assertion.

### Repair second reading by Q22

Read the changed Transported fields against the node's phrase “reduction/limit
transport ... and its specified ambient realization”. The new equation fixes
that previously missing relation, using the published proper conjugate and
unit-normalized open mate, without assuming any q or b. Rechecked the retained
clause table, counit order, actual-map scalar witnesses and en≠n transports.
New nodes only give ownership of already published definitions; their statements
and recorded signatures were checked against the source bodies and docstrings.
The signed cone specialization is mathematically the same clause. No node
statement correction or STATEMENT-DISPUTED finding is required.
