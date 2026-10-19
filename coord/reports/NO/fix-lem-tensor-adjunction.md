## Worker report

Retained the saved stage-2 packet and its module
`Sheaf.Paper.TensorAdjunctionExchange`. The only postponed theorem is
`WeilConjectures.TensorAdjunctionExchange.tensor_adjunction`; its proof is `sorry`
and its docstring gives the nine DAG proof steps. All helper definitions have
explicit data. No mathematical statement or dependency node was changed.

The source checked is
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.md`.
It has the same displayed exchange, admissibility condition, two naturality
variables, and three compatibility clauses as the DAG statement.

The correspondence with the statement is as follows.

- The global finite-field and coefficient hypotheses are the binders
  `D : FiniteFieldDatum`, `A : D.CoefficientDatum`, the finite extension `E`,
  `[Field E]`, `[Algebra (Padic A.l) E]`,
  `[FiniteDimensional (Padic A.l) E]`, and `n`, `hn : 1 ≤ n`.
  `A` includes the prime and the inequality with the characteristic.
- The supplied six-functor datum is the binder
  `six : SixFunctorOperationDatum D A E n hn`.
- Finite-type schemes over the fixed base are `X Y : SixFunctorSpace D`;
  `f : X ⟶ Y` is over that base. The separated finite-type condition is
  `[IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
  [QuasiCompact f.hom.left]`. No separatedness of X or Y over the field is added.
- `S : System ...` and `c : Compactification f.hom.left` present the already
  recorded coefficient operations and compactification. They do not assume
  the exchange. `Package` witnesses `finiteDatum`, `integralAt`, `rationalAt`, and
  `closedDatum` identify the four operations and both adjunctions with those
  of `six`. `OperationRealization.ordinary` and `.extraordinary` specify the
  transpose equations, rather than identifying only the object actions.
- The condition that f is exceptionally admissible is retained in
  `CorePackage.conclusion (s) (_h : Admissible ... s)`.
  `Admissible` matches the stage with the dependency's finite, integral,
  rational, or algebraically closed admissibility predicate. Thus the theorem
  packages an implication at each stage; it does not assert that admissibility
  always holds. The existential base-unit proof is part of that predicate.
- The inputs M and N range over `C l Ω X s` and `C l Ω Y s`, respectively,
  the published finite-Tor categories. `Stage` covers positive finite quotients,
  integral coefficients, rational coefficients, and the common-stage closure.
- `Model.left` is `Rf_* RHom_X(M,f!N)` and `Model.right` is
  `RHom_Y(Rf_!M,N)`. `Conclusion.exchange` is an isomorphism of curried
  bifunctors, so naturality includes contravariance in M and covariance in N.
- Canonicity is `Conclusion.components`: the inverse component is exactly
  `Model.inverseComponent`, obtained from projection and evaluation by the
  exceptional and ordinary adjunctions. `RingModel` fixes the finite Hom,
  tensor, evaluation, pullback, direct image, and ordinary adjunction on the
  ringed derived categories. `Projection.normalized` fixes the projection
  to the proper-counit/open-projection composite. `PartialRealization` fixes
  higher-stage Hom, tensor and evaluation to their published operations;
  the integral tensor is the completed one.
- Finite reduction and scalar extension are `Change`, `Compatible`, and
  `CorePackage.coefficientNaturality`. The comparison maps `Change.homX`,
  `.homY`, and `.star` are explicitly defined from evaluation and adjunction,
  rather than arbitrary arrows. `ringScalar` supplies comparisons for the
  allowed finite/integral changes of the given System. `rationalization`,
  `rationalScalar`, and `common` give the corresponding localized and
  common-stage changes and identify their exceptional comparison with S.
- Shifts are `Conclusion.first` and `.second`; the opposite-category shift
  in the first variable represents the negative Hom shift. `RingShifts`
  identifies the comparisons with the signed-source and unsigned-target
  ringed Hom shifts. `ChangeShifts` and `coefficientShifts` retain the shift
  equations for the specified coefficient maps.

Dependency declarations used directly are
`WeilConjectures.SixFunctorOperationDatum` from
`Sheaf.Paper.SixFunctorOperationDatum` and all four
`WeilConjectures.IsExceptionalAdjointAdmissibleAt*` predicates from
`Sheaf.Paper.ExceptionalAdjointAdmissibility`. Their declarations and
source docstrings were read. The imported published coefficient interface is
`ConstructibleExceptionalCoefficients.{Stage,C,Operation,System,FieldComparison}`
from `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
`CoefficientClosedStructure` is from
`Sheaf.Paper.CoefficientRingedTensorHomModel`.
The module also reuses the ringed projection and signed Hom realization
records in `Sheaf.Paper.VerdierExchange` and
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`; it does not apply
an exchange or biduality theorem. Generic categories, adjunctions, natural
isomorphisms, opposites and shift compatibility are Mathlib's declarations.

Edge cases checked in the signatures: the empty scheme and zero objects are
not excluded; no nonempty-scheme binder occurs. Positive quotient exponents
are `ℕ+` and the selected `n` has `hn : 1 ≤ n`, exactly as in the datum.
The first and second Hom variables are unrestricted finite-Tor objects;
there is no site-perfectness assumption. Shifts range over all integers.
The ringed sites retain object universe u+1 and morphism universe u. Integral
and field realizations retain the actual completed/localized/common-stage
categories. The four branches of admissibility are separate, so a
finite-stage hypothesis is not silently replaced by the stronger
algebraically closed one. Identity coefficient changes are not excluded.

Existing-declaration searches retained from the packet (`searches.jsonl`):
LeanFinder, "derived direct image internal Hom exceptional inverse image tensor
adjunction exchange isomorphism", returned eight generic adjunction/exponentiable
morphism hits, no complete four-stage pro-etale statement; Loogle,
"CategoryTheory.Adjunction, CategoryTheory.NatIso", reported unknown NatIso;
Mathlib grep, "upperShriek.*[Hh]om|[Hh]om.*upperShriek" in AlgebraicGeometry,
returned no hits; LeanSearch, "derived internal Hom exceptional inverse image
compact support adjunction canonical exchange", returned eight generic
adjunction and pullback hits. A fresh rg search of `lean/WeilConjectures` and
`lean/Sheaf` for the node id, tensor-adjunction and TensorAdjunctionExchange
found no existing complete pro-etale four-stage theorem. The upstream
`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek`
in `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` was opened: it is
on the etale derived category at finite coefficients, so it is not this
node's integral, rational and common-stage statement.

The resumed dry run initially failed only on the unscoped
`set_option maxHeartbeats 20000`. The unnecessary override was removed.
The saved node record described an older signature; `lean.statement` now
matches the module verbatim and `lean.declarations` lists the helpers.
Standalone scompile.py compilation then passed in both sandbox and library
names without warnings. The subsequent deliver2.py dry run passed preflight
and compilation (commit 4a67dc89b4 before this expanded report); nothing was
pushed by either dry run.

No new nodes, dependency modules, statement correction, or
`STATEMENT-DISPUTED` flag.

## Second reading by NO

Resumption self-check, with the node, current blueprint statement, saved module,
and both dependency declarations open. The dispatcher explicitly forbids
starting another agent; independent delivery review belongs to the maintainer.
The clause-by-clause correspondence is recorded above. In particular, I checked
that the current signature uses the bundled finite-type base schemes, that the
admissibility premise occurs inside `CorePackage.conclusion` separately at each
stage, that both Hom variances occur in `Conclusion.exchange`, and that its
inverse is constrained by the explicit evaluation/projection transpose.
`Package` identifies the operations with the supplied `six` rather than leaving
the datum unused. Finite and higher coefficient comparisons and both signed
shift variables are explicit fields. The concrete mismatches found on resumption
were the stale `lean.statement` and the unscoped heartbeat option, both repaired;
the brief Worker report was expanded to name the actual helpers and binders.
The mathematical statement and helper data were retained.


## Returned delivery repair (H3 F1 and F2)

Compared the saved packet with the return at immutable head dc185ea524b5 and
the current shared node. Only `lean` differs from the current node. The statement,
proof, dependencies and source remain unchanged. The delivery wrapper assembles
its commit on the current main branch.

F1: `CorePackage.ring` and `CorePackage.projection` range over every RingStage,
including `.integral E`. `Projection.projectionMap` and `Projection.normalized`
fix the projection to the actual `PurCompactSupport.projectionMap` at integral
as well as finite coefficients. The `rationalProjection` existential clause in
`Package` fixes the rational projection at every field L to the published
`(coefficientOperations L).rationalExchange (projectionSquare f c)` through
`SixFunctorExchangeData.projectionComponent`. The latter is `.stage.projection`
with the datum's endpoint identifications. `originalCoefficient` equates the
operation record at the original E with `six.higher`. The final closed-projection
clause uses `six.closure.commonStageExchange (projectionSquare f c)`.

`ProjectionRealized` equates the inverse projection through the support, tensor,
pullback and signed-braiding identifications. The given compactification c and
the identity-square compactification are compared by the datum's own
`U.comparison Q.f c Q.compactification` on both sides of that equality.
`tensorComponent` uses the published tensor normalization equality;
`tensorBraiding` uses `pullbackTensorRationalBraiding` or
`pullbackTensorCommonBraiding`, read in `DerivedPullbackTensorIso`. No arbitrary
braiding or projection is supplied in these clauses. Rescaling projection alone
breaks this equality before any coefficient-change tensor map can absorb it.
`compactificationSpace`, `compactificationOpen`, `compactificationProper` and
`projectionSquare` construct the identity square explicitly, including its
finite-type compactifying scheme and its commutativity and pullback proofs.

F2: `coefficientOperations L` is a published `SixFunctorHigherOperations` at
EVERY FieldStage L, with `coefficientNormalization L` supplying its
`SixFunctorIntegralNormalization` and `originalCoefficient` identifying the
original field with `six.higher`. `integralAt L` and `rationalAt L` identify all
four functors and both adjunction transposes with those operations. The records'
`integralPullback`, `rationalPullback`, `integralDirectImage`,
`rationalDirectImage`, `pullProjection` and `directProjection` retain the actual
completed/localized constructions on objects and maps. Thus the scalar,
rationalization and common-stage comparisons have realized ordinary operations
also at fields other than E. No coefficient cases or identity changes are removed.
The former duplicate `integralDatum`/`rationalDatum` witnesses at the original
field are supplied by these universal realizations and `originalCoefficient`.
`finiteDatum` and `closedDatum` still identify the finite and closed operations.

`Package` is now a proposition expressed by dependent existential quantifiers,
rather than a large structure with generated projections. Its existential
clauses retain all conclusion data, equalities, operation realizations and
normalizations. The theorem concludes `Package ...` directly. This is the same
existence conclusion as the former `Nonempty` structure; it avoids the compiler
cost of generated dependent recursors. Names prefixed with `_` are existential
witness names whose later clauses do not need to mention the witness; their
types remain required. There are no reflexive stand-ins for realizations.

Read the current server source of `SixFunctorOperationDatumStages` through
`scompile.py --source`; its interfaces match those used. No new nodes,
dependency modules, statement correction or STATEMENT-DISPUTED flag. The sole
postponed theorem remains `tensor_adjunction`, with its nine-step proof docstring.
Earlier timeouts and helper type errors were repaired in the sandbox; all final
checks use the prescribed wrapper and fixed limits.

## Second reading by NO (repair)

With the node, current blueprint and final module open, checked every hypothesis
and conclusion against the correspondence in the Worker report above. The datum,
finite extension, positive n, finite-type schemes and separated finite-type f
remain the same. Each stage retains its own `Admissible` premise. `Model.left`
and `.right` retain the displayed exchange, `Conclusion.exchange` its two
variances, `Conclusion.components` its evaluation transpose, `Compatible` the
coefficient square and `Conclusion.first`/`.second` both signed shift squares.

The original defect F1 is repaired at all finite/integral RingStages by
`Projection.normalized`, at every rational field by the projection existential,
and at the closed stage by the final `ProjectionRealized` clause. F2 is repaired
by the universal `integralAt`/`rationalAt` realizations and full coefficient
normalization records. These are existential CONCLUSIONS, never extra theorem
hypotheses. Rechecked that the final source contains these actual realizations
and projection equalities. The previously saved trial with reflexive equalities
was rejected during self-check and is not the delivered source.

Empty schemes, zero objects, all finite-Tor inputs, identity coefficient changes,
all integer shifts and the original site/category universes remain included.
All new helpers have real data and source docstrings, no new theorem was proved,
and `lean.statement` is extracted verbatim from the final signature. The
existential representation removes only generated structure machinery. The
source statement and DAG dependencies were not changed. Independent review
belongs to the maintainer; the dispatcher forbids spawning another worker.
