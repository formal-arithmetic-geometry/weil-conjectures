## Worker report

The module states `WeilConjectures.coef_verdier_weil_equivariance`, with its
proof postponed by `sorry`. All helper definitions have real data. The helper
records unpack this node's conclusion; they do not replace any coefficient
category, pullback, tensor, dual, evaluation, biduality, or scalar comparison.

I read the node, its three statement dependencies and their Lean records, the
recorded modules, and the current source statement and all three proof paragraphs:
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/`
`cor-coef-verdier-weil-equivariance.md` and its `.proof.md`. The source's short
statement is expanded in the DAG into the finite-stage and compatibility clauses
that the module spells out. No statement correction is made.

Hypotheses and objects:

- The finite field, its chosen algebraic closure, geometric fiber, and geometric
  Frobenius are the existing `FiniteFieldDatum`, `D.geometricFiber X₀`, and
  `D.geometricFrobenius X₀`.
- `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` expresses exactly the coefficient-prime
  assumption. Residue-field invertibility is supplied by `sfWeilPrimeInvertible`,
  not assumed separately.
- `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]` is the fixed coefficient algebraic closure. Its
  universe is independent of the universe `u` of the schemes.
- `(X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
  [QuasiCompact X₀.hom] [IsSeparated X₀.hom]` expresses separated finite type.
  The same conditions on `Y₀` occur under the quantifiers in `Conclusion`.
- The quantifier `(f₀ : X₀ ⟶ Y₀)` is an actual map over the finite field.
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` of `f₀.left` express
  the node's separated finite-type relative map. The map used by the operations
  is the existing `FrobeniusExchange.fiberMap D f₀`. Its inherited properties
  are given by Mathlib base-change constructions, without extra hypotheses.
- `Index l Ω` ranges over all finite extensions in Ω; `E ≤ L` is precisely a
  finite coefficient-field inclusion. The existing `Coefficient`, `transition`,
  and `inclusion` give the actual coefficient fields, scalar functors, and
  common-stage images. There is no selected lattice for a Weil structure.

Clauses:

- `FiberDuality`, `FiberInternalHom`, and `FiberDualizing` are transparent uses
  of the existing `CoefQbarVerdier` types with the inherited geometric-fiber
  instances supplied explicitly. They keep the actual RHom identification and
  exceptional-unit description of omega. They introduce no new duality notion.
- `Coefficients.finite E` and `.common` assert the equivariance package on the
  actual rational and common-stage duality data of `BX`.
- `dualStructure` is exactly `c.app (op K.carrier) ≪≫ V.mapIso K.str.symm.op`,
  so it uses the rational inverse Frobenius map directly. `Duality.morphism`
  is the commuting equation for the dual of every Weil arrow. Naturality and
  the original dual functor's laws give the contravariant lifted functor.
- `Duality.comparison_evaluation` specifies the internal-Hom comparison by the
  original evaluation and the dualizing structure, using the canonical
  pullback–tensor map. `evaluation_equivariant` is the displayed evaluation
  Weil-arrow equation, and `biduality_equivariant` is the equation for the
  actual `bidual` natural isomorphism, using the induced double-dual structure.
- `Coefficients.scalar E L h` states that both the published omega comparison
  and the published duality comparison are Weil arrows. Its arguments are
  `(BX.finite.scalar E L h).omega` and `BX.finite.beta E L h`; the latter is
  normalized to the canonical scalar duality map by `BX.finite.betaNormalized`.
  The coefficient Frobenius comparison is `scalarFrobenius`, the inverse of
  the existing normalized `rationalPullbackScalarComparison`.
- `Coefficients.stageFrobenius` is tied component by component to the recorded
  `sfWeilStagePullbackIdentification` by `stageNormalized`. Thus `.stage` states
  the same equivariance for the actual common-stage images, using the existing
  `omegaComparison` and `comparison` arrows. It is not an arbitrary stage map.
- `FrobeniusAdjunctions.finite` and `.common` concern the actual exceptional
  adjunctions from the published coefficient system. `finiteNormalized` and
  `commonNormalized` pin their left comparisons to `frobeniusRational` and
  `frobeniusCommonStage` for `frobeniusCompactModel D f₀ c₀`, conjugating by
  the published rational realization and inclusion comparisons. `mate` pins
  the right comparison to the mate of that fixed inverse left comparison. `unit` and `counit` explicitly require equivariance of its
  original unit and counit, rather than selecting another adjunction.
- `Adjunctions.scalar` requires equivariance of both canonical exceptional
  coefficient comparisons; `Adjunctions.stage` requires it for both specified
  inclusion comparisons. The underlying unit/counit and scalar/stage diagrams
  are already the equations of `A.properties` and the recorded finite system.
- Evaluation and biduality compatibility equations are those of the actual
  finite scalar and common-stage duality data, not existential substitutes.
  The module adds equivariance of their evaluation/biduality edges and of the
  omega/duality comparison edges. The tensor edge uses the canonical tensor
  scalar comparison and its Frobenius scalar coherence from
  `derivedPullbackTensorIso`. Hence these same commutative diagrams are diagrams
  of Weil arrows. Faithfulness of fixed-pair forgetful functors retains their
  original equalities. The exceptional diagrams likewise use the above
  equivariant comparisons and original units/counits.
- `Conclusion` provides these data for X, every descended f₀, and both
  coefficient levels simultaneously. The compactification parameter is an
  implementation parameter of the existing exceptional-operation interface;
  the assertion covers every compactification and does not assume one is
  chosen in the main theorem's hypotheses.

Dependency declarations used:

- `Sheaf.Paper.SixFunctorOperationDatum`: the recorded
  `WeilConjectures.SixFunctorOperationDatum` and its rational/common-stage
  Verdier conventions; it imports the underlying operation interfaces.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilFrobeniusPullback`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilPrimeInvertible`, and
  `sfWeilStagePullbackIdentification`. Their fixed-pair category is Mathlib's
  `CategoryTheory.Endofunctor.IsoAlgebra`, used directly here.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `rationalDerivedTensor`, `rationalDerivedInternalHom`, their common-stage
  analogues, and `rationalPullbackScalarComparison`. The actual duality
  identification fields use these operations, including their permitted
  bounded-constructible internal-Hom domains.
- `Sheaf.SixFunctors.CoefQbarVerdier`: `CoefQbarVerdier.Duality`,
  `.InternalHom`, `.Dualizing`, `.Exceptional`, `.ExceptionalFormula`,
  `.finiteAdjunction`, `.finiteLeftScalar`, `.finiteRightScalar`, and
  `CoefQbarTensor`. These tie every conclusion to the published operations
  and maps, and not merely to arbitrary functors with the same endpoints.
- `Sheaf.Paper.FrobeniusGeometricExchange`: `FrobeniusExchange.fiberMap`,
  `.fiber_finiteType`, `.geometricCompactification`, `.frobeniusCompactModel`,
  `.frobeniusRational` and `.frobeniusCommonStage`. Mathlib `MorphismProperty.baseChange_obj` and
  `.overPullbackMap` supply the other inherited geometric properties.
- `Sheaf.Paper.DerivedPullbackTensorIso`:
  `canonicalRationalPullbackTensor`, `canonicalCommonStagePullbackTensor`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `transition`,
  and `inclusion`; `AlgebraicallyClosedCoefficients.Index`, `.Coefficient`,
  and `.coefficientInclusion` are the existing field-stage conventions.
- Mathlib `CategoryTheory.mateEquiv` is the recorded mate construction.

The remaining imports are the stated proof dependencies. The proof-only node
`lem-coef-frobenius-exchange-equivalence` currently has no recorded module, so
there is no import to add for it. The completed transpose node is imported as
`Sheaf.Paper.CompletedTensorHomTranspose`. The theorem docstring follows the
node's eight proof steps, including rationalization, counit/evaluation
normalizations, and finite-diagram descent; no proof is attempted in this stage.

Edge cases checked:

- Empty schemes and zero complexes are included: there is no nonemptiness or
  nonzero-object hypothesis in the geometric or categorical binders.
- A point and a rational Frobenius automorphism equal to a uniformizer are
  included. Only the rational `K.str` and its inverse are used; there is no
  integral endomorphism or Frobenius-stable lattice assumption.
- Identity coefficient extensions are included by `h : E ≤ L`, with no strict
  inclusion requirement; repeated stages retain the existing unit/cocycle maps.
- Arbitrary Weil morphisms and rational Frobenius isomorphisms occur in the
  equations, not only finite-stage integral maps or a chosen set of generators.
- The coefficient closure and schemes have independent universes. Finite fields
  use the existing small representatives, as prescribed by the dependency.
- No additional geometric-fiber property is assumed; all are inherited by the
  specified base-change constructions. No ambient exceptional adjoint is used.

Searches (retained earlier attempt, recorded in `searches.jsonl`, checked against
current project sources):

- `msearch.py`, LeanFinder: “Verdier duality of Weil complexes equivariant
  evaluation biduality exceptional adjunction coefficient extension”: 8 hits,
  headed by homological-complex evaluation/corepresentability and Ext
  equivalences; none states this theorem on these completed categories.
- `msearch.py`, Loogle: `"IsoAlgebra", "Adjunction"`: no hits.
- `msearch.py`, Mathlib grep in `CategoryTheory`:
  `Weil.*[Dd]ual|[Dd]ual.*Weil`: no hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Weil/duality combinations
  found the upstream étale Weil and pairing constructions and the recorded
  rational/common-stage duality interfaces. None states the completed
  coefficient equivariance theorem. Searches for the exact node id and proposed
  declaration find no existing implementation in those source directories.
  The upstream derived-of-Weil-sheaves construction is deliberately not used:
  the dependency node specifies fixed pairs in the constructible category.

## Second reading by NQ

This is the author's final check; the maintainer supplies the independent review
under the dispatched-worker brief. I compared the source's three paragraphs,
the full DAG statement, and every record field. The retained draft originally
required extra instances on the geometric fiber map, and its source-map
instances did not resolve. The revised statement derives those properties from
the original hypotheses and supplies the fiber structure-map instances
explicitly. I checked the directions of `D(theta inverse)`, the biduality
square, the exceptional unit and counit equations, and the mate of inverse left
comparison. I also checked that scalar and common-stage comparisons are the
published maps, including identity coefficient inclusions, and that the
Frobenius structure ranges over rational pairs with no lattice restriction.
No mathematical node correction or disputed statement is proposed.

Resumed packet check (2026-10-19): the required initial dry run found a missing
line break between the inherited separatedness instance and `Duality` in the
`Coefficients.common` field, plus an extra space before `:=` in
`FiberExceptional`. I repaired these formatting defects; the remaining reported
unknown identifiers were consequences of the first parse failure. The prescribed
`scompile.py` then compiled both the sandbox check (52.6 s) and the library
module (45.4 s), with no warnings or errors. I reopened the current blueprint
statement and proof, the repair note (resolved stage 1), all three statement
dependency records and the relevant source declarations. The node differs from
the read clone only in `lean`; its recorded theorem signature matches the file
verbatim, all lines are within 100 characters, and the main theorem is the only
postponed proof. No mathematical statement or declaration signature changed in
this repair.

## Returned-head repair (22a032a16659)

F1: `Conclusion` now requires `DualizingNormalization` for X and for each Y.
For the descended structure morphism, this selects the actual exceptional
adjunction, requires its canonical compact-support Frobenius exchange through
`FrobeniusAdjunctions`, and uses its right mate. `DualizingMate.normalization`
is the equation theta_omega followed by omega ≅ G(1) equals pullback of that
identification followed by the mate and G of the constant-object identification.
`constant_unit` fixes the latter by the specified tensor left-unitor equation.
Thus the dualizing structure is constrained by step 3; it is no longer merely
a free field constrained by evaluation. This is imposed at every finite
coefficient stage and in the common-stage category. In the point/rank-one case,
rescaling theta_omega by a nonidentity scalar fails this mate normalization;
rescaling the identification on both sides does not repair that failure.

F2: `FrobeniusAdjunctions.finiteNormalized` identifies the left exchange,
conjugated by `A.system.ring.rationalLeft`, with the actual
`FrobeniusExchange.frobeniusRational` component. `commonNormalized` does the
same for `frobeniusCommonStage`, using `A.leftComparison` and the canonical
`sfWeilStagePullbackIdentification`. Both use exactly
`frobeniusCompactModel D f₀ c₀`. The existing mate, unit and counit equations
are retained in addition to this normalization, so they cannot serve as a
substitute for pinning the left exchange.

F3: `Conclusion`, `Adjunctions`, and `FrobeniusAdjunctions` quantify over
`c₀ : Compactification f₀.left`; every geometric exceptional record and
comparison uses `FrobeniusExchange.geometricCompactification D f₀ c₀`.
No arbitrary geometric compactification is quantified by the conclusion.
The finite-field point and structure-morphism property instances are actual
identity/inherited instances, not extra assumptions.

The source statement and three proof paragraphs in main-20261015 were reopened,
as were the coefficient-system realization and finite/common-stage Frobenius
exchange signatures. The first required resumed dry run exposed invalid
`Adjunction.left`/`right` projections in the retained repair. They were replaced
with the actual finite operation functors, and all structure-map properties
are supplied from the original hypotheses. This repair changes helper
conclusion data, not the DAG's mathematical statement or main theorem binders.
