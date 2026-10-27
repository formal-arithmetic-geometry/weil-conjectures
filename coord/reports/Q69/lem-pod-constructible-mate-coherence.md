## Worker report

Q69 stage 2, 2026-10-22. Repair of returned head e53c3a32238b.
The retained packet is rebased by preserving the current live node's accepted
statement, proof, proof dependencies and metadata, then attaching the Lean record
and added statement dependencies. The mathematical statement is unchanged.
Every mathematical theorem remains `sorry`; definitions have real data.

The module `Sheaf.Paper.ConstructibleMateCoherence` states the constructible
exceptional mate assertion and normalized rational and common-stage comparison
packages. `Sheaf.Paper.ConstructibleWeilModelSquares` supplies the finite-field
model diagrams and their actual scalar extension. Names below without a namespace
are in `WeilConjectures.PodConstructibleMate`.

### Hypotheses and clause correspondence

1. The primes, positive exponent, finite field, algebraic closure and coefficient
   prime are `FiniteFieldDatum` and `CoefficientDatum`. The rational assertions bind
   `E`, `Field E`, `Algebra (Padic C.l) E` and `FiniteDimensional (Padic C.l) E`.
   `C.different` is the distinct-prime hypothesis. Common comparisons use its fixed
   `C.Qbar`; common evaluation and exchange invertibility additionally admit any
   `Ω : Type v` with `Field`, `Algebra` and `IsAlgClosure` structures, independently
   of the scheme universe. `Models D` is the full subcategory of finite-type models
   over k₀, with all over-morphisms and no structural separatedness. `fiberModels`
   is the actual `Over.pullback` along Spec k → Spec k₀.
2. The stipulated constructible adjunction is `adj : F ⊣ G`. The generic theorem
   binds the two Frobenius equivalences as `S,T` and their specified comparison as
   `α : F ⋙ T ≅ S ⋙ F`. In Lean execution order this has components TF ≅ FS.
   `AdjunctionCoherent` requires `IsIso (mateEquiv adj adj α.inv).natTrans`, and
   fixes the isomorphism `β` to precisely that mate. Its next component equation is
   literally the unit–map–counit formula, with `adj.unit`, `G.map α.inv` and
   `G.map (T.map adj.counit)`. No ambient exceptional right adjoint is assumed.
3. `PodCovariantWeilLiftSpec G β` fixes its object structure to β followed by
   G(θ), arrows to G(u), and forgetting to G. `IsoAlgebra.mapOfNatIso α` is the
   left lift with structure α followed by F(θ). `IsoAlgebra` is the existing category
   of invertible fixed pairs, with its existing carrier Hom sets.
4. The two next conjuncts of `AdjunctionCoherent` write exactly the two mate
   equations, in execution order: Sη followed by βF then Gα; and αG followed by
   Fβ then εT. The following two conjuncts quantify over every fixed pair and state
   exactly the unit and counit structure equations. The final existential is an
   adjunction of these same two lifted functors, with carrier unit/counit equal to
   `adj.unit`/`adj.counit`; both original triangle identities are explicit.
5. `RationalLifts` fixes pullback componentwise to `rationalModelPullbackComponent`,
   direct image to its right mate, compact support to literal
   `FrobeniusExchange.frobeniusRational` at `frobeniusCompactModel`, and arbitrary
   compactifications by conjugation with the recorded compactification comparison.
   Exceptional comparison is the right mate of inverse support comparison. Tensor
   is fixed to `canonicalRationalPullbackTensor`. The operation data are the existing
   normalized `SixFunctorOperationDatum`; no six-functor coherence theorem is assumed.
6. `CommonLifts` repeats every normalization in the actual common-stage category:
   pullback is `podCommonSquarePullbackComponent`, support is literally
   `FrobeniusExchange.frobeniusCommonStage`, exceptional is its inverse's mate, and
   tensor is `canonicalCommonStagePullbackTensor`. Thus the common exceptional
   adjunction is applied with a equal to the actual common-stage Frobenius exchange.
7. `rational_comparisons_coherent` and `common_comparisons_coherent` respectively
   assert these normalized packages and `RationalCoherence`/`CommonCoherence`.
   Each coherence predicate contains ordinary and exceptional lifted adjunctions;
   pullback and direct composition; support compactification change and composition;
   exceptional composition; direct and compact-support exchange; and projection.
   Every lifted comparison is fixed to its specified carrier by equality/HEq.
   Exchange and projection remain transformations, with conditional invertibility
   only when the underlying comparison is already invertible. The common conjuncts
   quantify over arbitrary common Weil structures, without an integral lattice.
8. `homStructureMap` writes the inverse in Hom's first argument explicitly:
   the comparison followed by H(θ_K inverse, θ_L). `EvaluationEquivariant` states
   invertibility of this structure and the exact tensor/evaluation Weil equation.
   `rational_evaluation_equivariant` and `common_evaluation_equivariant` fix all
   typed inputs by their hP/hT/hH/hSC/hκ/hμ equalities to the actual operations,
   closed data and canonical comparisons. `hJ` retains the given permitted-pair
   domain; no unrestricted constructible internal Hom is asserted.
9. Composition, whiskering, inversion, and mates take place in the existing
   `IsoAlgebra` categories and their functor/natural-transformation categories.
   Their arrows already carry the Weil equation. The explicit generic mate is in
   `AdjunctionCoherent`; the exceptional composition conjuncts fix its canonical
   comparison carrier, and both stages' exchange conjuncts fix the actual exchanges.
   The unsplit coefficient-transport theorem is a proof dependency only, as in
   the unchanged DAG proof step 6; this packet does not restate that theorem.
10. `frobenius_exchanges_isIso` asserts invertibility of the actual rational and
    common-stage Frobenius arrows at `frobeniusCompactModel`. Relative separatedness
    and finite type are bound for f₀; structural separatedness of X₀ or Y₀ is absent.
    No new invertibility follows merely from equivariance.

### Return points repaired

1. Added `def-pod-weil-lift-interfaces`, owning the exact existing plain definitions
   `PodCovariantWeilLiftSpec`, `podWeilHomPairs`, `podWeilHomPairForget`,
   `podRationalSquarePullbackComponent`, and `podCommonSquarePullbackComponent`.
   Added `def-pod-partial-closed-interfaces`, owning the exact existing
   `PodPartialClosed`, `.evaluation`, and `podPairPullback`. Both records are
   `existing: true`, with their published modules, and the item cites both.
   The theorem-owned rational/common closed data and Hom comparisons remain cited
   through `lem-pod-derived-automorphism-hom-evaluation`: those are uniquely
   characterized constructions, not additional plain interface definitions.
2. The item cites `def-pur-completed-pullback-tensor-comparison` for
   `canonicalRationalPullbackTensor` and `canonicalCommonStagePullbackTensor`.
   The old theorem dependency is absent from the item's statement dependencies.
   The new square-component definition owner separately cites that theorem for
   its genuinely uniquely characterized pullback composition isomorphisms.
3. Retained `lem-weil-frobenius-square-cartesian`: its proof component actually
   types the commuting square passed to the pullback comparison.
4. Removed the delivered module and node record of
   `lem-pod-equivariant-mates-coefficient-transport` and its added statement edge.
   Its unchanged proof-plan citation remains. No declaration in the item statement
   refers to that removed module.
5. Added the full `CommonLifts`, `CommonCoherence` and
   `common_comparisons_coherent` analogue described in points 6–7 above.
6. The item cites `def-weil-operation-exchange-coefficient-descent`, the owner of
   `FrobeniusExchange.fiberMap`.

### Dependency declarations used

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `.CoefficientDatum`,
  `.geometricFiber`; `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `.geometricFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded rational/common categories,
  pullback, tensor, Hom and permitted-pair predicates.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilFrobeniusPullback`,
  `sfCommonStageWeilFrobeniusPullback`, and `sfWeilPrimeInvertible`.
- `Sheaf.Paper.SixFunctorOperationDatumStages`: `SixFunctorSpace`,
  `SixFunctorCompactifiedSquare`, `SixFunctorPushStage`,
  `SixFunctorHigherOperations`, `SixFunctorCommonStages`;
  `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`.
- `Sheaf.Paper.SixFunctorDatum`: `sixFunctorDirectComposition` and
  `sixFunctorExceptionalComposition`. No six-functor axiom is an assumption.
- `Sheaf.Paper.FrobeniusSquareExchange`: `FrobeniusExchange.fiberMap`;
  `Sheaf.Paper.FrobeniusGeometricExchange`: `.fiber_finiteType`,
  `.geometricCompactification`, `.frobeniusCompactModel`, `.frobeniusRational`,
  `.frobeniusCommonStage`.
- `Sheaf.SixFunctors.FrobeniusSquareCartesian`:
  `FiniteFieldDatum.frobenius_square_cartesian`.
- `Sheaf.Paper.SemilinearFieldOperationLifts`: the definitions in the new
  `def-pod-weil-lift-interfaces` record.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: the partial closed interfaces in
  the new definition owner, `podRationalClosed`, `podCommonClosed`,
  `podRationalHomComparison`, and `podCommonHomComparison`.
- `Sheaf.Paper.CompletedPullbackTensorComparison`:
  `canonicalRationalPullbackTensor`, `canonicalCommonStagePullbackTensor`.
- `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction`:
  `IsoAlgebra`, `.mapOfNatIso`, `.prod`, `.forget`; Mathlib
  `CategoryTheory.Adjunction.Mates`: `mateEquiv` and its mate calculus.
- Mathlib `Over`, `Over.pullback`, `ObjectProperty.FullSubcategory`, scheme
  morphism properties and `IsPullback`; `WeilConjectures.Compactification.Defs`:
  `Compactification`, `.copy`.

### Edge cases, searches and checks

Identity functors/maps give the original unit/counit formulas. Zero objects, zero
maps and empty schemes are not excluded. Model structures can be nonseparated.
Arbitrary compactifications are quantified; their change maps have exact carriers.
The common evaluation/exchange clauses allow an independent coefficient universe.
Arbitrary common Weil arrows do not require an invariant lattice. Noninvertible
exchange/projection maps remain morphisms. The Hom predicate retains every supplied
restriction, including the contravariant first argument. All variables and universes
are explicit with `autoImplicit false`. No statement correction or dispute is needed.

The retained searches are in `searches.jsonl`. Original LeanFinder query “Weil fixed
pairs exceptional inverse image Frobenius adjunction mate coherence” returned only
ordinary mate facts; Loogle for mateEquiv and IsoAlgebra gave no exact match;
Mathlib/source grep located the reused interfaces. Model-square searches with
LeanSearch and LeanFinder found individual base-change facts, Loogle for Over.pullback
and FullSubcategory no such model interface, and source/DAG/blueprint grep no duplicate.

For the definition-owner repair, LeanSearch query “Weil fixed pair covariant lift
formula permitted internal Hom pairs forgetful functor and Frobenius pullback square
comparison” returned eight unrelated Frobenius/fibered-category facts. LeanFinder
query “Partial tensor Hom closed transposition evaluation inverse transpose identity
functor on permitted pairs” returned eight rigid/closed monoidal facts, no partial
interface. Mathlib grep for the exact interface names returned zero. Project and DAG
rg found exactly the two published modules and their theorem records; no definition
node owned them. `blueprint_refs.py search 'partial closed'` returned zero; search
'Weil lift' returned three unrelated weight/purity nodes. The raw responses are
included in each new owner's mathlib_searches. These are existing definitions,
not replacement implementations.

The first retained-packet dry run compiled the main module on the server in 45.9 s
and found four line-width warnings. Those lines are reflowed in this repair.
All delivered modules are checked using the prescribed scompile.py/deliver2.py wrappers;
the dry run includes #check probes for every existing-owner declaration.

## New nodes

`def-pod-constructible-weil-model-squares` in
`Sheaf.Paper.ConstructibleWeilModelSquares` defines the finite-field model category,
compactified diagrams, actual scalar-extension image, and composition transport.
Its source is the model convention and comparison diagrams of prop-weil-operations
and lem-fix-weil-operations. Its searches distinguish models over k₀ from the existing
geometric diagrams over k. Its named pullback-preservation theorem supplies only
proof fields; no geometric datum is chosen from an arbitrary existence statement.

`def-pod-weil-lift-interfaces` records the existing definitions in
`Sheaf.Paper.SemilinearFieldOperationLifts`. Its statement spells out the covariant
Weil formula, the exact permitted-pair predicate and forgetful functor, and the
canonical rational/common square components through the existing compositors.
The source is lem-fix-weil-operations' operation and internal-Hom paragraphs.
The searches above locate these definitions, and no prior definition owner;
`existing: true` reuses them without another module.

`def-pod-partial-closed-interfaces` records the existing definitions in
`Sheaf.Paper.DerivedAutomorphismHomEvaluation`. Its statement spells out the additive
transpose, parameter naturality, evaluation as inverse transpose of the identity,
and restricted pair functor. The source is the tensor/Hom/evaluation paragraphs of
lem-fix-weil-operations (the published declarations also cite Stacks 08J9/0GMX).
The searches above found no definition owner and distinguish this partial interface
from Mathlib's globally closed monoidal categories. It is `existing: true`.

## Second reading by Q69

Self-check of the repaired node and both delivered files, performed in this worker
session; no other agents were started. The accepted split and natural-language
statement are unchanged. Re-read all six return points against the actual packet:
the two new existing definition owners list the named plain definitions and are
cited; canonical tensors and fiberMap have the requested owners; the Cartesian-square
theorem stays; the unwanted transport module and record are absent; the common-stage
predicate now mirrors every rational normalization, both lifted adjunctions, four
composition conjuncts, compactification change, both exchanges and projection.
In particular `CommonLifts.supportNormalization` names frobeniusCommonStage at
frobeniusCompactModel, `exceptionalMate` names its inverse's mate, and
the second conjunct of `CommonCoherence` uses that specified support comparison.
The common comparison theorem supplies these lifts from the actual common-stage
operation datum. The report's obsolete claims about delivering the coefficient
transport prerequisite were removed. Long lines found by the dry run were reflowed.

### Continuation self-check and compile repair

The prescribed retained-packet dry run confirmed a 60-second timeout in
`ConstructibleMateCoherence`. A sandbox-only profiler located repeated elaboration
of the inferred category and linear structure of the lifted-functor abbreviations.
Each rational/common pull, direct, support and exceptional functor now has an
explicit result type and explicit original endofunctors/operation arguments to
`IsoAlgebra.mapOfNatIso`. These convenience transports, including tensor, are real
irreducible definitions, retaining their original bodies. The two compactification
comparison carrier equations use `HEq`, just as the other comparison fields do;
unfolding the definitions identifies their endpoint types and gives exactly the
same equality. Coefficient `Algebra` is root-qualified to avoid the opened
endofunctor namespace's unrelated `Algebra`.

Read the item's current live statement and compared its fields against the packet:
only `lean` and added `stmt_deps` differ, with no removed base dependency. Read both
actual modules, all three new definition records and the source's operation,
internal-Hom, exceptional-adjunction, composition/exchange and projection paragraphs
in `sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`.
The return's six repairs remain present: exact existing plain-definition owners;
canonical tensor owner; genuine Cartesian-square dependency; no delivered
coefficient-transport theorem or statement edge; common-stage normalizations and
all coherence conjuncts; and the `fiberMap` definition owner. The new explicit types
introduce no mathematical hypothesis or different comparison.

To avoid generating unused recursors and large structure auxiliary declarations,
`RationalCoherence` and `CommonCoherence` are transparent Prop definitions, each
with the same ten clauses as a conjunction. Comments name the clauses in order:
ordinaryAdjunction, exceptionalAdjunction, pullComposition, directComposition,
supportComparison, supportComposition, exceptionalComposition, directExchange,
compactExchange, projection. In particular the second common conjunct applies
`AdjunctionCoherent` to the normalized support comparison, whose
`CommonLifts.supportNormalization` is literally `frobeniusCommonStage`.
Tensor convenience definitions also have explicit compact types. No coherence
clause was removed or altered by this presentation change.

The final category-inference repair names `rationalStageCategory` and
`commonStageCategory` as abbreviations of the existing instance families and
passes them explicitly to `SixFunctorPushStage` projections. These are the same
category structures, definitionally; no local instance or new category is used.
The corrected elaboration transparency setting permits these literal interfaces
without repeatedly reconstructing the underlying derived-category dictionaries.
