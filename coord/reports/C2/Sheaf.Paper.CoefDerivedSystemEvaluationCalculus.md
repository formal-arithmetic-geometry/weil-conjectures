## What changed

Prove `WeilConjectures.coefficientEvaluationTensorIso_exists` without changing its
statement. A new proof-only import, `Sheaf.Paper.CoefficientTotalTensorEvaluation`,
specializes the new `Sheaf.Paper.SemilinearTotalTensorEvaluation` theorem. It provides the ordinary total-complex evaluation comparison and its uniqueness on
pure tensor generators. Its proof uses the existing ordinary evaluation tensor
comparison, evaluation/coextension adjunction, signed total comparison, coproduct
summand equation, and pure-generator extensionality. The coefficient theorem is
its specialization to the actual coefficient ring sequence and actual section
transport. The evaluation functor equality is recorded explicitly; the generic
interface requires only preservation of zero morphisms. The coefficient module
specializes the transport to the actual `eqToHom` of the recorded equality of
abelian section objects, proved heterogeneously equal to the identity by equality
elimination. After the local unfolding improvements, keeping that specialization
in the assigned module still exceeded the 60-second limit. The assigned theorem applies the already specialized theorem with explicit
instance and universe arguments. It uses the library's existing kernel-checked
assignment pattern: build the application from elaborated local variables and
let the kernel check conversion to the goal, including the existing
section-transport definition. This avoids repeating a slow elaborator conversion
and changes no trust setting. Backward definitional-equality search is disabled
for this application and the subsequent interface block.
No existing definition or statement is changed.

All original declaration signatures, definition bodies and public imports are
retained. The existing scalar prefix is moved verbatim into the new
`Sheaf.Paper.CoefficientSystemScalarCalculus`, and the original module publicly
re-exports it. After local unfolding improvements the monolithic file still took
62–73 seconds, so this is the permitted performance split, with no mathematical
interface change. Local proof settings from the prefix are replayed for the
remaining original declarations. Three existing definition-node attachments and
the two original declaration inventories keep the moved names as re-exported declarations (review fix). Asynchronous elaboration is disabled in this module:
the original source exceeded 60 seconds with it enabled, while serialized
elaboration compiled the same interfaces in 55.7 seconds during development.
The local irreducibility settings in the new module affect only its own proofs.
The new module compiled cleanly through `lcompile.py` in 47.3 seconds after the
local irreducibility improvements; the coefficient specialization compiled in
27.3 seconds.

## Proved and sorry left

Closed one of the item's two original holes:
`WeilConjectures.coefficientEvaluationTensorIso_exists`
(`lem-coef-derived-system-evaluation-calculus`).

The remaining hole is
`WeilConjectures.coefficientDerivedSystemEvaluationCalculus`
(`lem-coef-derived-system-evaluation-calculus`), the final simultaneous assembly.
Its statement and body are untouched. No holes are added or split off.

The new theorems
`WeilConjectures.semilinearTotalTensorEvaluation_existsUnique` and
`WeilConjectures.coefficientTotalTensorEvaluation_existsUnique`, and all private
helpers, are proved. This is a proof of the ordinary evaluation hole, not a decomposition into new
unproved statements.

## No longer needed

None. All original public imports and planned dependencies of the unfinished final
assembly are retained. No source-library declaration, module, or unit route is
removed. The scalar prefix is relocated and re-exported, not pruned. Exploratory proof imports were replaced by the single import of the
new coefficient comparison theorem; they were not imports of the delivered baseline.

## Where the brief, the DAG or earlier work was wrong

The retained Z7 route note describes four holes and an old/new HomComplex import
collision. The current source has two holes, after the intervening repairs, and
its imports load successfully against the current published environment. The
ordinary evaluation proof follows the existing DAG's total-chain-comparison
route, with the generator formula and uniqueness now formalized explicitly.

The comparison works for arbitrary unbounded complexes, at every natural level,
including zero, and for zero sheaves and the empty site; its construction uses
coproduct preservation and ordinary tensor comparisons, with no K-flatness or
normalization hypothesis. Section transport is required to be heterogeneously
equal to the original section, so the generic statement admits no arbitrary
change of normalization.

## New nodes

`lem-coef-semilinear-total-tensor-evaluation`, in
`dag/nodes/sec-six-functors/lem-coef-semilinear-total-tensor-evaluation.json`,
records the fully proved generic ordinary total-tensor comparison and
pure-generator uniqueness. It is an auxiliary part of the existing calculus proof step 3, in
the same unit, and introduces no new unproved dependency. The existing calculus
node's proof, proof dependencies and proof origin record this specialization.
`lem-coef-actual-total-tensor-evaluation`, in
`dag/nodes/sec-six-functors/lem-coef-actual-total-tensor-evaluation.json`, records
the fully proved specialization to the actual coefficient sequence. Its explicit
functor equality and instance argument avoid inference through different
presentations of the same evaluation functor. It is separated only after the
local unfolding improvements, so that each delivered file meets the compile
limit. Neither auxiliary node leaves a proof hole.

The ownership and re-export record is
`coord/changes/C2-coefficient-scalar-foundation-split.md`; it lists every direct
importer and current claim holder. No importer needs an adaptation because all
exported names, signatures, data bodies and attributes are preserved.

All four delivered modules compiled in import order through `lcompile.py`:
scalar foundation 25.3 s, generic total evaluation 4.6 s, coefficient specialization
36.0 s, and assigned module 60.2 s (accepted by the compiler tool).

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
