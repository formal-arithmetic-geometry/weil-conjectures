## What changed

Proved `WeilConjectures.transportedReductionSystems_pullback_normalized` without changing
its signature. The added imports are private proof imports:
`Sheaf.Paper.QuotientExpressionKFlatNormalization` and
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients` (to compare the flatness
predicates for the resolution terms).

Represent the arbitrary ambient derived object by a flat-term K-flat complex P. Apply
`SY.reductionModel` and the existing singleton strict quotient-expression normalization
theorem to P. Their quotient models are isomorphic as whole complexes: the finite-level
isomorphisms respect every horizontal map, and the private `sequenceModuleIso` constructs
the sectionwise maps, restores linearity along the slice ring isomorphism, and checks
naturality by horizontal/vertical factorization. The private `presheafSequenceIso` and `sheafSequenceIso`
perform the assembly for arbitrary coefficient presheaves, avoiding repeated kernel
unfolding of the concrete coefficient rings. `sequenceComplexIso` checks the chain
condition. The private `restrictedMap_smul` and `conjugateSquare`
check the scalar and categorical algebra without unfolding the concrete coefficient rings.
The generic `pushforwardTransitionSection` also extracts the recorded section formula
before specializing to those rings. `sheafSequenceIsoOfTransitions` combines that
formula with the commuting squares generically, avoiding kernel timeouts from
concrete equality transports and scalar-restriction conversions.
Pull back this isomorphism and use the exact-derived comparison to reach the
normalized `Generated.pullF (Generated.input 0)` expression. The private `normalizedIso`
transports the actual universal Hom-set bijections by transition naturality.

Validation: the complete final module compiled through `lcompile.py` in 37.4 seconds,
with no warnings and no `sorry`, using the default heartbeat limit. The temporary
diagnostic module and profiling options have been removed.

The node proof and dependencies now record this route. The strict quotient normalization
node is used as a general tool; its singleton pullback case gives exactly the representative
calculation needed here, without replacing any step of the trace-transport unit.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.transportedReductionSystems_pullback_normalized`
(node `stage3-trf-transported-pullback-normalized`). Added 0 holes. No `sorry` remains in
the item or any new file. All private helpers are proved. Existing dependencies,
including the strict quotient-expression theory, retain their own separate obligations.

## No longer needed

No existing import was removed, and no module is withdrawn. No global pruning is claimed.
The former direct proof dependency `lem-pur-system-normalized-tensor-closure`
(`Sheaf.Paper.SystemNormalizedTensorClosure`) is unnecessary for this proof: the existing
strict quotient-expression theorem already supplies the required normalized pullback.
`prop-weil-pbc-proetale-constant-exact` is no longer a direct dependency of the item;
constant-coefficient exactness remains used inside the strict quotient theory.
`lem-coef-derived-system-evaluation-calculus` is retained for the supplied strict reduction
model. The replacement direct tool is `lem-pur-quotient-expression-kflat-normalization`;
`lem-pc-kflat-resolution` supplies the arbitrary ambient representative.

## Where the brief, the DAG or earlier work was wrong

The original plan did not supply the comparison between its abstract geometric inverse
image and the specified whole-system pullback. An existing strict quotient-expression
normalization theorem avoids constructing that comparison. Its use here includes an
actual whole-complex comparison, rather than inferring equality of derived system maps
from their finite evaluations.

STATEMENT-DISPUTED (separate dependency, reported for its owner):
`quotientExpressionKFlatOperations`
accepts arbitrary input systems N and assumes only finite-level goodness of generated
expressions, then asserts their normalization. That statement omits normalization of the
inputs. On a nonempty site take N_n = B_n[0] with zero nonidentity horizontal transitions.
All finite fibers are free and K-flat, as are finite tensors and pullbacks, but a transition
adjunct is zero, not invertible. The present proof uses the correctly restricted theorem
`quotientExpressionKFlatNormalization`, whose inputs are actual quotient reductions of P;
it does not apply `quotientExpressionKFlatOperations` to arbitrary N. Repairing the latter's
interface belongs to its own item and is reported here for the maintainer.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
