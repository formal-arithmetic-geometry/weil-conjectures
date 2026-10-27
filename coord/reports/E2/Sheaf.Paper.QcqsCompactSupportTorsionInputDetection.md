## What changed

This is a partial proof delivery. In the assigned module, proved
`WeilConjectures.sfQcqsCompactSupport_torsion_input_iff_reduction_eq`, the equivalence
between the torsion-input and finite-evaluation hypotheses of the assigned node and
its parent. The original theorem and its signature remain;
its stronger conclusion is still disputed and unproved.

The proof has four proved private helpers. `quotient_constructible` constructs the
restricted finite quotient of a constructible integral input as the third vertex of
a distinguished principal-reduction triangle. Triangulated closure gives its actual
constructibility, without choosing any data from a mere existence theorem.
`reduction_naturality` transports a retraction through a natural isomorphism and
cancels the resulting split monomorphism. `torsion_input_reduction_eq` assembles
these steps for the actual compact-support functors. For the converse,
`reduction_map_ext_on_restriction` is the proved scalar-adjunction cancellation
argument already used privately in the parent module, together with the existing
proved torsion coefficient action. The parent module is not imported.

For the geometric specialization, the quotient-input augmentation is the recorded
scalar-adjunction unit. Its reduced retraction is the actual counit, by the left
triangle identity. The independent normalized-isomorphism existence theorem and
invertibility of the actual finite mates give the required natural comparison for
the recorded integral functor. Naturality and the hypothesis at the quotient input
then identify every finite reduction of the two components. Conversely the torsion
coefficient action and scalar Hom transpose identify the components on finite
inputs from their reduced components. This proves a step of the original argument; it does not rename the remaining hole or assert that
finite evaluations are faithful.

Added proof imports: QcqsCompactSupportNormalizedIsoExistence,
QcqsCompactSupportFiniteComparison, QcqsCompactSupportTorsionCoefficientAction,
SfIntegralConstructibleTriangulated, IntegralPrincipalConeQuotientAugmentation (including its proved private regular
coefficient sequence), and AdicReductionTriangle. Public imports are unchanged.
The fully proved partial theorem and its node are attached to the assigned module,
as permitted by coord/brief-stage3.md section 3; no new unproved statement is added.

The construction works for index zero (exponent one), zero inputs and empty schemes.
It uses no finite-field datum and no separatedness of the structure morphisms.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added or split off: **0**.

Proved:

- `WeilConjectures.sfQcqsCompactSupport_torsion_input_iff_reduction_eq`
  (`lem-qcqs-compact-support-torsion-input-finite-evaluation`).
- Private helpers `reduction_naturality`, `quotient_constructible`,
  `reduction_map_ext_on_restriction`, and `torsion_input_reduction_eq`, all with
  complete Lean proofs and no sorry.

The sole remaining sorry is
`WeilConjectures.sfQcqsCompactSupport_torsion_input_ext`
(`lem-qcqs-compact-support-torsion-input-detection`). Its original statement is
unchanged and its proof remains exactly `by sorry`. The existing
STATEMENT-DISPUTED annotation is retained. The finite-evaluation result is a partial
proof, not a completed proof or a new decomposition of that remaining obligation.

Validation: the final single-file server compile passed in **5.2 seconds**.
The original theorem signature and public imports were compared verbatim with the
repository source and are unchanged. Both node proof-dependency lists equal the
union of their proof-step uses. The delivery runs the mandatory server preflight.

## No longer needed

No module is withdrawn and no existing proof import is removed: the item previously
had only its two public statement imports. No existing DAG dependency is claimed to
be globally unnecessary while the original proof remains unfinished.

The proved finite-evaluation step does not separately invoke the old plan's
CompactSupportReductionTower, CompactSupportRepresentativeIndependence,
CompletedDirectImageLimits, RingedStrictTowerHomotopyLimitIndependentCoefficients,
CoefDerivedSystemEvaluationCalculus, or IntegralOpenReductionComparison declarations.
Instead it uses the independent normalized-isomorphism existence theorem and the
actual finite comparison, with elementary adjunction cancellation. Some of those
older declarations remain transitive dependencies of the independent existence
argument; the unresolved original finish is also retained in the node. They are
therefore not withdrawn or marked as pruned by this packet.

## Where the brief, the DAG or earlier work was wrong

The quoted plan passes from agreement on restricted quotient inputs to agreement
of coherent comparisons on a strict resolving diagram. The available hypotheses
specify ordinary natural transformations on the derived constructible category;
they do not specify such a coherent lift. The derived reduction/total-limit
adjunction detects an entire system morphism, but its individual finite evaluations
cannot be substituted for that system morphism without an additional argument.
The new proof establishes the equivalence of torsion-input and finite-evaluation
agreement and stops before that unsupported substitution. In particular, passing
from the parent's finite-evaluation hypothesis to the torsion-input hypothesis does
not make the remaining rigidity assertion strictly simpler: the two hypotheses are
formally equivalent. Another split between them would only repackage that obligation.

The available integral constructible Milnor Hom injectivity statement uses a
FiniteFieldDatum and separatedness of the structure morphism. The assigned theorem
has an arbitrary base field and no such separatedness assumption. This packet does
not add those hypotheses or claim a counterexample to the original theorem. It
retains the earlier Q7 dispute and supplies a proved part for its eventual resolution.
No new sorry with the same obligation under another name is introduced. The unit's
realized statement and proof-step route are untouched.

## New nodes

`lem-qcqs-compact-support-torsion-input-finite-evaluation` records the proved equivalence
of torsion-input and finite scalar-reduction agreement in the assigned module. Its
proof dependencies are the principal coefficient sequence, the adic reduction triangle, integral triangulated
closure, the scalar adjunction, the actual finite compact-support comparison and the
independent normalized-isomorphism existence theorem, plus the existing torsion
coefficient action for the converse. Mathlib searches found the
adjunction left triangle identity and generic split-monomorphism cancellation.
The original node now distinguishes this proved part from its unfinished proposed
coherent-system argument. No change record is needed: no existing signature,
definition, attribute or public import changes.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
