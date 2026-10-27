## What changed

Moved the six existing comparison definitions, unchanged, into
Sheaf.Paper.ProperCoefficientDescentData and publicly reexported them from the
original module. The change record is
coord/changes/U1-proper-coefficient-descent-data.md. There are zero current Lean
importers and no consumer adaptation is needed.

The original properCoefficientDescent statement is unchanged. Its proof now
constructs the rational isomorphisms, the ordinary stage-system morphism, compatible
forward and inverse transformation families, and their descended natural
isomorphism. Same-stage naturality and its further-stage version use
StageSystem.Morphism.Hom.mapAt_naturality. The final isoToStage equation follows
from naturality of the descended transformation.

ProperRationalScalarSquare localizes the integral scalar equation, identifying the
prescribed rational transitions and comparison components, including the inverse
ordinary comparison. ProperIntegralScalarSquare isolates Steps 1--3 of the original
plan: equality of normalized integral scalar maps before rationalization.

## Proved and sorry left

Closed the original hole in
WeilConjectures.ProperCoefficientDescent.properCoefficientDescent
(lem-weil-proper-coefficient-descent), by decomposition. One of one original holes
is replaced; this is not an unconditional proof of the integral geometric step.

Added one hole:
WeilConjectures.ProperCoefficientDescent.integralScalarSquare
(lem-weil-proper-integral-scalar-square). It is strictly the integral scalar-square
conjunct, with no rationalization or common-stage descent conclusion. Its proof is
exactly `by sorry` and its docstring and node retain the coherent-system argument,
not an invalid appeal to faithfulness of separate evaluations.

The rational scalar square and all private helpers are proved; there are no other
holes in the delivery, and no hole in any definition.

Validation: lcompile.py accepted the unchanged-data module, the rational scalar
square (42.0 seconds), the integral statement after import cleanup (2.4 seconds),
and the complete parent theorem (32.2 seconds). The parent has only style warnings.
Mechanical comparison confirms all original signatures and six definition bodies
are unchanged. Every DAG proof_deps list equals the union of the step uses.

## No longer needed

Removed the direct proof imports Sheaf.SixFunctors.OpenTensorNormalization,
Sheaf.Paper.CoefficientExtensionReductionModel,
Sheaf.Paper.MixedReductionUnit,
Sheaf.Paper.IntegralSystemReductionFullyFaithful,
Sheaf.CategoryTheory.ScalarLocalization and Mathlib.LinearAlgebra.TensorProduct.Tower
from the parent module. The integral geometric dependencies remain in the new
integral scalar-square DAG plan; its statement-only module needs only the shared
data import. The unused proof-only imports of OpenTensorNormalization,
ProperIntegralTowerComparison, StrictDirectImageMixedUnit,
CoefficientExtensionReductionModel and IntegralSystemReductionFullyFaithful were
removed from that module. None is claimed as globally pruned.
ScalarLocalization and tensor base-change declarations are available through the
public prerequisites. No existing module or DAG node is withdrawn.

The top-level DAG now cites the integral scalar square, the proved rational square,
and the raw-localization natural-isomorphism API, followed by the existing stage
system API. The original geometric dependencies remain reachable through the
integral scalar-square node; their proof work is still needed. No unit statement
or unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan describes the right mathematical argument, but it does not
already provide a declaration of the integral scalar-square conclusion in the
existing shared normalization types. Its coherent-system proof is the remaining
subargument. The existing raw-localization and StageSystem APIs handle the rational
and quotient descent without adding separate lemmas for every representative step.

The first standalone parent/rational compile attempts were submitted before the
new shared data module's compiled artifacts were available; they failed at that
import. Validation uses the dependency-ordered sandbox compile thereafter.

Edge cases: identity field inclusions use the fixed scalar unit; the zero object
uses actual functor and natural-isomorphism laws. Arbitrary ramification is allowed:
the integral proof uses the mixed unit universally, not flatness of quotient maps.
All quotient exponents retain the original n+1 convention. Rational Hom modules
may have torsion before localization; localization and additive tensor formulas
work without a torsion-free hypothesis.

## New nodes

- def-weil-proper-coefficient-descent-data: the unchanged identity-open constructions
  and full-tower normalization predicates, in a cycle-free common module.
- lem-weil-proper-integral-scalar-square: the integral part of Steps 1--3, with the
  actual compact and ordinary normalized comparison data. One remaining hole.
- lem-weil-proper-rational-scalar-square: Step 5, applying localization to the
  integral equation and using the recorded component formulas. Proved.

All are under sec-zeta-weil/sk-input-weights and trace to the first paragraph of
prop-weil-proper-compact-coincidence. The blueprint search found no separate node
stating these normalization-specific squares; the existing general localization
lemmas and the given proper integral tower comparison were read first.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
