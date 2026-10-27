## What changed

Replaced `AlgebraicGeometry.strictEtaleCompactSupportTransport_composition`'s hole
with an explicit reduction through ordinary tensor associators and the composition
of a single normalized inverse-image square. Its signature and public imports stay
unchanged. Added proof imports of `Sheaf.Paper.StrictEtaleTransportAssociator` and
`Sheaf.Paper.StrictEtaleInverseTransportComposition`.

The item constructs the derived associators by localization and proves their
representative equations. It proves naturality of the mate equivalence in both
coefficient functors, transfers the inverse-image equations to the open and proper
mates, and combines them by functoriality, cancellation, and naturality into the
inverse compact-support projection equation. All helpers in the item are private
and fully proved.

## Proved and sorry left

Closed the original hole of
`AlgebraicGeometry.strictEtaleCompactSupportTransport_composition` by decomposition.
Added exactly two holes, each in a separate new module:

- `AlgebraicGeometry.strictEtaleOrdinaryTransportAssociator_exists`
  (`lem-pur-strict-etale-transport-associator`): ordinary tensor associator existence,
  with its unit normalization. It asserts no derived or geometric result.
- `AlgebraicGeometry.strictEtaleInverseTransport_composition`
  (`lem-pur-strict-etale-inverse-transport-composition`): compatibility for one
  normalized geometric inverse-image square with given composition records.
  It asserts no associator existence, open/proper mate, or compact-support result.

There are no holes left in the item module. This is a decomposition, not a net
proof gain: one original hole closed, two smaller holes added. All three modules compiled on the project server; the item took 12.8 seconds.
The final unused-simp-argument cleanup is checked again by the delivery compile.
Axiom checking is performed by the delivery preflight.

## No longer needed

No existing import, node, or module is pruned. Both original declared proof
dependencies are still used. No exceptional adjoint existence module is imported.
The ordinary associator lemma does not need derived descent; the item proves that
step directly from Mathlib's localization API (`lem-sfb-exact-derived-natural-iso`).
The unit record has no realized steps to replace, and the assigned route is kept.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependencies are definitions and the generic mate equivalence;
they do not state ordinary strict-system associator existence or inverse-square
composition. Those are the two substantive tensor-unit uniqueness steps in the
original prose plan, now separately stated. The remaining mate/localization and
projection calculations are implemented rather than moved into a new obligation.

The current blueprint defines integral/rational exceptional inverse images by
condensed Brown representability. This delivery preserves the assigned earlier
strict-system route and does not change any target or unit statement. Zheng's
Construction 4.1 supplies the system model, and Construction 5.15 supplies the
compact-support gluing pattern. The arbitrary-record lemmas here are explicit
interface-level elaborations of the supplied DAG proof, not direct quotations of
Zheng with his hypotheses dropped.

Edge cases checked in formulating the two lemmas: repeated index values, identity
coefficient maps, zero coefficient rings, and empty schemes. Scalar adjunction
uniqueness and localization apply in each case without flatness assumptions.
Equality is descended along Q, never deduced from derived evaluations.

## New nodes

`lem-pur-strict-etale-transport-associator` states ordinary associator existence on
one scheme. Its module is `Sheaf.Paper.StrictEtaleTransportAssociator`.

`lem-pur-strict-etale-inverse-transport-composition` states the coefficient cocycle
for one inverse-image square, with the composition records supplied. Its module is
`Sheaf.Paper.StrictEtaleInverseTransportComposition`.

Each node includes its exact Lean statement, source, natural-language proof, and
LeanSearch, LeanFinder and source-grep searches. No existing public interface or
source-library declaration changes, so no consumer adaptations are required.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
