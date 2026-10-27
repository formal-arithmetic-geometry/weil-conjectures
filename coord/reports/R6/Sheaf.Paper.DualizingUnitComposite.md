## What changed

Prove the three theorems of `Sheaf.Paper.DualizingUnitComposite`, preserving every
existing public signature and definition. Proved private helpers establish
unit normalization and naturality from the source library's projection unitality
and adjunction tensor naturality. The inverse clause follows by explicit
cancellation, for the arbitrary given trivialization. The source clause applies
the given normalization to the existing Dctf model of the dualizing object.
Each open-restriction equation follows by applying its functor to the equation.

The proof adds the private import
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit` and removes the
three unused private imports listed below. The node's proof and dependencies now
record this direct calculation. No adopted source file, target, public definition,
public import, or mathematical hypothesis changes. Preflight requires a record for the
private helper section commands; see
`coord/changes/R6-dualizing-unit-private-proof-context.md`. The downstream check finds
zero Lean importers and no consumer adaptation is required.

## Proved and sorry left

Closed all three original holes, owned by `lem-pur-dualizing-unit-composite`:

- `WeilConjectures.PurityFiniteSetting.dualizingTensor_unit`.
- `WeilConjectures.PurityFiniteSetting.dualizingComposite_inverse`.
- `WeilConjectures.PurityFiniteSetting.dualizingComposite_sourceCancellation`.

Holes added: zero. Sorries left in the delivered module: zero. No decomposition
or new assumption is used. The proofs still use the existing library's operation
and preservation interfaces; this is not a claim that their entire dependency
closure is free of sorry.

## No longer needed

Removed private imports:

- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.SixFunctors.OpenTensorNormalization`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.

The concrete upstream finite-module projection already provides the invertible
components and its unit equation. Accordingly this proof needs no separate
ringed projection-mate exactness, normalized-open projection, or compared finite
compact-projection theorem.

Removed the obsolete `tool_uses` approvals for
`lem-weil-pbc-ringed-projection-mate-exact`, `lem-sf-open-tensor-normalization`,
`lem-weil-finite-compact-projection-formula`, and `thm-sf-comp-composition`.
The first three correspond to the removed imports; the fourth is replaced here
by the already-specified finite exceptional compositor.

Removed proof-only node dependencies:

- `lem-pur-compact-transpose-unit-naturality`: its required concrete unit and
  naturality formulas are proved here from existing source-library results.
- `lem-pur-unital-tensor-transport-cancellation`: the specific cancellations and
  functorial transport are written directly; the W-first transpose already
  incorporates the symmetry.
- `lem-sf-ringed-derived-closed-symmetric-monoidal`: no separate ringed closed
  structure is needed for the existing etale tensor and unitor interfaces.
- `thm-sf-comp-composition`: the actual isomorphism used here is already supplied
  by the statement dependency `def-pur-finite-exceptional-composition`.

These are dependencies removed from this item's proof, not requests to withdraw
nodes or source declarations still used by other items. No unit statement or unit
proof step is bypassed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The current DAG's two newly planned abstract/unit-naturality dependencies have no
Lean attachment in this checkout. They are unnecessary for this proof: the
source library already supplies `projectionMap_rightUnitality` and
`Adjunction.projectionTensorMap_naturality_right`. Search found no one-line
Mathlib theorem proving the complete geometric statement. The sandbox initially
contained an unfinished attempt; its calculations have been completed and
checked against the unchanged canonical map definitions.

The named sigma already uses W-first coordinates. No extra braiding should be
inserted. The rho normalization is applied only to the stated Dctf object. Its
proof of membership comes from the existing exceptional-preservation result.
All arbitrary trivializations and all stated open restrictions are retained.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
