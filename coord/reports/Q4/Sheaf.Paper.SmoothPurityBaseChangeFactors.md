## What changed

The item module now proves `AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.finite_factors`
from a separate finite orientation lemma. Its statement, all existing public imports, all
public definitions, and the entire tower section retain their original signatures and bodies.
No other existing Lean module is changed.

The proved private helper `tensor_base_change` reuses the already proved private
`Etale.CanonicalSmoothBaseChange.dualizing_tensor_base_change` via a proof-only `import all`
of `Sheaf.Paper.CohomologicalSmoothnessTheorem`. The corresponding proof-only import of
`Sheaf.AlgebraicGeometry.SmoothTensorDuality` supplies `smoothTensorDualityMap_eq`.
Monoidality of pullback preserves braiding; its two naturality equations and the tensor
interchange equation put the resulting factors into the order required by the item.
This tensor equation holds for every ordinary coefficient complex, so its proof does not
need the item's additional `IsCtf` hypothesis.

The proved private helper `gamma_base_change` expands the existing gamma definition and
composes the orientation and tensor equations. Naturality of the monoidal pullback
comparison and of the tensor square comparison, followed by functoriality of tensor,
identifies the source comparison with the specified `ordinaryFiniteTwistedPullbackComparison`.
The item then applies the comparison functor to all three ordinary equations.

The new module `Sheaf.Paper.FiniteSmoothOrientationBaseChange` isolates precisely the
orientation subargument from blueprint factors proof (1). It keeps all the item's geometric,
coefficient, and diagonal normalization hypotheses and the actual canonical unit exchange
and Kummer-normalized line comparison. It asserts neither a tensor equation nor a gamma
equation. Its ordinary-etale formulation allows the proved gamma assembly to compose it
before applying site comparison. Its docstring includes the full diagonal cube, DNC,
normalization uniqueness, coefficient transport and inverse-equation argument.

The item DAG now records this finite route and retains the previous full plan explicitly
for the untouched tower theorem. No target statement or adopted source-library file changed.

Validation: both private calculations compiled separately through `lcompile.py`; the new
orientation module compiled in 5.2 seconds. The complete delivery set also compiled without errors or warnings. The tool accepted
both files under its per-file acceptance check; its displayed totals include setup and
cache waits. The delivered files contain no temporary profiler options. No local Lake or Lean process was used.

## Proved and sorry left

Closed the body of `AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.finite_factors`
(node `det-sp-purity-bc-factors`). Its tensor factor is proved from existing declarations,
and its gamma factor is proved by composing tensor compatibility with orientation
compatibility. The two new private helpers have complete proofs and no holes.

Added one hole:
`AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.finite_orientation_base_change`
in `Sheaf.Paper.FiniteSmoothOrientationBaseChange`, node
`lem-sp-finite-normalized-orientation-base-change`.

Retained one original hole:
`AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.tower_factors`, node
`det-sp-purity-bc-factors`. Its statement and complete proof-in-words docstring are unchanged.

Thus one of the item's two original sorry bodies is replaced by a proof, with one strict
orientation subargument split off. This is a decomposition, not a net hole closure:
one hole closed, one added, and two holes remain across the delivered Lean files.
There are no new holes in definitions or private declarations.

## No longer needed

Removed these unused proof-only imports from the item:

- `Sheaf.Paper.DiagonalExchangeCube`
- `Sheaf.Paper.SectionDncIntegrationSquare`
- `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport`
- `Sheaf.Paper.ProEtaleCtfPullbackDomains`
- `Sheaf.Paper.SmoothPurityCompactProjectionBaseChange`
- `Sheaf.CategoryTheory.Adjunction.TensorCounitExchangeCalculus`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The finite tensor proof no longer needs to instantiate the abstract restricted-domain,
compact-projection or tensor-counit calculus statements: the existing cohomological
smoothness file already proves the ordinary tensor calculation for exactly these maps.
The finite gamma assembly uses ordinary monoidal comparison naturality directly.
The new orientation lemma's plan still needs the diagonal cube, section DNC square and
coefficient transport. The retained tower plan still cites the original dependencies.
The new orientation module also omits the unused
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions` import: its statement uses
only the already imported Mathlib pullback conventions.
Consequently no entire dependency node or module is asserted globally unnecessary,
no module is withdrawn, and no declaration in the adopted source tree is removed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The existing proof plan did not mention the proved private
finite tensor base-change calculation in `CohomologicalSmoothnessTheorem`; reusing it is
shorter than repeating that calculation through the abstract domain calculus.

The module has a rework/quarantine entry, but its current live source exists. This delivery
starts from that live source, preserves its Lean attachment and tower definitions, and
neither deletes nor empties a quarantined path.

Edge cases of the split orientation statement were checked in words: identity base
change, relative dimension zero, empty schemes and the zero coefficient ring all use the
same unit or zero-category equations. No flatness of the coefficient map or base change
is introduced. In the Lean assembly, the symmetry calculation needs only the displayed
finite projection-formula instances, and the gamma calculation treats the line comparison
as an arbitrary isomorphism satisfying the orientation equation; no faithfulness or
invertibility of site comparison is assumed there.

## New nodes

`lem-sp-finite-normalized-orientation-base-change` in
`dag/nodes/sec-smooth-purity/lem-sp-finite-normalized-orientation-base-change.json`
realizes the finite coefficient orientation portion of blueprint `det-sp-purity-bc-factors`,
proof (1), in `Sheaf.Paper.FiniteSmoothOrientationBaseChange`. Its statement omits all
tensor-mate and gamma conclusions of the item, so the new hole is a strict subargument.
LeanSearch, LeanFinder/Loogle and Mathlib grep found no matching normalized orientation
result. Its statement dependencies, numbered proof, proof dependencies, source and exact
Lean signature are recorded. No change record is needed because no existing statement,
definition or public import changed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
