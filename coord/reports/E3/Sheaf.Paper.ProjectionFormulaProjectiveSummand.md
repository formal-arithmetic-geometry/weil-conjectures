## What changed

Filled `SheafOfModules.ringedProjectionFormula_projective_summand` without changing its
statement or `ringedProjectionFormulaSummandArrows`. The proof transports the supplied
splitting to the coefficient sheaf, uses the finite-free lemma at shift zero, and applies
naturality and functoriality to prove both inverse equations. Package independence is
reflexivity: the existing arrow construction uses the package only in proof fields.
The finite-free retract route and the blueprint unit's realized statements and steps stay.
Both modules compile through `lcompile.py`; the delivery compile and axiom probes also
passed. The first preflight found only a node-signature metadata mismatch, now corrected.

Added `Sheaf.Paper.ProjectionFormulaInverseNaturality`, with the proved public theorem
`SheafOfModules.ringedProjectionFormulaInverse_naturality`. Its private lemmas establish
ordinary tensor and chain-mate naturality, naturality of mixed representatives using one
common K-flat resolution, and naturality of the derived complex comparisons. The theorem
transports the inverse chain square through those comparisons. These are actual proofs;
no new assumption or unproved intermediate statement was introduced.

The item imports the new theorem privately. All existing public signatures, definitions,
and public imports are unchanged. Updated its DAG proof and dependencies and added the
node for the new naturality theorem. No consumer adaptation or definition repair is needed.

## Proved and sorry left

Closed the item's sole hole:
`SheafOfModules.ringedProjectionFormula_projective_summand`.

Also proved the new declaration
`SheafOfModules.ringedProjectionFormulaInverse_naturality`, node
`lem-weil-pbc-projection-inverse-coefficient-naturality`.

Original holes: 1. Closed: 1. Added: 0. Remaining in both delivered modules: 0.
Split-offs with `sorry`: 0. The proof uses existing declared dependencies, including the
finite-free lemma and the normalization/invertibility interfaces of the arrow module;
it does not claim those dependencies have themselves been discharged.

## No longer needed

Removed the item's direct private import
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback` and its direct proof-dependency edge to
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. That result remains needed in the new
naturality module, through the existing arrow interface, so this removes a redundant
import and edge, not a whole module from the targets' closure.

Kept `Sheaf.Paper.ProjectionFormulaFiniteFree` and
`lemma-weil-pbc-projection-formula-finite-free`: the proof really uses the free case.
No whole modules or other planned dependency nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement, changed target, or mathematical error was found. The DAG describes
forward naturality and a retract formula for the reverse arrow. The current Lean reverse
arrow is defined instead by the transported finite-total chain inverse, so its coefficient
naturality needed an explicit proof before the retract calculation could use it. The new
proved lemma supplies that interface. The presentation-independence clause is already
definitional for this construction; it needs no separate uniqueness lemma.

The new naturality proof uses the existing generic K-flat resolution theorem as a tool,
`CochainComplex.exists_isKFlatResolutionGeneral`, whose mathematical node is
`lem-pc-kflat-resolution`. It only supplies a common resolution for a naturality check;
no protected unit statement or proof step is bypassed.

## New nodes

`lem-weil-pbc-projection-inverse-coefficient-naturality`, in
`dag/nodes/sec-proper-base-change/`, records the proved coefficient naturality of the
specified reverse projection arrow. The source is the naturality/retract calculation
in the projection-formula summand proof, with the specified arrow construction from
its preceding definition. Its Lean module is
`lean/Sheaf/Paper/ProjectionFormulaInverseNaturality.lean`. The proof is complete,
including zero maps, zero coefficients, and independently chosen packages. It leaves
nothing for another worker. No change record is required because no existing statement,
definition, or public import was changed.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
