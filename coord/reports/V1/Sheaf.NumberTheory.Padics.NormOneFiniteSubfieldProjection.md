## What changed

Completed `Padic.exists_normOne_finiteSubfield_projection` in
`Sheaf.NumberTheory.Padics.NormOneFiniteSubfieldProjection`, with its statement unchanged.
The proof imports the two existing declared inputs
`Sheaf.Analysis.Normed.Module.AdmissibleScalarBalls` and
`Sheaf.Analysis.Normed.Module.ContractiveExtensionFromAdmissibleValues` privately.
It supplies a local `NormedSpace F Ω` directly from norm multiplicativity, obtains
properness of F using `FiniteDimensional.proper`, and applies these inputs to the
inverse of the isometric inclusion of F onto its linear range. The resulting
contractive extension fixes F and is bundled using `LinearMap.mkContinuous`.
No completeness of Ω is introduced. All existing public imports are preserved.

Updated the item's node proof and declaration docstring to describe the actual
four-step assembly. The unit route and all theorem signatures remain unchanged.
No other existing module or node is changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`Padic.exists_normOne_finiteSubfield_projection`
(node `lem-sfb-norm-one-finite-subfield-projection`).
Added 0 holes, split off 0 statements, and left 0 holes in the delivered module.

The proof uses existing, separately assigned theorems
`LinearMap.exists_admissible_scalar_of_isCompact_closedBall` and
`LinearMap.exists_contractive_extension_of_admissible_values`, whose proofs are
still `sorry` in the shared source inspected for this delivery. They are the
stated DAG dependencies, and this delivery adds no holes to their modules.

## No longer needed

Removed the direct private imports `Mathlib.Topology.Compactness.Compact` and
`Mathlib.Order.Zorn`. Compactness is available through the actual inputs and
finite-dimensional properness; Zorn is internal to the existing conditional
extension theorem, so this module need not import it directly.

Removed `lem-weil-l-adic-extension-absolute-value` from the item's proof dependencies.
There is no need to compare two separately constructed absolute values: the norm
on F is inherited from Ω, and the inclusion is isometric by construction. This
removes only this proof edge; it makes no claim that the node or its module is
globally unused. No Sheaf or WeilConjectures module is withdrawn. All other
original proof dependencies are used.

## Where the brief, the DAG or earlier work was wrong

The original module docstring described the older direct seven-step compact-ball
and Zorn argument, while the current DAG already exposes the two reusable
analytic inputs. The delivery synchronizes the docstring with that assembly.
The restriction-norm uniqueness step is unnecessary for the inherited norm.
Neither observation changes the mathematical statement or the unit route.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
