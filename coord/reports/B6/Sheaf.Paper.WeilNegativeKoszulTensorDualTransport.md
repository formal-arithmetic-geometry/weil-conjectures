## What changed

Reduced `AlgebraicGeometry.Scheme.negativeKoszulTensorDualTransport` through the existing,
explicit `CategoryTheory.ringedNegativeKoszul` complex. The theorem's signature and its
public imports are unchanged. Its two new proof imports supply coefficient realization
and duality on one ringed site. The assembly composes their chain isomorphisms and proves
both the transition square and the degree-zero unit equation by associativity and the
component formula for composition.

Added `Sheaf.CategoryTheory.RingedNegativeKoszulTransitions`: the negative-factor map is
explicitly multiplication by b in degree -1 and identity in degree zero. Its chain equation
is proved, and the transition on several factors is the recursive tensor of these maps.
No transition or other data is chosen from an existence theorem. The module also proves
the empty-tensor duality, with its transition and unit equations, by inverse Hom-unit
evaluation. The private assembly helper handles zero factors by that proved theorem and
nonzero factors by the remaining site-duality statement.

The intermediate complex is an existing construction in
`Sheaf.CategoryTheory.SignedKoszulCompletionModel`; none of that module's completion-model
existence assertions or finite-coordinate existence statements is used. This is reuse of
a definition, not a change of the blueprint unit route.

## Proved and sorry left

Closed the one existing textual hole:
`AlgebraicGeometry.Scheme.negativeKoszulTensorDualTransport`
(node `lem-weil-pbc-negative-koszul-tensor-dual-transport`). This is a decomposition,
not a sorry-free proof of the mathematical result: two smaller holes were added, so the
net hole change of this delivery is -1 closed-minus-added.

New holes, each exactly `:= by sorry` in its own new module:

- `AlgebraicGeometry.Scheme.negativeKoszulTensorRealization`
  (`lem-weil-pbc-negative-koszul-tensor-realization`): coefficient/site realization to the
  negative two-term tensor, including transitions and the empty-subset basis unit.
  It has no positive Koszul complex or internal Hom.
- `CategoryTheory.ringedNegativeKoszulSuccDuality`
  (`lem-weil-pbc-ringed-negative-koszul-duality`): duality for nonempty ordered tensors
  on a single ringed site, including transitions and units. It has no exterior algebra,
  scheme, adic datum, coefficient functor or scalar extension. The empty-list case is proved.

Also proved `CategoryTheory.ringedNegativeKoszulFactorTransitionF_comm` and
`CategoryTheory.ringedNegativeKoszulZeroDuality`. There is no hole in any definition.

## No longer needed

No existing public import is removed, and no module or declaration is withdrawn.
The main node's direct proof dependencies on the exterior basis and the coefficient,
negative algebraic tensor, and positive system definitions are replaced by the two
specific comparison statements and the explicit transition/base-case API. These
mathematical ingredients remain needed below the new nodes; they are not claimed as
pruned. In particular, the exterior-basis leaf remains in the realization node.

The searches also inspected `SignedKoszulFiniteCoordinates`,
`RingedKoszulFiniteEvaluation`, `HomComplexToSingle`, `HomTensorTotal`,
`WeilCompletedTensorTransport` and `WeilCompletedModuleTensorTransport`. None of their
comparison statements is imported: their conclusions do not give the required two
normalized comparisons without additional work. No target, unit, or source-library
statement is removed or changed.

## Where the brief, the DAG or earlier work was wrong

There is no disputed statement or assigned return to repair. The original proof plan
combined two distinct missing comparisons: realization of exterior rank-one factors and
finite free internal duality. The listed dependencies provide constructions and exterior
bases; they do not already state either comparison. The reduction now makes that boundary
concrete, using the already existing negative two-term tensor as the shared intermediate.
It does not move the original theorem under another name.

Checked the signs in one and two factors. An integer parity check for every subset
in ranks zero through five also passed. For one factor the Hom sign in degree -1 is
+1. For two selected factors the negative-to-positive-dual basis sign is -1; in general
it is (-1)^(k(k-1)/2) for k selected indices. Removing one selected index changes it by
(-1)^(k-1), precisely compensating for the Hom differential sign. Transitions are diagonal
products of the b_i and commute with these signs. The empty-subset sign is +1. The
zero-factor case is proved directly; the statements require no scalar inverses, so zero
and unit scalars, repeated scalars, the zero ring, and the empty site are included.

## New nodes

`def-weil-pbc-ringed-negative-koszul-transitions` records the explicit transitions on the
existing negative model, their proved chain equation, and the proved empty-tensor duality.
Its new module has no sorry.

`lem-weil-pbc-negative-koszul-tensor-realization` isolates the rank-one exterior basis,
coefficient realization and finite tensor comparison. Its full proof in words specifies
the basis, scalar, transition and unit normalizations.

`lem-weil-pbc-ringed-negative-koszul-duality` isolates the nonempty finite free tensor duality
on one site. Its full proof in words specifies the dual-basis signs, transitions and unit.
The item node's proof and proof-dependency list now match the composition in Lean.
No change record is needed: no existing statement, definition or interface is changed.

All four delivered Lean modules were checked with lcompile.py. The supporting modules
compiled cleanly in 8.0, 4.5 and 8.8 seconds; the final item compiled cleanly in 6.2 seconds.
Static checks also confirmed the unchanged original signature, verbatim Lean statements
in node records, existing DAG dependencies, module headers and the 100-character limit.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
