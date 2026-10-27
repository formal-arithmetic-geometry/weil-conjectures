## What changed

Proved `AlgebraicGeometry.Scheme.finiteTate_local_root_tensors_hom_ext` without changing
its signature. The proof transposes the maps through the comparison adjunction, lifts
all roots on a finite intersection of covering image sieves, applies the hypothesis,
and uses separatedness. The finite-root comparison identifies the underlying units.

Added `Sheaf.Paper.FiniteTateEtalePowerGeneration` with the proved local-span theorem
`AlgebraicGeometry.Scheme.finiteTateEtalePowerGenerator_locally_span`. Its private
presheaf constructions and tensor induction establish generation before sheafification;
the comparison map is locally surjective. This makes the tensor-generation step
explicit, including degree zero. Only proof imports were added to the assigned module.
The original node now records the actual local-span dependency and argument.
Both modules compiled together with `lcompile.py --all`; the delivery checks compile
the final files and check the declaration/axiom and DAG constraints again.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finiteTate_local_root_tensors_hom_ext`
(node `lem-pur-finite-tate-local-root-tensors-ext`).

Added 0 holes; split off 0 unfinished statements. The new theorem
`AlgebraicGeometry.Scheme.finiteTateEtalePowerGenerator_locally_span`
(node `lem-pur-finite-tate-etale-power-generation`) is proved. No `sorry` remains in
either delivered Lean module. Existing finite-root comparison and root-tower declarations
are used as the stage-3 dependencies; their proofs are outside this item.

## No longer needed

None. No original imports, modules, declarations or unit steps are withdrawn.
`def-pur-sheaf-tensor-product` remains needed through the local-generation argument;
its direct proof-dependency edge is replaced by the new generation node. The other
original proof dependencies, finite-root site comparison and root-tower finite tensor,
remain used.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid. The sectionwise generators do not span arbitrary global
sections after sheafification; local span is the precise statement needed. The proof
supplies this local-generation bridge rather than assuming global generation.
The tensor exponent zero, empty root tuple, empty scheme and zero coefficient ring
are covered without additional hypotheses. No definition or existing statement changed.

## New nodes

`lem-pur-finite-tate-etale-power-generation` records local span by the ordered pure
root tensors. It is a strictly smaller generation result, independent of the pro-etale
site, root lifts, prime, coefficient field and map-extensionality conclusion. The
statement and its proof follow Stacks Tags 03EK and 00WK. Its new module is proved
in this delivery, so it adds no unfinished obligation. No change record is needed:
there is no change to an existing definition, statement or public interface.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
