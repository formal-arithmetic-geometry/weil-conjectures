## What changed

Completed `AlgebraicGeometry.Scheme.adicReduction_cocycle` in its existing module,
without changing its statement or any shared definition. All added helpers are private
and proved. The proof first establishes ordinary tensor coherence by three tensor
adjunctions and the normalized insertion-of-one formula, lifts it degreewise, and uses
an abstract pasting calculation plus K-flat resolving extensionality for derived coherence.
It then specializes to the quotient maps, including repeated indices.

The two `import all` proof imports expose the existing normalization and resolving
APIs. The item's DAG proof and dependency list now record this argument.
The complete file passed `lcompile.py` in 12.4 seconds before removing profiling options.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.adicReduction_cocycle`
(node `lem-sfb-adic-reduction-cocycle`).

No holes added, no split-off statements, and no `sorry` remains in the delivered module.
The proof uses the existing library declarations for K-flat resolutions, change of rings,
and normalized derived comparisons; their underlying dependencies are unchanged.

## No longer needed

The unproved `Sheaf.Paper.AdicExtensionCompCocycle` and its node
`lem-sfb-adic-extension-comp-cocycle` are not used. That proof import was present at
session start and was removed from the shared source during the session. This delivery
proves the needed general coherence privately instead. No existing declaration is removed
or replaced by a hole. None of the original K-flat proof dependencies is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier report left the assigned hole open after introducing an unproved, more
general cocycle. This delivery supplies the ordinary tensor argument and the derived
pasting argument, rather than introducing another coherence assumption.

Direct conversion through concrete comparison projections caused deterministic kernel
timeouts. The proof uses a local ordinary comparison defined by equality transport and
abstract congruence lemmas for transporting comparison isomorphisms and their components.
The generic cocycle is first packaged as an equality of whole natural isomorphisms.
Only an abstract category lemma extracts its components after specialization. This avoids
expanding chosen isomorphisms while comparing equal but differently written universe
expressions. These changes preserve all constructions. No mathematical statement or
unit route changes.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
