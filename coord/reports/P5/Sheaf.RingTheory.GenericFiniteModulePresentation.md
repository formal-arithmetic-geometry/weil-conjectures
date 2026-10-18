## What changed
Added `Sheaf.RingTheory.LocalizedFinitePresentationData`, splitting out the finite exact localized free presentation produced by the polynomial-presentation and generic-freeness argument. The item theorem now imports that module and proves finite presentation from the exact sequence: the relation map has finitely generated range because its source is finite, and exactness identifies that range with the kernel. Removed the proof-only generic-freeness import from the item module because the final extraction uses only the new data lemma and Mathlib.

## Proved and sorry left
Proved `Module.Finite.exists_finitePresentation_localizedModule_powers` in the item module. The new intermediate theorem `Module.Finite.exists_localized_finite_presentation_data` remains `sorry`, with node `lem-pur-generic-finite-module-presentation-data`; it is the polynomial-presentation/generic-freeness construction and is strictly stronger concrete data than the extracted finite-presentation proposition.

## No longer needed
Removed the proof-only import `Sheaf.RingTheory.FinitelyPresentedAlgebraModuleGenericFreeness` from `GenericFiniteModulePresentation.lean`; its declarations are used only in the proof of the new intermediate node, not by the completed extraction. The original node dependencies for generic freeness, Noetherianity, and finite submodules are therefore no longer direct dependencies of the item proof.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt treated the full polynomial presentation, denominator clearing, torsion-kernel cancellation, and quotient descent as one indivisible Lean proof. The concrete exact-sequence interface makes the final finite-presentation extraction short and checkable; the construction itself is isolated as a named intermediate node for follow-up proof work.

## New nodes
`lem-pur-generic-finite-module-presentation-data` — `Module.Finite.exists_localized_finite_presentation_data` in `lean/Sheaf/RingTheory/LocalizedFinitePresentationData.lean`; this is the finite exact sequence produced by the Stacks Tag 051T construction.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
