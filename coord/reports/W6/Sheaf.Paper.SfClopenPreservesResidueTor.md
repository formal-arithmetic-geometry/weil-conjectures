## What changed

Proved `WeilConjectures.sf_clopen_preserves_residue_tor` with its original signature.
The proof first uses the exponent-one scalar comparison, identifies the two slice
sites through `Scheme.ProEt.sliceEquiv`, and realizes the induced module restriction
as an additive tensor equivalence. It transports every degree-zero test module and
its vanishing homology through that equivalence, then compares the two composites
of exact restriction functors on derived categories. A private finite-level lemma
separates this argument from scalar reduction. The ordinary restriction square is
proved for abstract ring sheaves and then specialized, avoiding expansion of the
concrete coefficient constructions.

Added `Sheaf.Algebra.Homology.RingedEquivalenceDerivedTensorComparison`, proving
`SheafOfModules.ringedEquivalence_derivedTensorComparison`. Its private helper proves
that the termwise image of a K-flat complex under an additive tensor equivalence is
K-flat. The public comparison follows by choosing a K-flat representative and using
the existing K-flat single-tensor comparison on both sides. No full derived monoidal
coherence assertion is needed. Both sites and the derived categories retain their
independent universes.

The item's new proof imports are private. Transparency-aware elaboration is enabled;
named continuity and exactness evidence avoids repeated instance searches. The scalar
functors are locally irreducible in this proof and used through their named comparison,
so no shared definition or exported reducibility attribute changes. Its existing public import and all existing
signatures are unchanged. The item's node now records the actual argument. No shared
definition, other existing module, source-library declaration or target was changed.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.sf_clopen_preserves_residue_tor`
(node `lem-sf-clopen-preserves-residue-tor`).

Also proved the new theorem
`SheafOfModules.ringedEquivalence_derivedTensorComparison`
(node `lem-sf-ringed-equivalence-derived-tensor-comparison`).

Holes closed: 1 of 1. Holes added: 0. Split-off unproved statements: 0.
No `sorry` remains in either delivered Lean module. The existing scalar-comparison
statement is used as an available dependency; its proof is outside this delivery.

## No longer needed

Removed `lem-pur-finite-product-derived-tensor-calculus` from this item's planned
proof dependencies. The slice-equivalence proof requires no finite-product tensor
calculation, so its module is not imported. This does not assert that the module is
unused by other targets or authorize its withdrawal.

`lem-weil-pbc-site-derived-tensor-descent` is used through the new generic comparison,
not as a separate step of the main theorem. No existing imports were removed from
the original module, which originally had only its statement import. No modules
are withdrawn and no other planned dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The statement and its relocalization plan are correct. The finite-product dependency
was unnecessary. The general tensor comparison can be proved from the already
available K-flat resolution and single-tensor comparison, without leaving a further
hole or restating the assigned obligation.

Small cases checked in the argument: the zero complex, zero coefficient ring and
empty site require no additional assumption. For a>b the ordered-interval conjunct
is inherited from the premise. Degree-zero test modules need not be flat: only the
chosen representative of the derived object is required to be K-flat.

The generic K-flat resolution and single-tensor nodes are used as tools from their
units, solely to establish the equivalence comparison. The clopen scalar comparison,
slice-site argument and the item's original unit route are retained.

## New nodes

`lem-sf-ringed-equivalence-derived-tensor-comparison` states the objectwise derived
tensor comparison against a module in degree zero for an additive ordinary-tensor
equivalence. It is completely proved in its new module. Its node records the signed
total-complex comparison, the inverse-equivalence proof of K-flat preservation, and
the K-flat representative calculation, with sources and actual Mathlib searches.
It introduces no pending proof obligation. There are no change records because no
existing statement or definition changed.

Validation: `lcompile.py --all` completed with exit code 0, no warnings and no holes.
The item compiled in 30.5 seconds; the new comparison module had previously compiled
from source in 25.8 seconds and was reused in the final clean run.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
