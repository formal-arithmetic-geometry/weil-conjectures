## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_adjunctions`
from the existing preservation and ambient-adjunction declarations. Two private,
proved categorical helpers construct full-subcategory restrictions and verify the
exact ambient Hom-equivalence equation using Mathlib's restriction formula.

The pullback clause uses direct-image stability. The tensor clause uses tensor
stability and internal-Hom stability after the stated braiding transport. The
exceptional clause first restricts the adjunction at the canonical compactification
used by direct-image stability. Compactification coherence then transports its
ambient adjunction to each boundary compactification, retaining the same right
adjoint and restricted functors.

Added the proof imports `Sheaf.Paper.CompactificationCoherenceCocycle` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`. Updated the item's proof,
proof dependencies and proof origin to describe this transport. Existing public
declarations, signatures, definitions, docstrings and public imports are unchanged.
No additional module is changed and no new node is introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_adjunctions`
(node `det-thm-sf-ctf-stability-adjunctions`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the item
module. The private helpers are proved. Existing imported preservation and
coherence theorems remain separate proof obligations, as intended by stage 3.
This delivery proves the item from those existing declarations.

Validation: `lcompile.py` compiled the complete delivered module with exit code 0
in 36.4 seconds, without errors or warnings. The initial required delivery dry
run timed out at 60 seconds; the subsequent single-file compile succeeded. The
previous attempts' missing `DerivedCategory.braidedCategory'` dependency error no
longer occurs. The required `deliver3.py --no-push` then returned OK: the complete module
compiled and passed server preflight, including its axiom probe. Review class:
CODEX, because the proof route is updated in the node file.

## No longer needed

None. Every original proof dependency is used; no original import was removed.
No node or module is made unnecessary by this proof. Both additional imports
supply declarations used by the exceptional clause.

## Where the brief, the DAG or earlier work was wrong

The direct-image stability declaration fixes the canonical compactification,
whereas this item's exceptional clause quantifies over every boundary
compactification. The original plan omitted that interface distinction. The
existing theorem `compactification_coherence_cocycle` supplies the natural
comparison on the source localizing closure. Lifting it to the target localizing
closure and transporting the adjunction resolves the distinction without
changing either statement.

Retained and checked the earlier attempt's work against current sources. Searches
recorded in `searches.jsonl` used LeanFinder for full-subcategory restriction,
Loogle for `CategoryTheory.Adjunction.restrictFullyFaithful`, launcher grep and
local `rg`. Mathlib supplies both the restriction and its Hom formula; the library
supplies all geometric input. The source blueprint's adjunction proof paragraph,
the unit statement, the dependency nodes and the dependency signatures were read.
The unit's route is preserved. No new mathematical claim is postulated.

The categorical helpers apply to arbitrary full subcategories, including empty
ones. The proof imposes no extra nonemptiness, coefficient or compactification
hypotheses; zero objects and empty schemes are covered by the existing
preservation declarations and fully faithful inclusions. Adjunction transport
uses only the comparison isomorphism, without choosing data from an unproved
mere existence theorem in any definition.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
