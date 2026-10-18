## What changed

Proved the identity and composition laws of the explicit direct-sum restriction
in `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`, without changing any
existing signature, definition, visibility or import. A proved private helper
computes restriction on each direct-sum inclusion. Both proofs use direct-sum
extensionality and the restriction laws of the given module sheaf. The dependent
section indices are compared explicitly using the functor laws of A.

## Proved and sorry left

Closed 2 of the original 3 holes:
- `CategoryTheory.elementDirectSumMap_id`.
- `CategoryTheory.elementDirectSumMap_comp`.

Added 0 holes. Remaining original hole:
- `CategoryTheory.ringed_sheaf_slice_adjunction`, node
  `lem-weil-pbc-ringed-sheaf-slice-adjunction`.

The main theorem remains unchanged with its complete natural-language proof.
It still needs the arbitrary-sheaf fibre equivalence, localization geometric
morphism and induced module direct image, exact extension adjunction, and
relocalization. No new statement or arbitrary witness construction is introduced.

## No longer needed

None. No imports removed and no nodes or modules pruned. The original imports
still support the public constructions and remaining main theorem. The completed
functoriality proofs use only Mathlib and the module's existing definitions.

## Where the brief, the DAG or earlier work was wrong

The recorded general module-adjunction dependency uses CommRingCat, whereas
this module's existing theorem quantifies over RingCat. Its declaration therefore
does not apply directly at this interface. Mathlib's over-site API and the proved
source `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf` concern a site
object; they do not supply the equivalence for a slice over an arbitrary sheaf.
These are limitations for completing the remaining theorem, not reasons to
alter its hypotheses. The two direct-sum functoriality laws require neither
commutativity nor a representability hypothesis.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
