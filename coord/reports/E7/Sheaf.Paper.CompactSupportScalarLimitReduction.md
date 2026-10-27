## What changed

Proved `scalarRoosTensorProducts` using an integral basis. Restricted scalar
extension is naturally a finite power, which preserves countable products.
Restriction is a right adjoint and reflects isomorphisms, hence reflects these
limits; scalar extension therefore preserves them. Its induced functor on
cochain complexes preserves the same products, so the canonical product
comparison is invertible.

The new helper is private and proved. Public statements, definitions and public
imports are unchanged. The DAG records the existing lemmas used by the proof.
No new modules or split statements were added. The pre-existing arithmetic-index
initiality argument was moved into a private order-theoretic lemma. The scheme
namespace is opened with its conflicting `Modules` name hidden, avoiding repeated
failed resolution against scheme modules. These elaboration changes preserve all
public signatures and definitions.

Validation: the delivered version compiled successfully in 50.7 seconds through
`lcompile.py`. All added proof imports passed the import-direction cycle check.

## Proved and sorry left

Closed one of eight original holes:

- `WeilConjectures.PurStrictScalar.scalarRoosTensorProducts`

Added zero holes. Seven original holes remain unchanged:

- `WeilConjectures.PurStrictScalar.scalarLimitTensor_exact`
- `WeilConjectures.PurStrictScalar.scalarCompletion_existsUnique`
- `WeilConjectures.PurStrictScalar.scalarLimitRestriction_exact`
- `WeilConjectures.PurStrictScalar.scalarRoosComparison_existsUnique`
- `WeilConjectures.PurStrictScalar.scalarRoosNormalization`
- `WeilConjectures.PurStrictScalar.scalarRoosTensorNormalization`
- `WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`

## No longer needed

None. The completed argument implements the recorded finite-basis route.
All other dependencies remain needed by the seven unfinished declarations;
no module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. A proof of `scalarRoosComparison_existsUnique`
from `strictRoosDerivation` and the uniqueness of right-derived functors was
also developed and typechecked, but the resulting file repeatedly exceeded the
60-second compile limit. Local equation lemmas and reduced proof imports did
not bring that version under the limit. It is not included in this partial
delivery; its original hole is preserved. A continuation can use the universal
Roos derived unit, transport the canonical limit-complex derived unit along
`strictTowerLimitIso`, and apply `Functor.rightDerivedUnique`; localization full
faithfulness and `rightDerived_ext` give uniqueness.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
