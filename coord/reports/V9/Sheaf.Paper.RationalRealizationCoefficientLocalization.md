## What changed

Proved `AlgebraicGeometry.Scheme.rationalRealizationCoefficientLocalization` in
`Sheaf.Paper.RationalRealizationCoefficientLocalization`, with its full signature unchanged.
The proof compares integral constant sections using every normalized finite reduction and
injectivity of the existing profinite residue-limit equivalence. It then constructs the
sectionwise localization isomorphism, proves its naturality on integral generators, sheafifies
it, and composes with the realization's specified continuous localization isomorphism.
The two existing pointwise normalizations prove the unit equation. Localization uniqueness
on integral generators proves the constant-fraction equation; applying the inverse gives
exactly the stated inverse formula.

All helper assertions are proved local assertions inside this theorem. Added proof-only access
to the existing finite-constant normalization helper and the proved profinite-tower theorem.
Updated the item's proof steps and dependency list to describe the actual argument.
No other existing module, public declaration, definition, instance or statement changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.rationalRealizationCoefficientLocalization`
(node `lem-per-rational-realization-coefficient-localization`).
No holes remain in the item and no holes or split-off obligations were added.
The complete file compiled cleanly through `lcompile.py` in 23.1 seconds.
The signature was compared with the shared source and is unchanged.

## No longer needed

The separate theorem `continuousCoefficientCompletion`
(node `lem-weil-pbc-continuous-coefficient-completion`) is not needed: the given realization's
finite and integral normalizations already provide all residue comparisons. The proof uses
`lem-sfb-integers-profinite-tower` directly for joint injectivity of reductions.
The separate theorem `continuousCoefficientLocalization`
(node `lem-weil-pbc-continuous-coefficient-localization`) is not needed: the given realization
already carries its normalized localization isomorphism. Its module remains needed elsewhere;
this delivery withdraws neither declaration nor module.
The derived-localization theorem in
`Sheaf.Paper.RationalContinuousCoefficientDerivedLocalization` is not used, but that public
import stays because the statement uses its canonical localized coefficient map.
Removed the unused proof import `Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion`
from the sandbox draft. No modules are withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's first step suggested obtaining joint monicity from another completed-ring comparison.
The normalized residues of the supplied realization and the existing residue-limit ring
equivalence suffice directly. The second step needs no new continuous localization theorem,
since its normalized isomorphism is a field of the realization. The argument works on empty
test objects by pointwise extensionality and never assumes global bounded denominators.
The canonical ring structures must be specified explicitly when localizing sections:
sectionsSubring uses the RingCat forgetful presentation while the presheaf is in CommRingCat.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalRealizationCoefficientLocalization": "fa1f767ca3bd561d790347fe360ce854a6e1d0ad"}, "results": {"Sheaf.Paper.RationalRealizationOrdinaryLocalization": {"hash": "dba83abb4a24dd05a130a6b89158b533ce26fa62", "status": "OK"}}, "seconds": 65, "time": "2026-10-28T15:59:33+0800", "transitive": 0, "version": 1}
```

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
