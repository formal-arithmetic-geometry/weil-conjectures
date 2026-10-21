## What changed

Replaced the proof of `CategoryTheory.Mod.extensionIso_quotient_formula` in
`Sheaf.CategoryTheory.ExtensionIsoQuotientFormula`. Its signature and public imports are
unchanged. The proof uses the specified upstream comparison, not a newly chosen isomorphism:
Mathlib's `Adjunction.homEquiv_leftAdjointUniq_hom_app` gives its normalization at the
extension unit. The restriction equivalence has identity underlying counit, so this
normalization identifies unit insertion with the inverse component. The existing
`whiskerLeft_extendUnitHom_smul'` calculation and linearity give the quotient formula.
The coequalizer projection is epic, giving uniqueness; module isomorphism identities and
naturality give all remaining clauses.

Updated the node's proof, proof dependencies and proof origin to describe this argument.
No definitions, statements, source-library modules, or consumers were changed.

Validation: `lcompile.py` compiled the final module without errors or warnings in 6.4 seconds.
The theorem signature was compared textually with the original and is unchanged; every
Lean line is at most 100 characters.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.Mod.extensionIso_quotient_formula`
(node `lem-sfb-extension-iso-quotient-formula`). No holes added or split off; no `sorry`
remains in the delivered Lean module. All nine clauses, including both naturality
equations, are proved.

## No longer needed

Removed redundant private imports of `Mathlib.CategoryTheory.Adjunction.Basic`,
`Mathlib.CategoryTheory.Adjunction.Mates`, `Mathlib.CategoryTheory.Adjunction.Unique`,
`Mathlib.CategoryTheory.Equivalence`, and `Mathlib.CategoryTheory.Limits.HasLimits`.
Their required APIs already arrive through the unchanged public source-library imports.

The proof does not construct a separate identity-on-arrows Hom adjunction or compare
two adjunction structures. It computes the unit of the inverse equivalence directly.
The direct proof dependency `det-def-sfb-ring-object-monoid` is removed: the monoid unit
and triangle calculation is already proved by the extension API's
`whiskerLeft_extendUnitHom_smul'`, rather than repeated here. This node remains needed
through statement and other proof dependencies; no module is withdrawn or globally pruned.
The other original dependency nodes remain used, including the Hom-equivalence
construction's computation rule. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan contains unnecessary work: its
identity-Hom adjunction and comparison of adjunctions are replaced by computation of
the unit of the exact adjunction already used to define the comparison. Its action/unit
calculation is already available upstream, and naturality follows directly from the
existing natural isomorphism and its inverse. The node was updated accordingly.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
