## What changed

Implemented proofs for the six existing theorem holes in
`Sheaf.Paper.ExceptionalProEtaleRealization`, preserving every existing signature,
definition, instance, import and docstring. Added private proof helpers for cancelling
scalar restrictions and for the compatibility of the constant-ring sheafification units.

The finite realization is proved to be an additive equivalence by its three factors.
The normalized ordinary comparison is constructed from the actual module-sheafification
unit: its fixed-scalar linearity follows from the explicit quotient coordinate map, and
its underlying abelian map is an isomorphism because the original presheaf is already
a sheaf. This also proves uniqueness on all specified unit sections. Fully faithful
precomposition with the recorded realization gives the inverse comparison. Ordinary
evaluation is definitionally equal. Fully faithful precomposition with derived
localization gives the normalized derived evaluation comparison and its uniqueness.

The final uniqueness step makes the cancelled equality explicit and uses
`Iso.cancel_iso_inv_right`. The required delivery dry run passed compilation and
preflight, with review class `AUTO` (dry-run commit `9b05dfa098`).

## Proved and sorry left

The source replaces the six original holes with proof terms, all attached to
`def-pur-adic-proetale-realization`:

- `WeilConjectures.integralExceptionalProRealization_properties`
- `WeilConjectures.integralExceptionalLevel_equivalence`
- `WeilConjectures.integralExceptionalFixedUnit_existsUnique`
- `WeilConjectures.integralExceptionalLevelFixed_existsUnique`
- `WeilConjectures.integralExceptionalCoordinatesEvaluation`
- `WeilConjectures.integralExceptionalProEvaluationModel_existsUnique`

All six original holes are closed; zero sorry remains in the item.
Zero holes are added, no result is split off, and no new module is introduced.
Existing dependencies retain their own separately tracked holes;
this is a proof of the assigned item from those existing declarations.

## No longer needed

None. All three existing public imports remain needed by the original definitions,
normalization statements or coefficient-sheafification instances. The node has no
listed proof dependencies to prune. No module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The owning node is a definition node with empty `proof` and `proof_deps`; the six
existing theorem docstrings provide the proof plans. This delivery implements those
plans without a route or statement change, so no node edit or change record is needed.

The retained earlier attempt had unverified proofs and compiler transport failures.
The resumed session checked the retained cancellation fix against the Mathlib API.
The compile server now responded, and compilation and preflight passed. No tool
was modified or bypassed.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
