## What changed

Proved `WeilConjectures.compactSupportRestriction_identity` in
`Sheaf.Paper.CompactSupportRestrictionIdentity`, with its signature unchanged.
Private proved helpers identify the derived scalar identity on localized complexes
and establish the identity law for the specified direct-image comparison from
`compactSupportScalarDirectNormalization` and `ExactDerivedSquare.normalized_naturality`.
The final proof pastes this with the existing `sfOpenRestriction_derived_id`.
A private identity-isomorphism equation keeps equality transport from unfolding large
scalar functors during kernel checking; local derived-functor irreducibility and
the standard derived-category instance keep the proof presentations consistent.
Proof imports expose no additional interface. The existing node now records this argument.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.compactSupportRestriction_identity`
(`lem-coef-compact-support-restriction-identity`).
No holes remain in the item; no holes or split-off statements were added.
The server compilation passed in 15.0 seconds with profiling enabled; the development
profiling options were then removed for the delivery checks.
All private helpers have complete proofs. The imported normalization and open-identity
lemmas are already proved; their pre-existing dependencies are unchanged.

## No longer needed

None: the original public presentation import and every original declared proof dependency
are retained. The direct K-injective calculation is supplied by the existing proved
unit-normalization theorem, rather than repeated. No modules or declarations are withdrawn.
No geometric boundedness, invertibility of a prime, or proper-base-change hypothesis is used.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The DAG's direct-image uniqueness step is
implemented by the existing all-complex unit normalization and its proved naturality
lemma. The node now names these precise additional dependencies. No definitions,
statements, source-library modules, or consumer interfaces changed.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
