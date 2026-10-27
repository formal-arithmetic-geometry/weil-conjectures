## What changed

Proved `WeilConjectures.PrimitiveCounit.directEvaluation_eq` by comparing the actual
coefficient ring maps and applying the equality for composed module pushforwards.
The coefficient transports are identities on sections; the remaining square is the
specified constant-section ring map. A proved private generic composition lemma
keeps the module pushforward implementation out of the concrete categorical rewrite.
All existing theorem signatures and public imports are retained. `RoosRealization`
is the same three-field data through a generic `NormalizedComparison` record,
with the constructor and projection names retained as wrappers. This avoids kernel
checking its large concrete recursor. See
`coord/changes/R6-primitive-counit-roos-record.md` for the representation change
and all consumer modules. The identity bridge
`finiteTensorBridge` unfolds only the unrestricted reduction wrapper; the
scalar-extension functor and identity isomorphism are unchanged. An explicit result type on `inverseEvaluation` avoids inferring its large type
through the uniqueness witness; the chosen value is unchanged. Local transparency
settings keep large categorical definitions folded. The generic record supplies
the eliminators in place of the old concrete record.

## Proved and sorry left

Closed one of the three original holes:

- `WeilConjectures.PrimitiveCounit.directEvaluation_eq`.

Two original holes remain, both attached to
`lem-pur-completed-primitive-counit-comparison`:

- `WeilConjectures.PrimitiveCounit.inverseEvaluation_existsUnique`.
- `WeilConjectures.completedPrimitiveCounitComparison`.

No holes are added. No definition contains `sorry`.

## No longer needed

No existing import, node or module is removed. The delivered direct-image proof
needs only the original imports. The retained larger realization development and
its two proposed ordinary tower lemmas are kept in `scratchpad/`; they are not part
of this partial delivery and no new dependency is introduced for them.

## Where the brief, the DAG or earlier work was wrong

The previous disk-space failure is no longer observed. The retained larger proof
was not compiled and contained an unknown section-transport helper. During this
attempt the direct-image proof was repaired and checked separately within the
whole item. The inverse-image proof still exhausts its heartbeat budget when
converting the section carriers of the equality-transported evaluation functors.
The larger realization proof is retained for later work, without claiming it as
proved or delivering unvalidated lower statements. Local transparency settings keep
the chosen adjoint and the Roos-limit functor folded during generated record checks;
the explicit resolution formula and finite inverse-image comparison retain their
original unfolding context.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
