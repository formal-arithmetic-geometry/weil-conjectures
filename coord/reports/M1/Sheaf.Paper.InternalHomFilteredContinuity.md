## What changed

Proved `WeilConjectures.SfbHomFilteredColimit.internalHom_filtered_continuity`
in `Sheaf.Paper.InternalHomFilteredContinuity`, with its signature and existing
public import unchanged. Added private, fully proved helpers for finite-free and
colimit tensor exactness, the degree-zero total-tensor comparison, transport of
continuity along a diagram quasi-isomorphism, and derived Hom invariance.

Proof imports supply the proved independent-universe tensor API, universe-general
Hom quasi-isomorphism theorem, single-complex tensor comparison, bifunctor
colimits and exact-colimit preservation of quasi-isomorphisms. Updated the node's
proof and proof origin to describe the actual Lean argument. No definition,
public signature, source-library module or consumer changed. The private helper
scopes and added namespace openings are recorded in
`coord/changes/M1-internal-hom-filtered-proof-scopes.md`; the single downstream
consumer is held by R3 and requires no adaptation.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.SfbHomFilteredColimit.internalHom_filtered_continuity`
(node `lem-sfb-internal-hom-filtered-continuity`). All three conjuncts are proved.
Zero holes remain in the item; zero holes added and zero statements split off.
All added helpers are private and completely proved.

The final single-file `lcompile.py` check passed without warnings at the default
heartbeat and 60-second limits. Delivery runs the declaration/axiom preflight.

## No longer needed

No original import, declared dependency, node or module is withdrawn. All six
existing proof dependencies remain used. No new dependency on the unfinished
`InternalHomFiniteFreeStage` calculation is needed: tensor exactness is proved
directly from the given finite powers of the unit. The supplied termwise lower
bound makes a good lower truncation unnecessary. K-flatness of P is unnecessary
in this subargument, but the existing hypothesis and theorem signature are kept.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan is valid. Its docstring mentions a good lower truncation;
the formal statement already gives the required termwise lower bound on L, so
the proof uses it directly. No lower bound on the K-injective replacement or on
Hom(P,I(L)) is assumed. Finite rank zero is covered by the finite-product proof.

The first compiler attempts reported a missing published artifact for the newly
landed data module. It became available during proof development; no landed
dependency was copied, changed or redelivered to work around that publication lag.

The first delivery preflight requested this change record because its conservative
interface scanner flags new universe/section/open commands. That packet was not
pushed. The record now describes their local proof scope and the unchanged public
signature and consumer.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
