# F66Adj: exact Kernel site

**Declaration:** `imageHomIso_naturality`, origin `f66ad18a9ed`.

## Measurements

The type-only probe is 3.10 s. Synchronous Before is 116.48 s / 12,639,544
KB; skipped is 4.30 s. After is 3.40 s. `probes/ApplicationOnly.lean` binds
`homIso_naturality_of_counit` with the old concrete parameters and then uses
`sorry`: 35.32 s on / 3.50 s skipped. Replacing the final coherence argument
with a typed `sorry` (`probes/NoHTau.lean`) leaves 35.02 s, so the helper application itself is the
first expensive component. The full Before adds the final handoff and takes
116.47 s.

## Exact component

The expensive expression is the application of
`homIso_naturality_of_counit` whose result contains
`(GT.map (c.hom.app K).op).app ...`; the declaration goal contains the same
map through `imagePullback` and `leftDerivedUpperStarComp`. The compact probe
shows that the result's `NatTrans.app` is instantiated through the abstract
`GT`, while the goal expands the concrete `ExternalRHom.globalHom` path.
This is the coefficient-variance/`NatTrans.app` handoff described by the fix.

Diagnostics on the application-only probe report 511,948 Kernel unfolds of
`Add.add`, 368,876 `Functor.obj`, and 257,828 `DFunLike.coe`.

## Classification

Primary mechanism: **E** (different concrete and abstract interface paths).
Contributing mechanisms: **A** and **C** because the comparison is under
dependent functor applications. Evidence: **confirmed** for the helper
application and **strongly supported** for E/A/C. The fixed helper exposes
the coefficient variance as `γ`, then substitutes it, making the `NatTrans.app`
argument syntactically match.
