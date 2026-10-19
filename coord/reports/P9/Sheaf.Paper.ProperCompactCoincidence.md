## What changed

Proved `WeilConjectures.properCompactCoincidence` in
`Sheaf.Paper.ProperCompactCoincidence`, preserving its statement, universes,
quantification over both normalized coefficient actions, and all public imports.
All new helpers are private and fully proved in the same module. The two local
backward-elaboration transparency options support the published derived-functor
interfaces; they do not change imported files or exported declarations. No other
Lean module or existing definition was changed. Updated the owning node's proof,
proof dependencies and proof origin to describe the implemented argument.

The finite comparison uses that the open immersion of any compactification of a
proper morphism is clopen, so extension by zero equals direct image. The integral
comparison uses the identity compactification and the published normalized qcqs
realization. The identity coefficient map is checked at every finite projection;
identity open extension follows from uniqueness of adjoints. Compactification
independence for integral, rational and all supplied algebraically closed actions
is obtained by applying the published composition comparisons to identity followed
by the structure morphism. The ordinary tower values are compared using uniqueness
of their Roos vertices. Localization, finite-stage inclusion, point fibres and
cohomology functors then give all remaining clauses.

Used `lem-zl-field-shriek-composition-qcqs` as a tool for compactification independence,
and `def-weil-system-operation-exchange-realization` for its normalized compact
realization and ordinary Roos presentation. These published interfaces provide the
needed integral naturality and actual ordinary tower vertices; the old finite-origin
coherence statement alone does not. No unit statement or realized step is bypassed.

Validation: the complete proof compiled cleanly with lcompile.py in 57.4 seconds
before removing unused imports, and in 51.6 seconds after pruning. Earlier
identity-open helpers and finite/integral value helpers were also checked through lcompile.py. Explicit functor types and the
published completed direct-image additivity theorem avoid expensive unresolved
functor metavariables. The final packet restores the protected unit-route import
and records the two local elaboration options and proof-only import changes in
`coord/changes/P9-proper-compact-proof-context.md`. The delivery dry run checks it.

## Proved and sorry left

Closed 1 original hole: `WeilConjectures.properCompactCoincidence`
(node `prop-weil-proper-compact-coincidence`). Added 0 holes; split off 0 statements.
There are no `sorry`s left in the delivered Lean module. Existing imported theorems
remain the library's proof dependencies; no transitive axiom-freedom claim is made.

## No longer needed

Removed these eight direct proof imports:

- `WeilConjectures.Compactification.Refinement`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`
- `Sheaf.Paper.CommonStageCompactWeilCohomology`
- `Sheaf.Paper.SfCommonStageDirectImage`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`

The finite proof does not need `lem-sf-proetale-constructible-origin`: the
proper/clopen comparison works on the whole finite derived category. The import
`Sheaf.Paper.CompactificationCoherence` is retained because it realizes the protected
unit `sk-prop-sf-comp-coherence`; its general coherence theorem remains on the
unit route although no direct application is needed in this proper special case.
The integral proof uses the normalized completed realization and the ordinary Roos presentation, so it does not need
`lem-sf-compact-support-restriction-of-scalars` directly. The unused local proof
dependencies are removed from this node's proof dependencies; the unit-route module remains imported. The general
`def-weil-extension-by-zero` dependency is replaced by
`sk-def-sfb-finite-lower-shriek` and the intrinsic realization interface; the
extension-by-zero construction itself is still used. No globally unreachable-module claim
is made: other parents and the retained dependencies can still need them.

The removed direct imports of definitions remain available through retained public
interfaces. Compactification, extension by zero, rationalization and ordinary
cohomology definitions are still used; their owning nodes are not pruned. The
common-stage Weil cohomology and common-stage direct-image specializations are
unnecessary to this proof, which uses the recorded geometric ordinary values.

## Where the brief, the DAG or earlier work was wrong

The earlier missing server artifact `Compactification.RefinementCategory.olean`
is now available. No launcher script or shared source was changed to work around it.
The retained proof's algebraically closed inclusion call had obsolete explicit
arguments; its current signature takes the finite stage and implicit scheme.

The DAG's finite-origin coherence and termwise transition argument is a valid plan,
but the library now exposes shorter normalized realization and composition APIs.
The owning node records the actual route. All comparisons still concern the same
proper structure morphism, arbitrary specified compactification and original
coefficient categories. The empty scheme, zero input, identity structure morphism,
and every positive finite exponent are included; no additional hypothesis was used.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
