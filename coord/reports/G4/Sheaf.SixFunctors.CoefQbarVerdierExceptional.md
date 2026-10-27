## What changed

Replaced the proof of `WeilConjectures.CoefQbarVerdier.exceptional_descent` by an
explicit construction from the finite coefficient system. The original signature
and public import are unchanged. All additional proof imports are private.

The construction reindexes the existing rational cocycle by the coefficient-inclusion
composition law, transports its scalar comparisons to the prescribed stage systems,
and builds both stage-system morphisms. The finite mate equations supply compatible
units and counits. `StageSystem.Morphism.adjunction` gives their actual descended
adjunction. The proof verifies every object, identity-component, unit, counit and
scalar equation of `ExceptionalProperties`.

The new module `Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula` isolates the
remaining finite exceptional comparison and scalar square. It asserts local natural
isomorphisms whose source is one finite coefficient category, for a fixed existing
system and the specified dualities; it asserts neither a descended exceptional
functor nor an adjunction. The item proves the gluing: cancel the invertible scalar
comparison in the two scalar squares, factor each pair-category morphism into two
transitions and an included finite morphism, and prove naturality. Its components
then give the required formula and its exact normalization.

The two proved helper modules `Sheaf.SixFunctors.CoefQbarRationalScalarCocycles`
and `Sheaf.SixFunctors.CoefQbarFiniteScalarCocycles` isolate the raw cocycle
reindexing and its transport to prescribed stages. They add no holes. Packaging
component equations before specialization and keeping cached category definitions
irreducible removed repeated kernel expansion. The combined item still took
78--83 seconds, so these self-contained calculations were moved to separate
modules; no compiler limit or transparency check was relaxed.

Validation: all four sandbox modules compile together in import order without
warnings: finite formula 42.2 s, rational cocycles 24.8 s, finite cocycles 34.9 s,
and the item 30.3 s. The original theorem signature is unchanged byte for byte.
No dependency cycle passes through any delivered node. Temporary probe files and
profiling options were removed.

No existing module other than the item was changed. The generic native
`StageSystem.Morphism.functor` and representation theorem are used as proved
categorical tools (the existing attachment `lem-pur-associative-stage-family-descent`),
not as a replacement for a geometric step of the unit.

## Proved and sorry left

The one original hole, `WeilConjectures.CoefQbarVerdier.exceptional_descent`
(node `lem-coef-qbar-verdier-exceptional-descent`), is replaced by a complete Lean
proof from the stated dependencies and one strictly smaller finite-stage theorem.
There are zero holes left in the item module. The two auxiliary theorems
`WeilConjectures.CoefQbarVerdier.rational_scalar_cocycles` and
`WeilConjectures.CoefQbarVerdier.finite_scalar_cocycles` are fully proved.

One hole is added: `WeilConjectures.CoefQbarVerdier.finite_exceptional_formula`
(node `lem-coef-qbar-finite-exceptional-formula`) in the new module. Its proof is
exactly `by sorry`; its docstring and node give the source and argument.

This is a decomposition: one upper hole closed, one finite hole added, net zero.
It is not reported as an unconditional proof of the original theorem. The entire
exceptional adjunction construction, all eight property clauses, and the global
comparison gluing are proved. There is no hole in any definition or private helper.

## No longer needed

No original import is removed, and no whole-library module is claimed pruned.
`Sheaf.SixFunctors.CoefQbarVerdierData` remains the public statement dependency and
`Sheaf.CategoryTheory.StageSystemAdjunction` remains a private proof dependency.

The parent no longer directly uses `lem-coef-rational-operations`: it obtains the
system from `lem-sf-constructible-exceptional-adjunction-coefficients`. It uses the
native proved StageSystem functor, rather than the separate
`lem-sbc-coherent-pair-functor-descent` existence interface.

`lem-weil-scalar-extension-composition` is no longer a direct dependency of the
parent; the explicit scalar-cocycle transport is recorded in the two proved helper
nodes instead.

`lem-pur-integral-operations-scalar-extension`,
`def-weil-derived-pullback-tensor-hom`, and
`def-weil-exceptional-inverse-image` are no longer direct proof dependencies of the
parent. The new finite lemma still needs the first two, and its specified existing
system retains the exceptional-operation definitions. These are dependency
refinements, not claims that the corresponding modules can be withdrawn.

## Where the brief, the DAG or earlier work was wrong

The shared rework snapshot mentioned quarantine and an import failure. The current
server queue instead lists this as a one-hole proof item, its rework row is absent,
and the original module compiles. No archived declaration or dependency was removed.

The earlier plan omitted the equality transports between the chosen StageSystem
transitions and the literal rational scalar functors. The proof supplies those
transports explicitly, including transport of both mate equations and reindexing
of the scalar associator. It does not change the target or any shared definition.

The finite comparison theorem is stronger than a separate choice of comparisons
for each scalar pair: it requires one normalized family. The remaining proof must
use the evaluation-defined adjunction transpose to obtain that family; arbitrary
pairwise choices from an existence theorem are insufficient.

A traversal of the shared snapshot also found an unrelated existing cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`, and an absent referenced node
`def-weil-pbc-localization-universal-property`. These records were not changed;
this observation concerns the snapshot, not a new edge in this delivery.

## New nodes

`lem-coef-qbar-finite-exceptional-formula` records precisely the finite-source
exceptional comparisons and their scalar square from retained step 9. The existing
rational exceptional-identification declaration was read first; it supplies pairwise
comparisons, but not the globally consistent finite family or its transport through
the specified inclusion comparisons. The new node leaves only that finite work;
the parent proves the adjunction and gluing. Repeated fields and empty/zero
categories use the same identities; no nonzero object or nonidentity extension is
assumed. Mathlib searches and the blueprint search found no exact duplicate.
There are no change records because no existing public interface changes.

`lem-coef-qbar-rational-scalar-cocycles` records the proved generic reindexing of
the existing system's two scalar cocycles. Its public component predicate prevents
expanding specialized coefficient categories while checking the proof.

`lem-coef-qbar-finite-scalar-cocycles` records the proved specialization to the
small coefficient models and equality transport to the chosen stage associators.
These are the existing scalar-coherence steps, with no new proof obligations.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula": "daa915578bc7cb25307508b0860086d3c8fe884f", "Sheaf.SixFunctors.CoefQbarFiniteScalarCocycles": "8a4f0298b38ff37929ad02850303591ef498f846", "Sheaf.SixFunctors.CoefQbarRationalScalarCocycles": "d36f4764065905715312b2ff87574709dd896a55", "Sheaf.SixFunctors.CoefQbarVerdierExceptional": "807b526093da108aa223c17704358fc4c6826b8c"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdier": {"hash": "36026758723ddb846cce37cc323a7b8f7ea0a6f9", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierDualizing": {"hash": "cd16b4af6d8c1a630d26dd9de7b846da0c3f90f8", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T03:29:30+0800", "transitive": 0, "version": 1}
```

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
