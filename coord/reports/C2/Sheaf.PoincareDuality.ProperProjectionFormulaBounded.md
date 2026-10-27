## What changed

Reapplied the retained proof to the current restored source of
`Sheaf.PoincareDuality.ProperProjectionFormulaBounded` and proved `isIso_properProjection_bounded` with its original statement and hypotheses.
Extension by zero supplies the bounded constructible input. The existing coefficient
projection square transports invertibility through exact scalar equivalences. Explicit
isometric coefficient realizations and the integral constructibility comparison reduce
the four coefficient presentations to the stated integral and rational projection clauses.
All mathematical helpers in the item are private and proved. The current theorem signature and docstring are preserved. The compactification route
of unit `sk-thm-sf-verdier-exchange` is preserved.

Repaired `Sheaf.Paper.ModuleObjectProjectionMap` by packaging its existing category,
endpoints and canonical mate in `ProjectionMorphismData`. The map remains the morphism
of precisely that construction. This avoids repeatedly expanding its inferred category
interface during kernel checking; no arbitrary witness or new mathematical choice is used.
The new module `Sheaf.PoincareDuality.ModuleObjectProjectionMorphism` proves the
invertibility normalization `isIso_moduleObjectProjectionMap_iff` by reflexivity.
This is an API for the repaired definition, not a split of the projection argument.
The two original public imports of each existing module are retained. No source-library
file, existing consumer source, target statement or public hypothesis is changed.

Change records:
`coord/changes/C2-proper-projection-bounded-proof-context.md` and
`coord/changes/C2-module-object-projection-record.md`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_properProjection_bounded`.
Also proved the new normalization theorem
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_moduleObjectProjectionMap_iff`.
Added zero holes; split off zero unfinished statements. There are zero `sorry`
occurrences in all three delivered Lean modules. Existing stated dependencies are
imported rather than reproved here.

The repaired three-module set compiled without errors or warnings on the current
published build: map 3.1 s, normalization 11.5 s, assigned item 50.8 s.
Earlier retained consumer checks passed for CoefficientProjectionSquare,
IntegralProperBaseChange, IntegralQuotientProjectionMap and ProperBaseChangeRational.
A fresh eight-consumer check was attempted against the current sources. It stopped
before checking a consumer because an unpublished dependency, OpenImmersionLocalizing,
requires the missing published ProjectionFormula artifact. Checking the unchanged
restored parent separately exceeded its file limit. No consumer interface error was
reported, and none of these unchanged consumer files is included in this delivery.
The current consumer inventory and definitionally unchanged interfaces are recorded
in the expanded change-record table. Delivery preflight is run by the delivery tool.

## No longer needed

Removed the proof import `Sheaf.Paper.ModuleRingedToposDerivedComparison` and the direct
proof dependency `lem-pd-module-ringed-topos-derived-comparison`. Both existing proper
projection clauses already use the canonical `moduleObjectProjectionMap`, so this argument
does not need a ringed-topos change of category. This does not withdraw that module or
any declaration; its other consumers retain their dependencies.

Also removed the direct proof import `Sheaf.Paper.IntegralResidueDerivedMonoidal`;
its definitions are already supplied through the proof dependencies. This removes no
module from the transitive closure. No original declared dependency besides the direct
ringed-topos comparison is pruned.

The seven original local `projection*` cache registrations are unnecessary. The proof
uses canonical instances and local reducibility boundaries instead. No module is withdrawn,
no source-library declaration is removed, and no maintainer tool approvals are changed.

## Where the brief, the DAG or earlier work was wrong

The original route inserted a ringed-topos equivalence despite the stated proper projection
inputs already concerning internal module objects and the same canonical mate. The glue
needed here is coefficient realization, transport of the actual map, and the comparison
of integral constructibility predicates. The revised node records that argument.

The earlier item was absent from `lean/` because it was quarantined, not withdrawn.
It has since been restored in the current shared source. The return at head `2ee398868`
reported that source creation after base `7da6b4235`; this repair takes that current file,
retains its statement and docstring, and applies the completed proof to it. Its Lean
attachment, parent dependency and unit realization are retained. Its original local cache
names were unavailable through the recorded imports. The restored proof uses the existing
canonical instances. The original inferred projection-map interface caused excessive
unfolding; the record repair stores the same construction and exposes a compact interface.

## New nodes

`lem-sfb-module-object-projection-morphism`: unconditional invertibility normalization
between the canonical module-object mate and the specified adjunction projection morphism.
The definitions, including their categories and endpoints, coincide, so the proof is
reflexivity. It has no `sorry` and is strictly a definition API, independent of properness,
boundedness and coefficient finiteness. The existing definition node
`def-sfb-module-object-projection-map` lists the new record and data constructor alongside
the preserved map declaration. Both change records are listed under What changed. The new node records LeanSearch, LeanFinder, Loogle and source searches.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
