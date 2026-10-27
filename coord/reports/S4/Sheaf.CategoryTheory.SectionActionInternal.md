## What changed

Proved all three holes of `Sheaf.CategoryTheory.SectionActionInternal`. The action is
constructed by `Functor.modObjObj` and `ModObj.ofIso` along the coefficient and module
counits. Its action equals the specified `sfbSectionActionLift`; the adjunction triangle
identity proves restriction and the existing tensor extensionality proves uniqueness
and the linearity iff. The unchanged-map functor is additive.

Constructed finite coordinate products explicitly, shrinking the full product group to
the coefficient universe. The presheaf product is a sheaf, its module action comes from
`Mod.limitModObj`, and internal limit reflection proves the product assertion for every
internal source. The empty case is terminal and zero; tensor uniqueness gives the regular
multiplication normalization. All existing signatures and definitions stay unchanged.
Only private proved helpers, a local instance registration, and private proof imports were added. The node proof now
records the monoidal transport route. No source-library files were changed.

## Proved and sorry left

Closed 3 of 3 original holes:
- `CategoryTheory.sfbSectionAction_hasSheafify`.
- `CategoryTheory.sfbSectionAction_isMonoidal`.
- `CategoryTheory.sfbSectionActionInternal`.

All belong to `lem-sfb-section-action-internal`. Zero holes remain in the module; zero
holes added and zero split off. The private constructions contain no postponed proofs.

## No longer needed

None. All existing public imports are retained for the interface; the existing private
module-limit import is used. All five declared proof dependencies remain used. The
transport route replaces the duplicated internal unit/associativity coherence calculation
with existing proved transport APIs; it removes no unit statement, module or node.
The new proof imports supply group shrinking, limits of sheaves, product-cone transport,
and sheafification on essentially small sites.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The existing source library already has `Functor.modObjObj`,
`ModObj.ofIso`, tensor uniqueness, and module limit creation, so the planned direct
coherence calculations were unnecessary. The coordinate construction explicitly handles
the independent finite-index universe, including the empty index type. No new nodes,
statement changes or forced adaptations were required. The preflight requested a change
record for the extra scope and variable commands; it is
`coord/changes/sfb-section-action-internal-proof-scopes.md`. The underlying-module helper
uses an explicitly local instance registration. The consumer search found zero downstream
modules and only the item itself using these declarations.

Validation: the completed proof compiled without errors or warnings in 14.1 seconds;
the delivery tool repeats compilation and performs the declaration axiom audit.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
