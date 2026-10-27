## What changed

Proved `CategoryTheory.exists_ringFamily_idealDescentData` in
`Sheaf.Paper.FunctorialRingComplexIdealDescent` from the existing locally equal model
comparison, restriction comparison, and covering-locus hom-ext declarations.

On every common span, choose the chain isomorphism specified by its formula on
sheafification-unit sections. Covering-locus uniqueness proves naturality under further
restriction and the cocycle. Evaluating at the terminal test object constructs the linear
transitions; the chain equation proves differential compatibility. For augmentation,
project the degree-zero restricted single complex to the unit module, verify its formula
on unit sections, and use that all other target degrees are zero. The five resulting
fields are assembled by a proved private constructor.

The public signature and all public imports are unchanged. Private proof interfaces use
the global scalar sheaf restricted to the slice, a direct restriction functor with a proved
natural isomorphism to the native functor, typed unit and transport maps, and cached logical
instances. Large native constructions stay closed where their proved APIs suffice.
No source-library module or other group's module is changed. The change record is
`coord/changes/U3-ideal-descent-private-interfaces.md`.

The node's proof and direct proof-dependency list are updated to match these declarations.
No node statement, unit route, or Lean attachment changes.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.exists_ringFamily_idealDescentData`
(node `lem-weil-pbc-functorial-ring-complex-ideal-descent`).

Holes added: zero. Holes left in the delivery: zero. No obligation was split off or renamed.
Imported declarations may still contain their existing holes; they are the intended
stage-3 dependencies. The complete selected source compiled cleanly through `lcompile.py` in 55.0 seconds;
delivery validation is pending.

## No longer needed

Removed the redundant private imports
`Sheaf.CategoryTheory.ModuleSheafificationLocalIso` and
`Sheaf.CategoryTheory.ModuleSheafificationRestriction`. The latter's hom-ext theorem is
still used and is available through the public imports of `RingFamilyRestriction`.
The former supplies no declaration directly used by this proof, so its direct dependency
edge and proof-step use are removed. It remains a dependency of the comparison tools;
no module is globally pruned or withdrawn.

All other declared dependencies are used. The specialized private
`ringFamilyComponentEquiv_trans` helper is replaced by the proved generic equality-transport
calculation `componentEquiv_trans`.

## Where the brief, the DAG or earlier work was wrong

The prescribed mathematical route works. The original private interfaces repeatedly
compare native identity scalar restriction with direct slice restriction, unfolding large
sheafification, single-complex and abelian-category constructions. Typed private interfaces
and their explicit compatibility proofs avoid those expensive conversions. The augmentation
argument needs compatibility with the specified restriction isomorphism; this is proved
using the generic single-complex restriction calculation rather than assumed.

The consumer check found no external user of any changed private declaration. The textual
`restrictedModel` hit in `Sheaf.Paper.CompletedStalkFrobeniusReduction` is that module's own
unrelated definition at line 269. No forced adaptation is needed. Empty index families,
empty generating lists and the zero ring use the same proof, with no new premise.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
